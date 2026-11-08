// Exact numeric DFS for enumerate_form. No group theory or semantic filters here.
// Called via ctypes.PyDLL: GIL held, PyErr_CheckSignals preserves Python timeouts.
#include <Python.h>
#include <algorithm>
#include <cstdint>
#include <cstring>
#include <stdexcept>
#include <unordered_map>
#include <vector>

using U = uint64_t;
using Bits = std::vector<U>;
struct Interrupted {};
static void signals() { if (PyErr_CheckSignals() < 0) throw Interrupted{}; }
static bool any(const Bits &a) { for (U x : a) if (x) return true; return false; }
static Bits ones(size_t rows) {
    Bits r(std::max<size_t>(1, (rows+63)/64), ~U(0));
    if (!rows) r[0]=0;
    else if (rows%64) r.back()=(U(1)<<(rows%64))-1;
    return r;
}
static bool intersects(const U *a, const Bits &r) {
    for (size_t w=0; w<r.size(); ++w) if (a[w]&r[w]) return true;
    return false;
}
struct Matrix {
    size_t cols, rows, words;
    const U *data;
    Bits owned;
    Matrix(const U *d,size_t c,size_t r):cols(c),rows(r),words(std::max<size_t>(1,(r+63)/64)),data(d) {}
    const U *col(int c) const { return data+size_t(c)*words; }
    Matrix(const Matrix &p,const Bits &r):cols(p.cols),rows(0),words(0),data(nullptr) {
        std::vector<size_t> positions;
        for (size_t w=0;w<r.size();++w) {
            U x=r[w];
            while(x) { positions.push_back(w*64+__builtin_ctzll(x)); x&=x-1; }
        }
        rows=positions.size(); words=std::max<size_t>(1,(rows+63)/64);
        owned.assign(cols*words,0);
        for(size_t c=0;c<cols;++c) {
            if (!(c%64)) signals();
            const U *src=p.col(c);
            for(size_t j=0;j<rows;++j) {
                size_t i=positions[j];
                if ((src[i/64]>>(i%64))&1) owned[c*words+j/64]|=U(1)<<(j%64);
            }
        }
        data=owned.data();
    }
};
// Output column in its final item size (1/2/4/8 bytes, little-endian), in
// fixed chunks: no vector-doubling slack or reallocation copy, and Python can
// free each chunk right after copying it.
struct Column {
    static constexpr size_t CHUNK=size_t(1)<<20;
    size_t item=8, n=0;
    std::vector<std::vector<unsigned char>> chunks;
    void push(U v) {
        if(item<8 && (v>>(8*item))) throw std::overflow_error("native packed output overflow");
        if(chunks.empty() || chunks.back().size()==CHUNK*item) {
            chunks.emplace_back(); chunks.back().reserve(CHUNK*item);
        }
        auto &c=chunks.back(); size_t at=c.size(); c.resize(at+item);
        std::memcpy(c.data()+at,&v,item); ++n;
    }
};
struct Result {
    U count=0;
    std::vector<Column> keys, supports;
    std::vector<Bits> empty;
    Result(int k,int ksize=8,int vsize=8):keys(k+1),supports(k+1),empty(k+1) {
        for(auto &c:keys) c.item=size_t(ksize);
        for(auto &c:supports) c.item=size_t(vsize);
    }
};
struct Engine {
    int n,k,width,atoms;
    bool need,prune;
    U full,ticks=0;
    const U *coverage;
    const uint8_t *goals,*skip,*have0,*reqcols,*relations;
    const int32_t *reqoffs,*reqvalues,*clashoffs,*clashvalues,*provideroffs,*providervalues;
    int props_from;
    Matrix pall;
    Result out;
    std::unordered_map<U,Bits> lower,direct;
    Engine(int ksize,int vsize,int n_,int k_,int width_,U full_,bool prune_,int props_,const U *all,size_t nr,
           const U *cov,const uint8_t *g,const uint8_t *s,const uint8_t *h,
           const uint8_t *rc,const uint8_t *rel,const int32_t *ro,const int32_t *rv,
           const int32_t *co,const int32_t *cv,const int32_t *po,const int32_t *pv)
      :n(n_),k(k_),width(width_),atoms(n_/2),need(full_!=0),prune(prune_),full(full_),
       coverage(cov),goals(g),skip(s),have0(h),reqcols(rc),relations(rel),
       reqoffs(ro),reqvalues(rv),clashoffs(co),clashvalues(cv),provideroffs(po),providervalues(pv),
       props_from(props_),pall(all,n_,nr),out(k_,ksize,vsize) {}
    U code(const std::vector<int> &p) const {
        U c=1; for(int j:p) c=(c<<width)|U(j); return c;
    }
    bool has(const std::vector<int> &p,int j) const {
        if(have0[j] || std::find(p.begin(),p.end(),j)!=p.end()) return true;
        for(int selected:p) for(int i=provideroffs[selected];i<provideroffs[selected+1];++i)
            if(providervalues[i]==j) return true;
        return false;
    }
    bool req(const std::vector<int> &p,int atom) const {
        for(int i=reqoffs[atom];i<reqoffs[atom+1];++i) if(!has(p,reqvalues[i])) return false;
        return true;
    }
    bool used(const std::vector<int> &p,int atom) const {
        for(int j:p) if(j/2==atom) return true; return false;
    }
    bool conflicts(const std::vector<int> &p,int atom) const {
        for(int j:p) for(int i=clashoffs[atom];i<clashoffs[atom+1];++i)
            if(clashvalues[i]==j/2) return true;
        return false;
    }
    const Bits &direct_mask(const std::vector<int> &p) {
        U c=code(p);
        auto it=direct.find(c); if(it!=direct.end()) return it->second;
        Bits m((n+63)/64,0);
        bool valid=true; for(int j:p) if(!req(p,j/2)) valid=false;
        if(valid) {
            Bits r=ones(pall.rows);
            for(int j:p) for(size_t w=0;w<r.size();++w) r[w]&=pall.col(j)[w];
            if(any(r)) for(int g=0;g<n;++g) {
                if(!(g%64)) signals();
                if(req(p,g/2) && !intersects(pall.col(g^1),r)) m[g/64]|=U(1)<<(g%64);
            }
        }
        return direct.emplace(c,std::move(m)).first->second;
    }
    bool subtract(Bits &m,const std::vector<int> &q) {
        const Bits *d=nullptr;
        if(need) d=&direct_mask(q);
        else { auto it=lower.find(code(q)); if(it!=lower.end()) d=&it->second; }
        if(d) for(size_t w=0;w<m.size();++w) m[w]&=~(*d)[w];
        return any(m);
    }
    bool subsets(Bits &m,const std::vector<int> &p,int size,int start,std::vector<int> &q) {
        if(int(q.size())==size) return subtract(m,q);
        for(int i=start;i<=int(p.size())-(size-int(q.size()));++i) {
            q.push_back(p[i]); bool remaining=subsets(m,p,size,i+1,q); q.pop_back();
            if(!remaining) return false;
        }
        return true;
    }
    void leaf(const std::vector<int> &p,const Bits &r,int depth,U pm,const Matrix &P) {
        for(int j:p) if(!req(p,j/2)) return;
        if(!any(r)) { out.empty[depth].push_back(code(p)); return; }
        U miss=full&~pm; bool gc=false;
        Bits m((n+63)/64,0);
        for(int g=0;g<n;++g) {
            if(!goals[g] || (need && (coverage[g]&miss)!=miss)) continue;
            gc=true;
            if(used(p,g/2) || !req(p,g/2) || conflicts(p,g/2)) continue;
            if(!intersects(P.col(g^1),r)) { m[g/64]|=U(1)<<(g%64); ++out.count; }
        }
        if(!gc) return;
        U cp=code(p);
        if(depth<k) lower[cp]=m;
        if(!any(m)) return;
        std::vector<int> q;
        for(int size=1;size<int(p.size());++size) if(!subsets(m,p,size,0,q)) return;
        for(int g=0;g<n;++g) if((m[g/64]>>(g%64))&1) {
            U support=0; for(size_t w=0;w<r.size();++w) support+=__builtin_popcountll(P.col(g)[w]&r[w]);
            out.keys[depth].push((cp<<width)|U(g)); out.supports[depth].push(support);
        }
    }
    void children(std::vector<int> &p,const Bits &r,int start,int depth,U pm,const Matrix &P) {
        for(int j=start;j<n;++j) {
            if(skip[j] || used(p,j/2)) continue;
            if(prune && !p.empty() && !reqcols[j]) {
                bool extra=false;
                for(size_t w=0;w<r.size();++w) if(r[w]&~P.col(j)[w]) { extra=true; break; }
                if(!extra) continue;
            }
            if(conflicts(p,j/2)) continue;
            if(props_from && int(p.size())+1>=props_from && relations[j/2]) continue;
            Bits next(r.size()); for(size_t w=0;w<r.size();++w) next[w]=P.col(j)[w]&r[w];
            p.push_back(j); go(p,next,j+1,depth,pm|coverage[j],P); p.pop_back();
        }
    }
    void go(std::vector<int> &p,const Bits &r,int start,int depth,U pm,const Matrix &P) {
        if(!(++ticks%2048)) signals();
        if(need && __builtin_popcountll(full&~pm)>2*(depth-int(p.size())+1)) return;
        if(int(p.size())==depth) { leaf(p,r,depth,pm,P); return; }
        if(!p.empty()) {
            if(!any(r)) return;
            U on=0; for(U x:r) on+=__builtin_popcountll(x);
            if(on*4<P.rows && P.words>4) {
                Matrix packed(P,r); Bits all=ones(packed.rows);
                children(p,all,start,depth,pm,packed); return;
            }
        }
        children(p,r,start,depth,pm,P);
    }
};

// In-place minimal for PackedConditions buffers. Phase 1 only reads and marks
// (interruptible); phase 2 compacts stably and cannot be interrupted, so the
// arrays are never left half-compacted. Same test as algen_minimal: a key of
// length d>1 is dropped iff some key of length d-1 (one premise omitted, same
// goal) is present in the ORIGINAL input. Returns 0, or -1 with a Python error.
template<class K>
static int minimal_inplace_t(int k,int width,size_t vsize,void *const *keys_v,void *const *vals_v,size_t *sizes) {
    const U mask=(U(1)<<width)-1;
    std::vector<std::vector<U>> drop(k+1);
    for(int depth=2;depth<=k;++depth) {
        size_t n=sizes[depth]; if(!n) continue;
        const K *keys=static_cast<const K*>(keys_v[depth]);
        drop[depth].assign((n+63)/64,0);
        std::vector<int> prem(depth);
        for(size_t i=0;i<n;++i) {
            if(!(i%2048)) signals();
            U c=keys[i], goal=c&mask, rest=c>>width;
            for(int p=depth-1;p>=0;--p) { prem[p]=int(rest&mask); rest>>=width; }
            for(int omit:prem) {
                // repeated premises: omitting one value removes all its copies
                U q=1; int length=0;
                for(int x:prem) if(x!=omit) { q=(q<<width)|U(x); ++length; }
                q=(q<<width)|goal;
                const K *lower=static_cast<const K*>(keys_v[length]);
                if(sizes[length] && std::binary_search(lower,lower+sizes[length],K(q))) {
                    drop[depth][i/64]|=U(1)<<(i%64); break;
                }
            }
        }
    }
    for(int depth=2;depth<=k;++depth) {
        if(drop[depth].empty()) continue;
        K *keys=static_cast<K*>(keys_v[depth]);
        unsigned char *vals=static_cast<unsigned char*>(vals_v[depth]);
        size_t n=sizes[depth], w=0;
        for(size_t i=0;i<n;++i) {
            if((drop[depth][i/64]>>(i%64))&1) continue;
            if(w!=i) { keys[w]=keys[i]; std::memmove(vals+w*vsize,vals+i*vsize,vsize); }
            ++w;
        }
        sizes[depth]=w;
    }
    return 0;
}
extern "C" {
void *algen_enum(int n,int k,int width,U full,int prune,int props_from,
                const U *all,size_t nr,const U *initial,size_t selected,
                const U *coverage,const uint8_t *goals,const uint8_t *skip,const uint8_t *have0,
                const uint8_t *reqcols,const uint8_t *relations,
                const int32_t *reqoffs,const int32_t *reqvalues,
                const int32_t *clashoffs,const int32_t *clashvalues,
                const int32_t *provideroffs,const int32_t *providervalues,int ksize,int vsize) {
    try {
        if((ksize!=1&&ksize!=2&&ksize!=4&&ksize!=8)||(vsize!=1&&vsize!=2&&vsize!=4&&vsize!=8))
            throw std::invalid_argument("native enumeration: item size");
        Engine e(ksize,vsize,n,k,width,full,prune,props_from,all,nr,coverage,goals,skip,have0,reqcols,relations,reqoffs,reqvalues,clashoffs,clashvalues,provideroffs,providervalues);
        Matrix P(initial,n,selected); Bits r=ones(selected); std::vector<int> p;
        for(int depth=1;depth<=k;++depth) e.go(p,r,0,depth,0,P);
        signals(); return new Result(std::move(e.out));
    } catch(const Interrupted &) { return nullptr; }
      catch(const std::bad_alloc &) { PyErr_NoMemory(); return nullptr; }
      catch(const std::overflow_error &e) { PyErr_SetString(PyExc_OverflowError,e.what()); return nullptr; }
      catch(const std::exception &e) { PyErr_SetString(PyExc_RuntimeError,e.what()); return nullptr; }
      catch(...) { PyErr_SetString(PyExc_RuntimeError,"native enumeration failed"); return nullptr; }
}
U algen_count(void *p) { return static_cast<Result*>(p)->count; }
size_t algen_size(void *p,int depth,int kind) {
    auto &r=*static_cast<Result*>(p);
    return kind==2 ? r.empty[depth].size() : (kind==0?r.keys:r.supports)[depth].n;
}
const U *algen_data(void *p,int depth,int kind) {  // kind 2 (empty premises) only
    auto &r=*static_cast<Result*>(p); return kind==2 ? r.empty[depth].data() : nullptr;
}
size_t algen_itemsize(void *p,int depth,int kind) {
    auto &r=*static_cast<Result*>(p); return (kind==0?r.keys:r.supports)[depth].item;
}
size_t algen_nchunks(void *p,int depth,int kind) {
    auto &r=*static_cast<Result*>(p); return (kind==0?r.keys:r.supports)[depth].chunks.size();
}
const unsigned char *algen_chunk(void *p,int depth,int kind,size_t i,size_t *items) {
    auto &c=(kind==0?static_cast<Result*>(p)->keys:static_cast<Result*>(p)->supports)[depth];
    *items=c.chunks[i].size()/c.item; return c.chunks[i].data();
}
void algen_release_chunk(void *p,int depth,int kind,size_t i) {
    auto &c=(kind==0?static_cast<Result*>(p)->keys:static_cast<Result*>(p)->supports)[depth];
    std::vector<unsigned char>().swap(c.chunks[i]);
}
void algen_free(void *p) { delete static_cast<Result*>(p); }
int algen_minimal_inplace(int k,int width,int ksize,int vsize,void *const *keys,void *const *vals,size_t *sizes) {
    try {
        switch(ksize) {
            case 1: return minimal_inplace_t<uint8_t>(k,width,size_t(vsize),keys,vals,sizes);
            case 2: return minimal_inplace_t<uint16_t>(k,width,size_t(vsize),keys,vals,sizes);
            case 4: return minimal_inplace_t<uint32_t>(k,width,size_t(vsize),keys,vals,sizes);
            case 8: return minimal_inplace_t<uint64_t>(k,width,size_t(vsize),keys,vals,sizes);
        }
        PyErr_SetString(PyExc_ValueError,"native minimal: key size"); return -1;
    } catch(const Interrupted &) { return -1; }
      catch(const std::bad_alloc &) { PyErr_NoMemory(); return -1; }
      catch(const std::exception &e) { PyErr_SetString(PyExc_RuntimeError,e.what()); return -1; }
      catch(...) { PyErr_SetString(PyExc_RuntimeError,"native minimal failed"); return -1; }
}
void *algen_minimal(int k,int width,const U *const *keys,const U *const *supports,const size_t *sizes) {
    try {
        Result out(k); U mask=(U(1)<<width)-1;
        for(int depth=0;depth<=k;++depth) {
            for(size_t i=0;i<sizes[depth];++i) {
                if(!(i%2048)) signals();
                U c=keys[depth][i], goal=c&mask; bool keep=true;
                if(depth>1) {
                    U rest=c>>width; std::vector<int> prem(depth);
                    for(int p=depth-1;p>=0;--p) { prem[p]=rest&mask; rest>>=width; }
                    for(int omit:prem) {
                        U q=1; int length=0;
                        for(int x:prem) if(x!=omit) { q=(q<<width)|U(x); ++length; }
                        q=(q<<width)|goal;
                        if(sizes[length] && std::binary_search(keys[length],keys[length]+sizes[length],q)) {
                            keep=false; break;
                        }
                    }
                }
                if(keep) { out.keys[depth].push(c); out.supports[depth].push(supports[depth][i]); }
            }
        }
        signals(); return new Result(std::move(out));
    } catch(const Interrupted &) { return nullptr; }
      catch(const std::bad_alloc &) { PyErr_NoMemory(); return nullptr; }
      catch(const std::exception &e) { PyErr_SetString(PyExc_RuntimeError,e.what()); return nullptr; }
      catch(...) { PyErr_SetString(PyExc_RuntimeError,"native minimal failed"); return nullptr; }
}
}
