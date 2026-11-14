// Exact Library-value classification of bounded packed condition blocks.
// Separate from theorem verdicts and numeric enumeration. No input is mutated.
#include <Python.h>
#include <algorithm>
#include <cstdint>
#include <cstring>
#include <limits>
#include <stdexcept>
#include <unordered_map>
#include <vector>

using U = uint64_t;
struct Interrupted {};
struct Budget {};
static void signals() { if (PyErr_CheckSignals()<0) throw Interrupted{}; }
struct Values {
    std::vector<uint8_t> kinds;
    std::vector<U> single,multi,refuting,offsets,rows,sparse_keys,sparse_counts;
    std::vector<int32_t> columns;
};
static U key_at(const void *p,size_t i,int item) {
    U value=0;
    std::memcpy(&value,static_cast<const unsigned char*>(p)+i*size_t(item),size_t(item));
    return value;
}
static Values *classify(int n,size_t nr,const U *P,int width,int depth,int item,
                        const void *keys,size_t count,const int32_t *fixed,size_t nfixed,
                        const int32_t *offsets,const int32_t *values,size_t limit) {
    if(n<=0 || n%2 || width<=0 || width>=32 || depth<0 || depth>3 ||
       width*(depth+1)+1>64 || (item!=1&&item!=2&&item!=4&&item!=8) ||
       U(n)>U(1)<<width || nr>std::numeric_limits<U>::max()/U(n))
        throw std::invalid_argument("invalid values dimensions");
    Values *out=new Values;
    try {
        out->kinds.resize(count); out->single.resize(count); out->multi.resize(count);
        out->refuting.resize(count); out->offsets.reserve(count+1); out->offsets.push_back(0);
        size_t words=std::max<size_t>(1,(nr+63)/64);
        U mask=(U(1)<<width)-1;
        std::vector<int> cols;
        auto add=[&](int raw) {
            if(raw<0 || raw>=n || offsets[raw]==offsets[raw+1])
                throw std::invalid_argument("unsupported literal expansion");
            for(int32_t j=offsets[raw];j<offsets[raw+1];++j) {
                int c=values[j];
                if(c<0 || c>=n) throw std::invalid_argument("invalid primitive column");
                if(std::find(cols.begin(),cols.end(),c^1)!=cols.end())
                    throw std::invalid_argument("contradictory forbidden literals");
                if(std::find(cols.begin(),cols.end(),c)==cols.end()) cols.push_back(c);
            }
        };
        for(size_t i=0;i<count;++i) {
            if(!(i%64)) signals();
            cols.clear();
            for(size_t j=0;j<nfixed;++j) add(fixed[j]);
            U code=key_at(keys,i,item); int goal=int(code&mask); code>>=width;
            int prem[3];
            for(int j=depth-1;j>=0;--j) { prem[j]=int(code&mask); code>>=width; }
            if(code!=1 || goal>=n) throw std::invalid_argument("invalid packed condition key");
            for(int j=0;j<depth;++j) add(prem[j]);
            add(goal^1);
            U singles=0,multis=0,refuters=0;
            for(size_t w=0;w<words;++w) {
                if(!(w%1024)) signals();
                U valid=~U(0);
                if(!nr) valid=0;
                else if(w+1==words && nr%64) valid=(U(1)<<(nr%64))-1;
                U ok=valid,one=0,two=0;
                for(int c:cols) {
                    U yes=P[size_t(c)*words+w],no=P[size_t(c^1)*words+w];
                    ok&=~no;
                    U unknown=~(yes|no)&valid;
                    two|=one&unknown; one|=unknown;
                }
                U single=ok&one&~two;
                singles+=__builtin_popcountll(single);
                multis+=__builtin_popcountll(ok&two);
                refuters+=__builtin_popcountll(ok&~one);
                while(single) {
                    unsigned b=__builtin_ctzll(single); single&=single-1;
                    U bit=U(1)<<b;
                    int missing=-1;
                    for(int c:cols) if(!((P[size_t(c)*words+w]|P[size_t(c^1)*words+w])&bit)) {
                        missing=c; break;
                    }
                    if(missing<0) throw std::logic_error("missing single-unknown column");
                    if(out->rows.size()>=limit) throw Budget{};
                    out->rows.push_back(w*64+b); out->columns.push_back(missing);
                }
            }
            out->single[i]=singles; out->multi[i]=multis; out->refuting[i]=refuters;
            // R is an explicit existing Library refutation, never a C question.
            out->kinds[i]=refuters?3:singles?1:multis?2:0;
            out->offsets.push_back(out->rows.size());
        }
        std::unordered_map<U,U> counts;
        for(size_t i=0;i<count;++i) if(out->kinds[i]==1) {
            if(!(i%64)) signals();
            for(U j=out->offsets[i];j<out->offsets[i+1];++j)
                ++counts[out->rows[j]*U(n)+U(out->columns[j])];
        }
        out->sparse_keys.reserve(counts.size());
        for(const auto &kv:counts) out->sparse_keys.push_back(kv.first);
        std::sort(out->sparse_keys.begin(),out->sparse_keys.end());
        out->sparse_counts.reserve(counts.size());
        for(U key:out->sparse_keys) out->sparse_counts.push_back(counts.at(key));
        signals(); return out;
    } catch(...) { delete out; throw; }
}
extern "C" {
int algen_values(int n,size_t nr,const U *P,int width,int depth,int item,
                   const void *keys,size_t count,const int32_t *fixed,size_t nfixed,
                   const int32_t *offsets,const int32_t *values,size_t limit,void **result) {
    // Publish ownership into caller-owned memory before returning through
    // ctypes: a pending Python signal can interrupt assignment of a return
    // pointer, but it cannot hide this slot from the caller's finally block.
    *result=nullptr;
    try { *result=classify(n,nr,P,width,depth,item,keys,count,fixed,nfixed,offsets,values,limit); return 0; }
    catch(const Interrupted &) { return -1; }
    catch(const Budget &) { PyErr_SetString(PyExc_OverflowError,"value event budget exceeded"); return -1; }
    catch(const std::invalid_argument &e) { PyErr_SetString(PyExc_ValueError,e.what()); return -1; }
    catch(const std::bad_alloc &) { PyErr_NoMemory(); return -1; }
    catch(const std::exception &e) { PyErr_SetString(PyExc_RuntimeError,e.what()); return -1; }
    catch(...) { PyErr_SetString(PyExc_RuntimeError,"native value classification failed"); return -1; }
}
size_t algen_values_size(void *h,int kind) {
    auto &v=*static_cast<Values*>(h);
    switch(kind) {
        case 0:return v.kinds.size(); case 1:return v.single.size(); case 2:return v.multi.size();
        case 3:return v.refuting.size(); case 4:return v.offsets.size(); case 5:return v.rows.size();
        case 6:return v.columns.size(); case 7:return v.sparse_keys.size(); case 8:return v.sparse_counts.size();
    }
    return 0;
}
const void *algen_values_data(void *h,int kind) {
    auto &v=*static_cast<Values*>(h);
    switch(kind) {
        case 0:return v.kinds.data(); case 1:return v.single.data(); case 2:return v.multi.data();
        case 3:return v.refuting.data(); case 4:return v.offsets.data(); case 5:return v.rows.data();
        case 6:return v.columns.data(); case 7:return v.sparse_keys.data(); case 8:return v.sparse_counts.data();
    }
    return nullptr;
}
void algen_values_free(void *h) { delete static_cast<Values*>(h); }
}
