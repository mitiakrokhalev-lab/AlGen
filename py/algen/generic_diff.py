"""Сверка generic_filter до/после поправки класса (дыра 4.11): какие условия об
одном терме старый фильтр снимал при ALGEN_CLASS, хотя терм не доказуемо в
классе. Старый фильтр = новый без ALGEN_CLASS.

    python3 -m algen.generic_diff finite 3 "∀ G : Grp" "center(G); commutator(G)"
"""
import os
import sys
import time

from algen import enumerate as E
from algen.library import built_library
from algen.logic import Var, Vocab

cls, k = sys.argv[1], int(sys.argv[2])
t0 = time.time()
v = Vocab.section("grp")
lib = built_library(v)
form = E.SchemeForm(lib, v, sys.argv[3], [x for x in sys.argv[4].split(";") if x.strip()])
print(f"форма {time.time() - t0:.0f} с, матрица {form.m.shape}", flush=True)
# как table.view: таблица базы G для фильтра и класс как гипотеза базы
GV = next(t for t in form.own if isinstance(t, Var))
form.generic = (form.m if E.CLOSE_MARKED else form.e, {a[1]: i for i, a in enumerate(form.atoms) if a[0] == "p" and a[2] == GV})
a = ("p", cls, GV)
form.fixed_lits = list(form.fixed_lits) + [(a, True)]
form.fixed = list(form.fixed) + [2 * form.index[a]]
alive, empty = E.enumerate_form(form, k, m=form.m if E.CLOSE_MARKED else None)
mins = E.minimal(alive)
print(f"перебор {time.time() - t0:.0f} с, минимальных {len(mins)}", flush=True)
os.environ.pop("ALGEN_COMPRESS", None)
os.environ.pop("ALGEN_CLASS", None)
old = E.generic_filter(form, dict(mins))
n_old = form.n_generic
os.environ["ALGEN_CLASS"] = cls
new = E.generic_filter(form, dict(mins))
back = set(new) - set(old)
extra = set(old) - set(new)
print(f"класс {cls}: старый снял {n_old}, новый снял {form.n_generic}; вернулось {len(back)}, "
      f"лишних (снято новым, но не старым) {len(extra)}, оставлено из-за класса {form.generic_kept_class}")
terms = {}
for prem, g in back:
    t = form.lit(g)[0][2]
    terms[str(t)] = terms.get(str(t), 0) + 1
print("вернувшиеся по термам:", terms)
for prem, g in sorted(back)[:15]:
    ls = [l for j in prem for l in form.lits(j)]
    print("  ", " & ".join(E.lit_name(*x) for x in ls), "⇒", E.lit_name(*form.lit(g)))
sys.exit(1 if extra else 0)
