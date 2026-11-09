"""Список схем для пакетного перебора.

Схема — переменные (база) и термы-конструкции над ними. Условие перебора
говорит о свойствах переменных и термов, поэтому схема с набором термов S
покрывает все условия, где встречаются только термы из S. Условие с двумя
посылками и целью касается не больше трёх термов, так что достаточно схем
«база + не больше k термов» (k = 3 по умолчанию); условия о меньшем числе
термов повторяются в нескольких схемах и склеиваются в общей сводке.

    cd py && python3 -m algen.schemes --термов 2 > ../data/schemes/grp.txt
"""

import argparse
from itertools import combinations

# База: (id, условие, термы глубины ⩽ 2, которые библиотека умеет считать
# или выводит теория).
BASES = [
    ("G", "∀ G : Grp", [
        "center(G)", "commutator(G)", "ab(G)", "G / center(G)", "G / commutator(G)",
        "center(commutator(G))", "commutator(commutator(G))", "center(G / center(G))",
    ]),
    ("GN", "∀ G : Grp; ∀ N : Sub(G)", [
        "G / N", "normalizer(G, N)", "centralizer(G, N)", "normal-closure(G, N)",
        "center(G)", "commutator(G)", "center(N)", "commutator(N)",
    ]),
    ("AB", "∀ A : Grp; ∀ B : Grp", [
        "A × B", "A ∗ B", "A ≀ B", "B ≀ A", "center(A × B)", "commutator(A × B)",
    ]),
    ("GHK", "∀ G : Grp; ∀ H : Sub(G); ∀ K : Sub(G)", [
        "meet(G, H, K)", "join(G, H, K)", "normalizer(G, H)", "centralizer(G, H)",
    ]),
    ("GMN", "∀ G : Grp; ∀ M : Sub(G); ∀ N : Sub(M)", [
        "M / N", "G / M", "normal-closure(M, N)",
    ]),
    ("GHF", "∀ G : Grp; ∀ H : Grp; ∀ F : Mor(G, H)", [
        "ker(F)", "im(F)", "G / ker(F)",
    ]),
]


def schemes(k=3, bases=None):
    for bid, decl, terms in BASES:
        if bases and bid not in bases:
            continue
        for r in range(0, min(k, len(terms)) + 1):
            for ts in combinations(terms, r):
                sid = bid + ("-" + "-".join(str(terms.index(t) + 1) for t in ts) if ts else "")
                yield sid, decl, ts


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--термов", dest="k", type=int, default=3)
    ap.add_argument("--базы", dest="bases", default="", help="через запятую: G,GN,AB,GHK,GMN,GHF")
    a = ap.parse_args()
    print("# id | условие | термы  (python3 -m algen.schemes)")
    for bid, decl, terms in BASES:
        print(f"# {bid}: " + "; ".join(f"{i + 1} = {t}" for i, t in enumerate(terms)))
    for sid, decl, ts in schemes(a.k, set(filter(None, a.bases.split(",")))):
        print(f"{sid} | {decl} | {'; '.join(ts)}")


if __name__ == "__main__":
    main()
