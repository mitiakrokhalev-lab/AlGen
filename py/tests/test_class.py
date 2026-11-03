"""Полнота класса перебора k ⩽ 3, s ⩽ 2 (ALGEN_SIZE=2): генератор не теряет молча
ни конструкций, ни свойств, ни отношений словаря.

Сужать класс может только Дима; каждое исключение записано в table.EXCLUDED_OPS
с причиной. Тесты падают, если что-то выпало из перебора без записи.

    cd py && python3 -m unittest tests.test_class
"""

import os
import re
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PY = ROOT / "py"


def run_size(code):
    """Код в отдельном процессе с ALGEN_SIZE=2 (флаг читается при импорте модулей)."""
    env = dict(os.environ, ALGEN_SIZE="2", ALGEN_FAST="1")
    r = subprocess.run([sys.executable, "-c", code], cwd=PY, env=env, capture_output=True, text=True, timeout=900)
    if r.returncode:
        raise AssertionError(r.stderr[-3000:])
    return r.stdout


class ClassTest(unittest.TestCase):
    def test_every_construction_listed(self):
        """Каждая конструкция словаря — во вселенной или в реестре исключений с причиной."""
        from algen import table as t
        v = t.Vocab.section("grp")
        used, excl = set(t.CONS) | set(t.SIZE_EXTRA), set(t.EXCLUDED_OPS)
        self.assertEqual(sorted(set(v.cons) - used - excl), [], "конструкции словаря вне перебора и вне реестра")
        self.assertEqual(sorted(used & excl), [], "конструкция и в переборе, и в исключениях")
        self.assertTrue(all(r.strip() for r in t.EXCLUDED_OPS.values()), "исключение без причины")

    def test_constructions_reach_universe(self):
        """Конструкция из списка вселенной действительно строится хотя бы у одной базы."""
        out = run_size(
            "from algen import table as t\n"
            "v = t.Vocab.section('grp')\n"
            "ops = set()\n"
            "def walk(x):\n"
            "    import re\n"
            "    ops.update(re.findall(r'([a-z][a-z0-9-]*)\\(', x))\n"
            "for b in ('G', 'GN', 'GNy', 'GFE', 'GX', 'GXxy', 'Gx', 'Fam', 'D', 'n', 'P', 'NQA'):\n"
            "    for x in t.universe(v, b):\n"
            "        walk(x)\n"
            "print(' '.join(sorted(set(t.CONS) | set(t.SIZE_EXTRA))))\n"
            "print(' '.join(sorted(ops)))\n")
        want, got = (set(l.split()) for l in out.strip().splitlines()[-2:])
        # num-* и семейства по числу строятся у числовых баз; остальное — у групповых
        self.assertEqual(sorted(want - got), [], "конструкции, которые не строятся ни у одной базы")

    def test_full_props(self):
        """У каждого терма вселенной — все свойства словаря, подходящие его сорту."""
        out = run_size(
            "from algen import table as t, enumerate as E\n"
            "class T:\n"
            "    def __init__(self, *a, **k): pass\n"
            "    def solver(self): return None\n"
            "E.Theory = T\n"
            "E.Search = lambda *a, **k: None\n"
            "v = t.Vocab.section('grp')\n"
            "assert E.FULL_PROPS and not E.SKIP\n"
            "f = E.SchemeForm(None, v, t.BASES['D'], t.universe(v, 'D'), with_rows=False)\n"
            "have = {(a[1], a[2]) for a in f.atoms if a[0] == 'p'}\n"
            "miss = [(p, str(x)) for x in f.own for p in v.props if v.prop_fits(p, f.g.terms[x].sort) and (p, x) not in have]\n"
            "print(len(miss), miss[:5])\n")
        self.assertTrue(out.strip().startswith("0 "), out)

    def test_relations_all_pairs(self):
        """Отношения словаря заводятся у всех подходящих пар термов, а не только с переменной."""
        out = run_size(
            "from algen import enumerate as E\n"
            "from algen.etalon import scheme, term\n"
            "from algen.logic import Vocab\n"
            "v = Vocab.section('grp')\n"
            "g, _, _ = scheme(v, {'раздел': 'grp', 'условие': '∀ G : Grp; ∀ N : Sub(G)'})\n"
            "names = {str(x): x for x in g.terms}\n"
            "ts = [term(g, s, names, 'grp') for s in ('center(G)', 'commutator(G)', 'normalizer(G, N)', 'quotient(G, center(G))')]\n"
            "own = list(g.terms) + ts\n"
            "rel = {(a[1], a[2], a[3]) for a in E.relation_atoms(g, own)}\n"
            "subs = [x for x in own if g.terms[x].sort == 'Grp.sub']\n"
            "objs = [x for x in own if v.fits(g.terms[x].sort, 'Grp.obj')]\n"
            "miss = []\n"
            "for a in subs:\n"
            "    for b in subs:\n"
            "        if a != b and g.terms[a].links.get('ambient') == g.terms[b].links.get('ambient'):\n"
            "            x, y = sorted((a, b), key=str)\n"
            "            miss += [(r, str(x), str(y)) for r in ('eq-sub', 'conj-sub', 'permutes') if r in v.rels and (r, x, y) not in rel]\n"
            "            miss += [('le', str(a), str(b))] if ('le', a, b) not in rel else []\n"
            "for a in objs:\n"
            "    for b in objs:\n"
            "        if a != b:\n"
            "            x, y = sorted((a, b), key=str)\n"
            "            miss += [('iso', str(x), str(y))] if ('iso', x, y) not in rel else []\n"
            "            miss += [('embeds', str(a), str(b))] if ('embeds', a, b) not in rel else []\n"
            "print(len(miss), miss[:5])\n")
        self.assertTrue(out.strip().startswith("0 "), out)

    def test_no_silent_skips_in_workflows(self):
        """Ни один рабочий прогон не пропускает свойства флагом «--без»."""
        bad = []
        for f in sorted((ROOT / ".github" / "workflows").glob("*.yml")):
            for i, line in enumerate(f.read_text().splitlines(), 1):
                if re.search(r"--без\s+[a-z]", line) or re.search(r"SKIP:\s*\"[a-z]", line):
                    bad.append(f"{f.name}:{i}: {line.strip()}")
        self.assertEqual(bad, [], "пропуск свойств — сужение класса, его решает Дима")


if __name__ == "__main__":
    unittest.main()
