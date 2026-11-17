"""Earlier sort checks preserve ordered terms AND graph construction effects."""

import unittest
from unittest.mock import patch

from algen import table as T
from algen.logic import Vocab


class TypedUniverseTest(unittest.TestCase):
    def compare(self,vocab,base,size,archive=()):
        original = T.scheme
        results = []
        for enabled in (False,True):
            graphs = []
            def capture(*args,**kw):
                result = original(*args,**kw)
                graphs.append(result[0])
                return result
            with patch.object(T,'TYPED_UNIVERSE',enabled), \
                 patch.object(T,'archive_terms',return_value=list(archive)), \
                 patch.object(T,'scheme',side_effect=capture):
                terms = T.size_universe(vocab,base,size)
            self.assertEqual(len(graphs),1)
            graph = [(str(t),info.sort,tuple((k,str(v)) for k,v in info.links.items()),info.depth)
                     for t,info in graphs[0].terms.items()]
            results.append((terms,graph))
        self.assertEqual(results[0],results[1],(base,size))
        return results[1][0]

    def test_all_bases_all_constructions_size_one(self):
        v = Vocab.section('grp')
        for base in T.BASES:
            with self.subTest(base=base):
                self.compare(v,base,1)

    def test_size_two_dependent_slots_subsorts_arithmetic_and_archive(self):
        v = Vocab.section('grp')
        fixtures = [
            (('G','GN','GMN','AB'),('center','aut','inn','quotient','normalizer','prod','meet','ord','index')),
            (('GHF','GE','GFE','GxF'),('ker','im','id-mor','compose','apply-mor','equalizer','pullback','preimage')),
            (('MN','n','pqG'),('num-add','num-mul','num-sub','num-gcd','num-pow','num-phi')),
        ]
        for bases,ops in fixtures:
            with patch.object(T,'CONS',list(ops)),patch.object(T,'SIZE_EXTRA',[]):
                for base in bases:
                    with self.subTest(base=base):
                        terms = self.compare(v,base,2,('60','index(G,center(G))') if base=='G' else ())
                        if base=='GN':
                            self.assertIn('center(N)',terms)  # Sub fits Obj
                        if base=='G':
                            self.assertIn('quotient(aut(G), inn(G))',terms)
                            self.assertIn('num:60()',terms)


if __name__=='__main__':
    unittest.main()
