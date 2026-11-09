// Выгружает словарь и правила раздела в том виде, в каком их видит вывод:
// сокращения (preserves, reflects) развёрнуты в правила, контрапозиции и
// почленные копии отброшены — они равносильны исходным, а новый движок
// (py/algen/logic.py) получает контрапозицию сам, как следствие клаузы.
//
//   node tools/dump-rules.mjs grp > data/vocab/grp.json

import { category } from '../src/load.js';
import { правила } from '../src/deduce.js';

const cat = category(process.argv[2] ?? 'grp');
const прямые = правила(cat).filter((r) => !r.почленно && !/\(наоборот/.test(r.id));
const cons = [...cat.cons.values()].map((c) => ({
  id: c.id, in: c.in ?? [], out: c.out, gives: c.gives ?? null,
  commutative: c.commutative === true,
}));
console.log(JSON.stringify({
  id: cat.id,
  subsorts: [...cat.up].flatMap(([lo, his]) => [...his].filter((h) => h !== lo).map((h) => [lo, h])),
  properties: [...cat.props.values()].map((p) => ({ id: p.id, sort: p.sort })),
  relations: [...cat.rels.values()].map((r) => ({ id: r.id, in: r.in, same: r.same ?? null })),
  constructions: cons,
  degenerations: cat.degen,
  rules: прямые,
  gives: cons.filter((c) => c.gives).map((c) => ({ op: c.id, in: c.in, gives: c.gives })),
}, null, 1));
