// Выгружает правила раздела в том виде, в каком их видит вывод: сокращения
// (preserves, reflects, gives) развёрнуты, контрапозиции и почленные копии
// отброшены — они равносильны исходным и отдельной проверки не требуют.
//
//   node tools/dump-rules.mjs grp > /tmp/grp-rules.json

import { category } from '../src/load.js';
import { правила } from '../src/deduce.js';

const cat = category(process.argv[2] ?? 'grp');
const прямые = правила(cat).filter((r) => !r.почленно && !/\(наоборот/.test(r.id));
const gives = [...cat.cons.values()]
  .filter((c) => c.gives)
  .map((c) => ({ op: c.id, in: c.in ?? [], gives: c.gives }));
console.log(JSON.stringify({ rules: прямые, gives }, null, 1));
