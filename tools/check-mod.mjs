// Сверка базы модулей с моделью модулей.
//
//   node tools/check-mod.mjs [--подробно]
//
// Тот же приём, что у групп: правила написаны рукой по учебнику, модель
// считает по таблицам умножения, и ни одна из двух сторон не выводится из
// другой. Прогон каждого правила по всем парам (кольцо, модуль) библиотеки —
// единственное, что ловит опечатку в базе и ошибку в модели сразу.
//
// Отдельно проверяется ГРАНИЦА модели: правило, у которого посылки ни разу не
// сошлись, не проверено вовсе, и молчать об этом нельзя — иначе «расхождений
// нет» читается как «всё верно», хотя половина базы могла не испытываться.

import { category, каталогМодулей } from '../src/load.js';
import { TermGraph } from '../src/term.js';
import { правила } from '../src/deduce.js';
import { привязки, свойства, отношение } from '../src/model/instance.js';
import { НЕ_СЧИТАЕМ } from '../src/model/значение.js';

const подробно = process.argv.includes('--подробно');
const cat = category('mod');
const каталог = каталогМодулей();
const беды = [];

// Сцена правила настоящим графом: роли по сортам, термы правила достраиваются
// теми же apply, что и в переборе.
function собрать(rule) {
  const g = new TermGraph(cat);
  const узлы = new Map();
  const порядок = [];
  // Кольцо в сцене ОДНО, даже если правило его не называет. Иначе два модуля
  // окажутся над разными кольцами, и согласование слотов честно не даст
  // построить между ними гомоморфизм — сцена просто не соберётся.
  let общее = null;
  const кольцо = () => (общее ??= g.apply('choose-ring', []));
  for (const r of rule.scene) {
    let id;
    if (r.sort === 'Ring.obj') id = (общее ??= g.apply('choose-ring', []));
    else if (r.sort === 'Mod.obj') {
      const R = r.base ? узлы.get(r.base) : кольцо();
      if (R === undefined) return null;
      id = g.apply('choose-mod', [R]);
    } else if (r.sort === 'Mod.sub') {
      const M = узлы.get(r.ambient);
      if (M === undefined) return null;
      id = g.apply('choose-submod', [M]);
    } else if (r.sort === 'Mod.mor') {
      const M = узлы.get(r.dom);
      const N = узлы.get(r.cod);
      if (M === undefined || N === undefined) return null;
      id = g.apply('choose-mod-mor', [M, N]);
    } else return null;
    узлы.set(r.name, id);
    порядок.push(id);
  }

  const построить = (образец) => {
    if (typeof образец === 'string') return узлы.get(образец) ?? null;
    const args = (образец.args ?? []).map(построить);
    if (args.some((x) => x === null)) return null;
    try {
      return g.apply(образец.op, args);
    } catch {
      return null;
    }
  };
  const атомы = [...rule.if, rule.then].map((a) => ({
    ...a,
    узлы: a.rel ? a.args.map(построить) : [построить(a.t)],
  }));
  if (атомы.some((a) => a.узлы.some((x) => x === null))) return null;
  // Свободны ровно те вершины, что модель выбирает; остальное достраивается.
  const свободные = g.nodes
    .filter((n) => cat.cons.get(n.op)?.choice)
    .map((n) => n.id);
  return { g, узлы, атомы, свободные };
}

const значениеАтома = (значения, a) => (a.rel
  ? отношение(a.rel, значения.get(a.узлы[0]), значения.get(a.узлы[1]))
  : свойства(значения.get(a.узлы[0]))[a.p]);

let проверено = 0;
let сработало = 0;
const непроверенные = [];
const пропущенные = [];

for (const rule of правила(cat)) {
  const сцена = собрать(rule);
  if (!сцена) {
    пропущенные.push(rule.id);
    continue;
  }
  const { g, атомы, свободные } = сцена;
  const посылки = атомы.slice(0, -1);
  const вывод = атомы[атомы.length - 1];
  let сошлось = 0;
  let испытано = 0;

  for (const значения of привязки(g, свободные, каталог, 4000, 12)) {
    let всеВерны = true;
    for (const a of посылки) {
      const v = значениеАтома(значения, a);
      if (v === undefined || v !== (a.значение !== false)) {
        всеВерны = false;
        break;
      }
    }
    if (!всеВерны) continue;
    сошлось++;
    проверено++;
    const v = значениеАтома(значения, вывод);
    if (v === undefined) continue;
    испытано++;
    сработало++;
    if (v !== (вывод.значение !== false)) {
      беды.push(`правило «${rule.id}» ложно: ${описание(g, значения)}`);
    }
  }
  if (испытано === 0) непроверенные.push(`${rule.id} (посылки сошлись ${сошлось} раз)`);
  if (подробно) console.log(`${rule.id}: посылки ${сошлось}, вывод проверен ${испытано}`);
}

function описание(g, значения) {
  const куски = [];
  for (const [id, v] of значения) {
    const n = g.get(id);
    if (v.вид === 'кольцо') куски.push(`${n.sort === 'Ring.obj' ? 'кольцо' : '?'} ${v.имя}`);
    else if (v.вид === 'модуль' || v.вид === 'подмодуль') {
      const имя = v.A?.вид === 'имя' ? v.A.зап.имя : v.A?.вид === 'именПод' ? v.A.зап.имя : null;
      куски.push(имя ?? `${v.вид} порядка ${v.A?.G?.n ?? v.A?.H?.length ?? '?'}`);
    } else if (v.вид === 'модморфизм') куски.push('гомоморфизм');
  }
  return куски.join(', ');
}

console.log(`колец: ${каталог.кольца.length}, модулей в библиотеке: ${каталог.модули.length}`);
console.log(`правил в базе: ${правила(cat).length}, срабатываний вывода: ${сработало} `
  + `(посылки сходились ${проверено} раз)`);
if (пропущенные.length) {
  console.log(`сцену не собрать у ${пропущенные.length}: ${пропущенные.slice(0, 5).join('; ')}`);
}
if (непроверенные.length) {
  console.log(`\nНЕ ПРОВЕРЕНО МОДЕЛЬЮ (${непроверенные.length}) — это граница модели, а не успех:`);
  for (const r of непроверенные) console.log(`  ${r}`);
}
if (беды.length) {
  console.error(`\nРАСХОЖДЕНИЯ (${беды.length}):`);
  for (const b of [...new Set(беды)].slice(0, 30)) console.error(`  ${b}`);
  process.exit(1);
}
console.log('расхождений нет: база модулей не противоречит модели модулей');
