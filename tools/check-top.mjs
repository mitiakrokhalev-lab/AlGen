// Сверка базы топологии с моделью топологии.
//
//   node tools/check-top.mjs [--подробно]
//
// Тот же приём, что у групп и модулей: правила написаны рукой по учебнику,
// модель считает предпорядки, и ни одна сторона не выводится из другой. Прогон
// каждого правила по всем пространствам библиотеки — единственное, что ловит
// опечатку в базе и ошибку в модели сразу.
//
// Отдельно печатается ГРАНИЦА: правило, у которого посылки ни разу не сошлись
// или вывод ни разу не проверился, не проверено вовсе. Для топологии это особо
// важно — у конечных пространств половина свойств вырождена, и «расхождений
// нет» без этого списка читалось бы как «база верна».

import { category, каталогПространств } from '../src/load.js';
import { TermGraph } from '../src/term.js';
import { правила } from '../src/deduce.js';
import { привязки, свойства, отношение } from '../src/model/instance.js';

const подробно = process.argv.includes('--подробно');
const cat = category('top');
const каталог = каталогПространств();
const беды = [];

function собрать(rule) {
  const g = new TermGraph(cat);
  const узлы = new Map();
  for (const r of rule.scene) {
    let id;
    if (r.sort === 'Top.obj') id = g.apply('choose-space', []);
    else if (r.sort === 'Top.sub') {
      const X = узлы.get(r.ambient);
      if (X === undefined) return null;
      id = g.apply('choose-sub', [X]);
    } else if (r.sort === 'Top.mor') {
      const X = узлы.get(r.dom);
      const Y = узлы.get(r.cod);
      if (X === undefined || Y === undefined) return null;
      id = g.apply('choose-map', [X, Y]);
    } else return null;
    узлы.set(r.name, id);
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
  const свободные = g.nodes.filter((n) => cat.cons.get(n.op)?.choice).map((n) => n.id);
  return { g, атомы, свободные };
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

  for (const значения of привязки(g, свободные, каталог, 3000, 4)) {
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
  for (const [, v] of значения) {
    if (v.вид === 'имяпростр' || v.вид === 'имяподпр') куски.push(v.зап.имя);
    else if (v.вид === 'простр') куски.push(v.X.имя ?? `${v.X.n} точек`);
    else if (v.вид === 'подпростр') куски.push(`подпространство {${v.A.join(',')}}`);
    else if (v.вид === 'топотоб') куски.push(`отображение ${v.φ.join('')}`);
  }
  return куски.join(', ');
}

console.log(`пространств в библиотеке: ${каталог.length} `
  + `(конечных ${каталог.filter((x) => !x.бесконечное).length}, объявленных ${каталог.filter((x) => x.бесконечное).length})`);
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
console.log('расхождений нет: база топологии не противоречит модели топологии');
