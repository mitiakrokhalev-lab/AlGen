// Проверка руками написанных бесконечных групп правилами базы.
//
//   node tools/check-infinite.mjs
//
// Конечные группы вычисляются, и ошибиться в них негде. Бесконечные объявлены
// рукой — значит ошибиться можно где угодно, и единственная защита та же, что
// у конечных: прогнать по ним ВСЕ правила базы, написанные раньше и
// независимо. Плюс проверки самой записи: фактор берётся только по нормальной
// подгруппе, вся группа как подгруппа обязана иметь те же свойства, что сам
// объект, и так далее.

import { category, каталогГрупп } from '../src/load.js';
import { TermGraph } from '../src/term.js';
import { правила } from '../src/deduce.js';
import { вычислитьУзел, свойства, отношение } from '../src/model/instance.js';
import { НЕ_СЧИТАЕМ } from '../src/model/значение.js';
import { подзначение } from '../src/model/named.js';

const cat = category('grp');
const каталог = каталогГрупп({ полный: true });
const бесконечные = каталог.filter((x) => x.бесконечная);
const семейства = каталог.filter((x) => x.семейство);
const системы = каталог.filter((x) => x.система);
const беды = [];

// --- проверки самой записи ---------------------------------------------------

for (const з of бесконечные) {
  const поId = new Map((з.подгруппы ?? []).map((п) => [п.id, п]));
  const целые = (з.подгруппы ?? []).filter((п) => п.props?.whole === true);
  if (целые.length !== 1) {
    беды.push(`${з.id}: подгрупп со свойством whole должно быть ровно одна, а их ${целые.length}`);
  } else if (целые[0].объект !== з.id) {
    беды.push(`${з.id}: подгруппа «вся» объявлена изоморфной ${целые[0].объект}, а не самой группе`);
  } else {
    for (const [p, v] of Object.entries(з.props ?? {})) {
      const у = свойства(подзначение(целые[0]))[p];
      if (у !== undefined && у !== v) {
        беды.push(`${з.id}: у подгруппы «вся» свойство ${p} = ${у}, а у самой группы ${v}`);
      }
    }
  }
  for (const k of Object.keys(з.факторы ?? {})) {
    const п = поId.get(k);
    if (!п) беды.push(`${з.id}: фактор по неизвестной подгруппе «${k}»`);
    else if (п.props?.normal !== true) беды.push(`${з.id}: фактор по ненормальной «${k}»`);
  }
  for (const п of з.подгруппы ?? []) {
    if (п.props?.characteristic === true && п.props?.normal !== true) {
      беды.push(`${з.id}/${п.id}: характеристична, но не объявлена нормальной`);
    }
    if (п.props?.whole === true && п.props?.normal !== true) {
      беды.push(`${з.id}/${п.id}: вся группа обязана быть нормальной`);
    }
  }

  // Морфизм: инъективность и сюръективность — это НЕ отдельные сведения, а
  // тривиальность ядра и полнота образа. Записанное обязано совпасть.
  for (const м of з._морфизмы ?? []) {
    const где = `${з.id} → ${м.код?.вид === 'имя' ? м.код.зап.id : м.код?.G?.имя}`;
    const тривЯдро = м.ядро ? свойства(м.ядро).trivial : undefined;
    const полныйОбраз = м.образ ? свойства(м.образ).whole : undefined;
    if (м.props.injective !== undefined && тривЯдро !== undefined
      && м.props.injective !== тривЯдро) {
      беды.push(`${где}: инъективность ${м.props.injective}, а ядро тривиально = ${тривЯдро}`);
    }
    if (м.props.surjective !== undefined && полныйОбраз !== undefined
      && м.props.surjective !== полныйОбраз) {
      беды.push(`${где}: сюръективность ${м.props.surjective}, а образ полон = ${полныйОбраз}`);
    }
    if (м.ядро && свойства(м.ядро).normal !== true) {
      беды.push(`${где}: ядро обязано быть нормальной подгруппой`);
    }
    if (м.props['zero-mor'] === true && полныйОбраз === true && свойства(м.код).trivial !== true) {
      беды.push(`${где}: нулевой морфизм не может быть сюръективным на нетривиальную группу`);
    }
  }
}

// --- проверка правилами базы ---------------------------------------------------

// Сцена правила строится настоящим графом, и термы правила вычисляются тем же
// вычислителем, что работает при поиске. Иначе проверка проверяла бы не то.
function собратьСцену(rule) {
  const роли = rule.scene;
  const семьи = роли.filter((r) => r.sort === 'Grp.fam');
  if (семьи.length === 1 && роли.length === 1) return собратьСемью(rule, семьи[0]);
  const сист = роли.filter((r) => r.sort === 'Grp.diag');
  if (сист.length === 1 && роли.length === 1) return собратьСистему(rule, сист[0]);
  const объекты = роли.filter((r) => r.sort === 'Grp.obj');
  const подгруппы = роли.filter((r) => r.sort === 'Grp.sub');
  if (объекты.length + подгруппы.length !== роли.length) return null;
  if (подгруппы.length > 1) return null;
  if (подгруппы.length === 1 && подгруппы[0].ambient !== объекты[0]?.name) return null;
  if (объекты.length > 2) return null;

  const g = new TermGraph(cat);
  const узлы = new Map();
  for (const r of объекты) узлы.set(r.name, g.given('Grp.obj'));
  for (const r of подгруппы) узлы.set(r.name, g.apply('choose-sub', [узлы.get(r.ambient)]));

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
  return { g, узлы, атомы, объекты, подгруппы };
}

// Правило про семейство («произведение семейства абелевых абелево») проверяется
// на ОБЪЯВЛЕННЫХ бесконечных семействах: у конечных ∏ и ⊕ совпадают, и такая
// проверка ничего бы не значила.
function собратьСемью(rule, роль) {
  const g = new TermGraph(cat);
  const узлы = new Map([[роль.name, g.apply('choose-fam', [])]]);
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
  return { g, узлы, атомы, объекты: [], подгруппы: [], семья: роль };
}

// Правило про направленную систему («прямой предел абелевых абелев»)
// проверяется на ОБЪЯВЛЕННЫХ системах: у постоянных оба предела равны самой
// группе, и такая проверка ничего бы не значила.
function собратьСистему(rule, роль) {
  const g = new TermGraph(cat);
  const узлы = new Map([[роль.name, g.apply('choose-diag', [])]]);
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
  return { g, узлы, атомы, объекты: [], подгруппы: [], система: роль };
}

function значенияАтома(g, значения, a) {
  if (a.rel) return отношение(a.rel, значения.get(a.узлы[0]), значения.get(a.узлы[1]));
  const v = значения.get(a.узлы[0]);
  return v ? свойства(v)[a.p] : undefined;
}

let проверено = 0;
let сработало = 0;

for (const rule of правила(cat)) {
  const сцена = собратьСцену(rule);
  if (!сцена) continue;
  const { g, узлы, атомы, объекты, подгруппы, семья, система } = сцена;
  if (система) {
    for (const с of системы) {
      const значения = new Map([[узлы.get(система.name), { вид: 'имясистема', зап: с }]]);
      let целиком = true;
      for (const n of g.nodes) {
        if (значения.has(n.id) || n.op === 'choose-diag') continue;
        const v = вычислитьУзел(g, n.id, значения);
        if (v === null || v === НЕ_СЧИТАЕМ) { целиком = false; break; }
        значения.set(n.id, v);
      }
      if (!целиком) continue;
      const посылки = атомы.slice(0, -1);
      const вывод = атомы[атомы.length - 1];
      if (!посылки.every((a) => значенияАтома(g, значения, a) === (a.значение !== false))) continue;
      проверено++;
      const v = значенияАтома(g, значения, вывод);
      if (v === undefined) continue;
      сработало++;
      if (v !== (вывод.значение !== false)) {
        беды.push(`правило «${rule.id}» ложно на системе ${с.имя}`);
      }
    }
    continue;
  }
  if (семья) {
    for (const с of семейства) {
      const значения = new Map([[узлы.get(семья.name), { вид: 'имясемья', зап: с }]]);
      let целиком = true;
      for (const n of g.nodes) {
        if (значения.has(n.id) || n.op === 'choose-fam') continue;
        const v = вычислитьУзел(g, n.id, значения);
        if (v === null || v === НЕ_СЧИТАЕМ) { целиком = false; break; }
        значения.set(n.id, v);
      }
      if (!целиком) continue;
      const посылки = атомы.slice(0, -1);
      const вывод = атомы[атомы.length - 1];
      if (!посылки.every((a) => значенияАтома(g, значения, a) === (a.значение !== false))) continue;
      проверено++;
      const v = значенияАтома(g, значения, вывод);
      if (v === undefined) continue;
      сработало++;
      if (v !== (вывод.значение !== false)) {
        беды.push(`правило «${rule.id}» ложно на семействе ${с.имя}`);
      }
    }
    continue;
  }

  // В каталоге живут не только группы: там же объявленные СЕМЕЙСТВА и
  // СИСТЕМЫ, у которых нет ни таблицы умножения, ни свойств группы. Пока ни
  // одно правило не брало двух свободных объектов без конструкции между ними,
  // это не всплывало; правила переноса по изоморфизму берут ровно таких двух,
  // и сверщик падал на первой же системе.
  const группыКаталога = каталог.filter((x) => !x.семейство && !x.система);
  const наборыОбъектов = объекты.length === 1
    ? бесконечные.map((з) => [з])
    : бесконечные.flatMap((a) => группыКаталога.map((b) => [a, b]));

  for (const набор of наборыОбъектов) {
    const базовые = new Map();
    объекты.forEach((r, i) => {
      const x = набор[i];
      базовые.set(узлы.get(r.name), x.бесконечная ? { вид: 'имя', зап: x } : { вид: 'группа', G: x });
    });
    const варианты = подгруппы.length
      ? (набор[0].подгруппы ?? []).map((п) => подзначение(п))
      : [null];

    for (const под of варианты) {
      const значения = new Map(базовые);
      if (под) значения.set(узлы.get(подгруппы[0].name), под);
      // Достроить все термы правила; невычислимое отменяет проверку.
      let целиком = true;
      for (const n of g.nodes) {
        if (значения.has(n.id)) continue;
        if (n.op === 'given' || n.op === 'choose-sub') continue;
        const v = вычислитьУзел(g, n.id, значения);
        if (v === null || v === НЕ_СЧИТАЕМ) {
          целиком = false;
          break;
        }
        значения.set(n.id, v);
      }
      if (!целиком) continue;

      const посылки = атомы.slice(0, -1);
      const вывод = атомы[атомы.length - 1];
      let всеВерны = true;
      for (const a of посылки) {
        const v = значенияАтома(g, значения, a);
        if (v === undefined) {
          всеВерны = false;
          break;
        }
        if (v !== (a.значение !== false)) {
          всеВерны = false;
          break;
        }
      }
      if (!всеВерны) continue;
      проверено++;
      const v = значенияАтома(g, значения, вывод);
      if (v === undefined) continue;
      сработало++;
      if (v !== (вывод.значение !== false)) {
        беды.push(
          `правило «${rule.id}» ложно на ${набор.map((x) => x.имя ?? x.id).join(', ')}`
          + (под ? ` (подгруппа ${под.зап.имя})` : ''),
        );
      }
    }
  }
}

console.log(`объявленных систем: ${системы.length}, семейств: ${семейства.length}`);
console.log(`бесконечных групп: ${бесконечные.length}, подгрупп объявлено: ` +
  `${бесконечные.reduce((s, з) => s + (з.подгруппы?.length ?? 0), 0)}`);
console.log(`срабатываний правил на них: ${сработало} (посылки сошлись ${проверено} раз)`);

if (беды.length) {
  console.error(`\nРАСХОЖДЕНИЯ (${беды.length}):`);
  for (const b of [...new Set(беды)].slice(0, 40)) console.error(`  ${b}`);
  process.exit(1);
}
console.log('расхождений нет: объявленные бесконечные группы не противоречат ни одному правилу базы');
