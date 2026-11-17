// Проверка объявленных полей и расширений правилами базы.
//
//   node tools/check-fld.mjs
//
// Всё в разделе полей написано рукой, значит ошибиться можно где угодно.
// Защита та же, что у бесконечных групп и у колец: прогнать по библиотеке ВСЕ
// правила базы, написанные раньше и независимо, и потребовать, чтобы ни одно
// не оказалось ложным.
//
// Плюс проверки самой записи, которых правилами не выразить, потому что они
// про СОГЛАСОВАННОСТЬ двух слоёв: порядок группы Галуа обязан равняться
// степени расширения Галуа, а у ненормального — делить её.

import { category, каталогПолей } from '../src/load.js';
import { TermGraph } from '../src/term.js';
import { правила } from '../src/deduce.js';
import { вычислитьУзел, свойства, отношение } from '../src/model/instance.js';
import { НЕ_СЧИТАЕМ } from '../src/model/значение.js';

const cat = category('fld');
const библиотека = каталогПолей();
const { поля, расширения } = библиотека;
const беды = [];

const полеЗн = (зап) => ({ вид: 'полеЗ', зап });
const расширЗн = (зап) => ({ вид: 'расшир', зап });

const порядок = (G) => G?.n ?? G?.порядок ?? null;

// --- проверки самой записи -----------------------------------------------------

for (const S of расширения) {
  const где = S.имя;
  const p = S.props ?? {};
  if (p.galois === true && (p['normal-ext'] === false || p.separable === false)) {
    беды.push(`${где}: объявлено Галуа, но ненормально или несепарабельно`);
  }
  if (p['normal-ext'] === true && p.separable === true && p.algebraic === true && p.galois !== true) {
    беды.push(`${где}: нормально, сепарабельно и алгебраично — обязано быть Галуа`);
  }
  if (p['finite-ext'] === true && p.algebraic !== true) {
    беды.push(`${где}: конечно, а алгебраичность не объявлена`);
  }
  const n = порядок(S._галуа);
  if (n !== null && S.степень !== undefined) {
    // |Gal(L/K)| = [L : K] — это и есть определение расширения Галуа.
    if (p.galois === true && n !== S.степень) {
      беды.push(`${где}: расширение Галуа степени ${S.степень}, а группа порядка ${n}`);
    }
    // У ненормального автоморфизмов меньше, и их число делит степень.
    if (p.galois === false && (n > S.степень || S.степень % n !== 0)) {
      беды.push(`${где}: группа автоморфизмов порядка ${n} не делит степень ${S.степень}`);
    }
  }
}

for (const K of поля) {
  const p = K.props ?? {};
  if (p['prime-field'] === true && K.простое !== K.id) {
    беды.push(`${K.имя}: простое поле обязано быть своим простым подполем`);
  }
  if (p['alg-closed'] === true && K.замыкание !== K.id) {
    беды.push(`${K.имя}: алгебраически замкнутое обязано совпадать со своим замыканием`);
  }
  if (p['finite-field'] === true && p['alg-closed'] === true) {
    беды.push(`${K.имя}: конечное поле не бывает алгебраически замкнутым`);
  }
}

// --- сцена правила --------------------------------------------------------------

function собратьСцену(rule) {
  const g = new TermGraph(cat);
  const узлы = new Map();
  const роли = { поля: [], расширения: [] };
  const записи = (rule.scene ?? []).map((о) => [о.name, о]);
  // Правила про ЧИСЛО («чётная степень конечна») сверять на библиотеке нечем:
  // свободного числового узла в языке нет, число всегда чей-то терм. Их
  // проверяет числовой слой раздела групп, где арифметика та же.
  if (записи.some(([, о]) => о.sort === 'Fld.num')) return null;
  if (записи.some(([, о]) => !String(о.sort).startsWith('Fld.'))) return null;

  for (const [имя, о] of записи) {
    if (о.sort !== 'Fld.obj') continue;
    узлы.set(имя, g.apply('choose-field', []));
    роли.поля.push(имя);
  }
  for (const [имя, о] of записи) {
    if (о.sort !== 'Fld.mor') continue;
    const D = узлы.get(о.dom);
    const C = узлы.get(о.cod);
    if (D === undefined || C === undefined) return null;
    узлы.set(имя, g.apply('choose-ext', [D, C]));
    роли.расширения.push({ имя, dom: о.dom, cod: о.cod });
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
  const атомы = [...(rule.if ?? []), rule.then].map((a) => ({
    ...a,
    узлы: a.rel ? a.args.map(построить) : [построить(a.t)],
  }));
  if (атомы.some((a) => a.узлы.some((x) => x === null || x === undefined))) return null;
  return { g, узлы, атомы, роли };
}

function значенияАтома(значения, a) {
  if (a.rel) return отношение(a.rel, значения.get(a.узлы[0]), значения.get(a.узлы[1]));
  const v = значения.get(a.узлы[0]);
  return v && v !== НЕ_СЧИТАЕМ ? свойства(v)[a.p] : undefined;
}

function* наборы(роли) {
  const выбор = new Map();
  function* поПолям(k) {
    if (k === роли.поля.length) { yield* поРасширениям(0); return; }
    for (const K of поля) { выбор.set(роли.поля[k], K); yield* поПолям(k + 1); }
  }
  function* поРасширениям(k) {
    if (k === роли.расширения.length) { yield new Map(выбор); return; }
    const { имя, dom, cod } = роли.расширения[k];
    for (const S of расширения) {
      if (S._дом !== выбор.get(dom) || S._код !== выбор.get(cod)) continue;
      выбор.set(имя, S);
      yield* поРасширениям(k + 1);
    }
  }
  yield* поПолям(0);
}

// --- прогон --------------------------------------------------------------------

let проверено = 0;
let сработало = 0;
const пропущено = [];

for (const rule of правила(cat)) {
  const сцена = собратьСцену(rule);
  if (!сцена) { пропущено.push(rule.id); continue; }
  const { g, узлы, атомы, роли } = сцена;
  const вид = new Map();
  for (const имя of роли.поля) вид.set(имя, полеЗн);
  for (const { имя } of роли.расширения) вид.set(имя, расширЗн);

  for (const набор of наборы(роли)) {
    const значения = new Map();
    for (const [имя, зап] of набор) значения.set(узлы.get(имя), вид.get(имя)(зап));
    let целиком = true;
    for (const n of g.nodes) {
      if (значения.has(n.id)) continue;
      const v = вычислитьУзел(g, n.id, значения);
      if (v === null || v === НЕ_СЧИТАЕМ) { целиком = false; break; }
      значения.set(n.id, v);
    }
    if (!целиком) continue;
    const посылки = атомы.slice(0, -1);
    const вывод = атомы[атомы.length - 1];
    if (!посылки.every((a) => значенияАтома(значения, a) === (a.значение !== false))) continue;
    проверено++;
    const v = значенияАтома(значения, вывод);
    if (v === undefined) continue;
    сработало++;
    if (v !== (вывод.значение !== false)) {
      const где = [...набор].map(([имя, зап]) => `${имя} = ${зап.имя}`).join(', ');
      беды.push(`правило «${rule.id}» ложно при ${где}`);
    }
  }
}

console.log(`полей: ${поля.length}, расширений: ${расширения.length}`);
console.log(`посылки сошлись ${проверено} раз, вывод был проверяем ${сработало} раз`);
if (пропущено.length) console.log(`правил вне библиотеки полей (числовые и групповые): ${пропущено.length}`);

const уникальные = [...new Set(беды)];
if (уникальные.length) {
  console.log(`\nрасхождений: ${уникальные.length}`);
  for (const b of уникальные.slice(0, 60)) console.log(`  ${b}`);
  process.exitCode = 1;
} else {
  console.log('\nрасхождений нет: объявленные поля не противоречат ни одному правилу базы');
}
