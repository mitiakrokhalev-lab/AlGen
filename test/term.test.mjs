import test from 'node:test';
import assert from 'node:assert/strict';

import { category } from '../src/load.js';
import { TermGraph, nameParticipants, render } from '../src/term.js';
import { known, undefinedSlots, components } from '../src/facts.js';
import { normalize } from '../src/normalize.js';

const cat = category('grp');
const строка = (g, id) => render(g, id, nameParticipants(g, [id]));

test('файл категории грузится без замечаний', () => {
  assert.equal(cat.problems.length, 0);
  assert.ok(cat.cons.has('quotient'));
  assert.ok(cat.props.has('normal'));
});

test('подсорта: свойство объекта применимо к подгруппе', () => {
  const g = new TermGraph(cat);
  const G = g.given('Grp.obj');
  const Z = g.apply('center', [G]);
  // center объявлен на Grp.sub, но abelian живёт на Grp.obj — подсорт пускает.
  assert.equal(known(g, Z, 'abelian'), true);
  assert.equal(known(g, Z, 'normal'), true);
});

test('сорт аргумента проверяется', () => {
  const g = new TermGraph(cat);
  const G = g.given('Grp.obj');
  // группа не годится туда, где ждут морфизм
  assert.throws(() => g.apply('ker', [G]), /ждал Grp\.mor/u);
});

test('согласование: подгруппа обязана быть подгруппой ИМЕННО этой группы', () => {
  const g = new TermGraph(cat);
  const G = g.given('Grp.obj');
  const H = g.given('Grp.obj');
  const N = g.apply('choose-sub', [H], { props: { normal: true } });
  assert.throws(() => g.apply('quotient', [G, N]), /ambient/u);
});

test('согласование пуллбэка: общий кодомен', () => {
  const g = new TermGraph(cat);
  const A = g.given('Grp.obj');
  const B = g.given('Grp.obj');
  const C = g.given('Grp.obj');
  const f = g.apply('choose-mor', [A, C]);
  const плохой = g.apply('choose-mor', [B, A]);
  assert.throws(() => g.apply('pullback', [f, плохой]), /cod/u);
  const хороший = g.apply('choose-mor', [B, C]);
  assert.ok(Number.isInteger(g.apply('pullback', [f, хороший])));
});

test('детерминированные конструкции схлопываются, выбор — нет', () => {
  const g = new TermGraph(cat);
  const G = g.given('Grp.obj');
  assert.equal(g.apply('center', [G]), g.apply('center', [G]));
  const N = g.apply('choose-sub', [G], { props: { normal: true } });
  const M = g.apply('choose-sub', [G], { props: { normal: true } });
  assert.notEqual(N, M);
});

test('коммутативная операция не различает порядок аргументов', () => {
  const g = new TermGraph(cat);
  const G = g.given('Grp.obj');
  const N = g.apply('choose-sub', [G]);
  const M = g.apply('choose-sub', [G]);
  // Пересечение подгрупп коммутативно ПО-НАСТОЯЩЕМУ: N ∩ M и M ∩ N — одно и
  // то же множество, а не изоморфные копии.
  assert.equal(g.apply('meet', [G, N, M]), g.apply('meet', [G, M, N]));
});

test('произведение НЕ коммутативно как терм', () => {
  const g = new TermGraph(cat);
  const G = g.given('Grp.obj');
  const H = g.given('Grp.obj');
  // A × B и B × A изоморфны, но это разные термы: у произведения есть порядок
  // сомножителей, и без него не записать координатную подгруппу N × M.
  assert.notEqual(g.apply('prod', [G, H]), g.apply('prod', [H, G]));
  const N = g.apply('choose-sub', [G]);
  const M = g.apply('choose-sub', [H]);
  const S = g.apply('prod-sub', [G, H, N, M]);
  assert.equal(g.rel(S, 'ambient'), g.apply('prod', [G, H]),
    'подгруппа-произведение обязана жить в ТОМ САМОМ произведении');
});

test('вырождение с условием применяется только когда условие известно', () => {
  const дано = (props) => {
    const g = new TermGraph(cat);
    const G = g.given('Grp.obj');
    const H = g.given('Grp.obj');
    const f = g.apply('choose-mor', [G, H], { props });
    const k = g.apply('ker', [f]);
    const n = normalize(g, [k]);
    return строка(n.graph, n.roots[0]);
  };
  assert.equal(дано({ injective: true }), '1');
  assert.equal(дано({}), 'ker φ');
  assert.equal(дано({ injective: false }), 'ker φ');
});

test('цепочка вырождений у абелевой группы доходит до конца', () => {
  const g = new TermGraph(cat);
  const G = g.given('Grp.obj', { abelian: true });
  const q = g.apply('quotient', [G, g.apply('commutator', [G])]);
  const n = normalize(g, [q, g.apply('center', [G])]);
  assert.equal(строка(n.graph, n.roots[0]), 'G');
  assert.equal(строка(n.graph, n.roots[1]), 'G');
  assert.ok(n.applied.length >= 3);
});

test('G/[G,G] узнаётся как абелианизация', () => {
  const g = new TermGraph(cat);
  const G = g.given('Grp.obj');
  const q = g.apply('quotient', [G, g.apply('commutator', [G])]);
  const n = normalize(g, [q]);
  assert.equal(строка(n.graph, n.roots[0]), 'G^ab');
});

test('частичность операции видна как «не определено», а не как ошибка', () => {
  const g = new TermGraph(cat);
  const G = g.given('Grp.obj', { abelian: false });
  const t = g.apply('torsion', [G]);
  const дыры = undefinedSlots(g, [t]);
  assert.equal(дыры.length, 1);
  assert.equal(дыры[0].свойство, 'abelian');
  assert.equal(дыры[0].статус, 'нет');
});

test('«не знаем» и «знаем, что нет» различаются', () => {
  const g = new TermGraph(cat);
  const G = g.given('Grp.obj');
  const N = g.apply('choose-sub', [G]);
  const q = g.apply('quotient', [G, N]);
  assert.equal(undefinedSlots(g, [q])[0].статус, 'неизвестно');
  assert.equal(known(g, N, 'normal'), undefined);
});

test('ядро нормально по построению, поэтому фактор по нему определён', () => {
  const g = new TermGraph(cat);
  const G = g.given('Grp.obj');
  const H = g.given('Grp.obj');
  const k = g.apply('ker', [g.apply('choose-mor', [G, H])]);
  const q = g.apply('quotient', [G, k]);
  assert.deepEqual(undefinedSlots(g, [q]), []);
});

test('связность условия считается по аргументам конструкций', () => {
  const g = new TermGraph(cat);
  const G = g.given('Grp.obj');
  const H = g.given('Grp.obj');
  assert.equal(components(g, [g.apply('center', [G]), g.apply('commutator', [H])]).length, 2);
  assert.equal(components(g, [g.apply('prod', [G, H])]).length, 1);
});

test('кросс-категорная конструкция берёт сорт из другой категории', () => {
  const g = new TermGraph(cat);
  const R = g.given('Ring.obj', {}, { имя: 'ℤ', named: true });
  const U = g.apply('units', [R]);
  assert.equal(строка(g, U), 'ℤ^×');
  assert.equal(g.get(U).sort, 'Grp.obj');
});

test('печать сложного терма расставляет скобки по приоритету', () => {
  const g = new TermGraph(cat);
  const G = g.given('Grp.obj');
  const H = g.given('Grp.obj');
  const p = g.apply('prod', [G, H]);
  const q = g.apply('quotient', [p, g.apply('commutator', [p])]);
  assert.equal(строка(g, q), '(G × H)/[G × H, G × H]');
});

test('амальгама печатается через свои концы, а не через морфизмы', () => {
  const g = new TermGraph(cat);
  const A = g.given('Grp.obj');
  const B = g.given('Grp.obj');
  const C = g.given('Grp.obj');
  const f = g.apply('choose-mor', [A, B], { props: { injective: true } });
  const h = g.apply('choose-mor', [A, C], { props: { injective: true } });
  assert.equal(строка(g, g.apply('pushout', [f, h])), 'H ∗_G K');
});

test('свойства на детерминированном узле — НАВЯЗАННЫЕ, а не часть личности', () => {
  // Договор изменился ради числового слоя: «(G : N) равно 2» — это посылка
  // условия про построенный терм, а не свойство самого терма. В ключ такие
  // свойства не идут, иначе два одинаковых терма с разными посылками стали бы
  // разными термами и схлопывание по ключу потеряло бы смысл.
  const g = new TermGraph(cat);
  const G = g.given('Grp.obj');
  const Z = g.apply('center', [G], { props: { abelian: true } });
  assert.deepEqual(g.get(Z).props, {}, 'собственных свойств у построенного терма нет');
  assert.deepEqual(g.get(Z).навязано, { abelian: true });
  // Тот же терм без посылок обязан быть ТЕМ ЖЕ узлом.
  assert.equal(g.apply('center', [G]), Z);
  // А посылки, навешенные дважды, объединяются на одном узле.
  g.apply('center', [G], { props: { trivial: false } });
  assert.deepEqual(g.get(Z).навязано, { abelian: true, trivial: false });
});

// --- ключ вопроса -------------------------------------------------------------
//
// Чем задача опознаётся для читателя. Ключ терма для этого не годится прямо: у
// выбирающего узла в него входят навешанные свойства, и «N нормальна ⇒ G/N
// абелева» выглядело бы другим вопросом, чем «N нормальна и максимальна ⇒ …».

test('ключ вопроса не замечает свойств на выборе, но различает сами выборы', async () => {
  const { построитьСхему, ключВопроса, канонТерма } = await import('../src/scene.js');
  const схема = {
    узлы: [
      { имя: 'G', op: 'given', sort: 'Grp.obj' },
      { имя: 'N', op: 'choose-sub', args: ['G'], props: { normal: true } },
      { имя: 'Q', op: 'quotient', args: ['G', 'N'] },
    ],
  };
  const цель = { p: 'abelian', узел: 'Q', значение: true };
  const ключ = (свойства) => {
    const { g, имена } = построитьСхему(cat, схема, new Map(свойства));
    return ключВопроса(g, имена, цель);
  };
  const пусто = ключ([]);
  const сМаксимальностью = ключ([['N', { maximal: true }]]);
  const сКонечностью = ключ([['G', { finite: true }]]);
  assert.equal(пусто, сМаксимальностью,
    'посылка на выборе нового вопроса не делает: вопрос тот же, условие сильнее');
  assert.equal(пусто, сКонечностью, 'посылка на данных — тем более');
  assert.ok(!/[{}]/.test(пусто), `в ключе остались свойства: ${пусто}`);

  // А вот ДВА РАЗНЫХ выбора склеиваться не должны: иначе «N ∩ M тривиально»
  // стало бы «N ∩ N тривиально».
  const двойная = {
    узлы: [
      { имя: 'G', op: 'given', sort: 'Grp.obj' },
      { имя: 'N', op: 'choose-sub', args: ['G'] },
      { имя: 'M', op: 'choose-sub', args: ['G'] },
    ],
  };
  const { g, имена } = построитьСхему(cat, двойная);
  assert.notEqual(канонТерма(g, имена.get('N')), канонТерма(g, имена.get('M')),
    'два выбора — две личности, и номер выбора обязан остаться в ключе');
});

test('ключ вопроса не зависит от посылок — сцену хватит построить один раз', async () => {
  const { построитьСхему, ключВопроса } = await import('../src/scene.js');
  const схема = {
    узлы: [
      { имя: 'G', op: 'given', sort: 'Grp.obj' },
      { имя: 'Z', op: 'center', args: ['G'] },
    ],
  };
  const ключ = (свойства, узел) => {
    const { g, имена } = построитьСхему(cat, схема, new Map(свойства));
    return ключВопроса(g, имена, { p: 'cyclic', узел, значение: true });
  };
  // Вырождений ключ НЕ знает: `построитьСхему` их не делает, это работа
  // normalize. Поэтому «Z(G) циклична» у абелевой G остаётся отдельным
  // вопросом — и выкидывают такое условие раньше, как вырожденное.
  assert.equal(ключ([['G', { abelian: true }]], 'Z'), ключ([], 'Z'),
    'ключ обязан быть один и тот же при любых посылках');
  assert.notEqual(ключ([], 'Z'), ключ([], 'G'), 'а про разные термы — разный');
});
