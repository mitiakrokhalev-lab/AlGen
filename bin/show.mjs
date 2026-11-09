// Смоук-прогон ядра: собрать несколько графов условия руками и показать,
// что с ними делают каноника, вырождения и проверки. Не генератор — проверка,
// что представление вообще работает.

import { category } from '../src/load.js';
import { TermGraph, nameParticipants, render } from '../src/term.js';
import { undefinedSlots, components } from '../src/facts.js';
import { normalize } from '../src/normalize.js';

const cat = category('grp');

function показать(заголовок, построить) {
  const g = new TermGraph(cat);
  const { roots, пояснение } = построить(g);
  const names = nameParticipants(g, roots);
  console.log(`\n── ${заголовок}`);
  if (пояснение) console.log(`   ${пояснение}`);
  for (const r of roots) console.log(`   терм:  ${render(g, r, names)}   [ключ ${g.get(r).key}]`);

  const норм = normalize(g, roots);
  const имена2 = nameParticipants(норм.graph, норм.roots);
  for (const r of норм.roots) console.log(`   норма: ${render(норм.graph, r, имена2)}`);
  for (const a of норм.applied) console.log(`   свернул: ${a.правило.почему}`);

  const дыры = undefinedSlots(g, roots);
  for (const d of дыры) {
    console.log(`   не определено: ${d.op}/${d.роль} требует «${d.свойство}» — ${d.статус}`);
  }
  const куски = components(g, roots);
  if (куски.length > 1) console.log(`   НЕСВЯЗНО: кусков ${куски.length} — это не задача`);
}

показать('фактор по выбранной нормальной подгруппе', (g) => {
  const G = g.given('Grp.obj');
  const N = g.apply('choose-sub', [G], { props: { normal: true } });
  return { roots: [g.apply('quotient', [G, N])] };
});

показать('ядро инъективного гомоморфизма', (g) => {
  const G = g.given('Grp.obj');
  const H = g.given('Grp.obj');
  const f = g.apply('choose-mor', [G, H], { props: { injective: true } });
  return { roots: [g.apply('ker', [f])], пояснение: 'вырождение с условием: свойство известно' };
});

показать('ядро произвольного гомоморфизма', (g) => {
  const G = g.given('Grp.obj');
  const H = g.given('Grp.obj');
  const f = g.apply('choose-mor', [G, H]);
  const k = g.apply('ker', [f]);
  return { roots: [g.apply('quotient', [G, k])], пояснение: 'фактор законен: ядро нормально по построению' };
});

показать('цепочка вырождений у абелевой группы', (g) => {
  const G = g.given('Grp.obj', { abelian: true });
  const c = g.apply('commutator', [G]);
  return { roots: [g.apply('quotient', [G, c]), g.apply('center', [G])] };
});

показать('G/[G,G] у произвольной группы', (g) => {
  const G = g.given('Grp.obj');
  return { roots: [g.apply('quotient', [G, g.apply('commutator', [G])])], пояснение: 'должно узнаться как абелианизация' };
});

показать('амальгама', (g) => {
  const A = g.given('Grp.obj');
  const B = g.given('Grp.obj');
  const C = g.given('Grp.obj');
  const f = g.apply('choose-mor', [A, B], { props: { injective: true } });
  const h = g.apply('choose-mor', [A, C], { props: { injective: true } });
  return { roots: [g.apply('pushout', [f, h])], пояснение: 'одна операция на свободное произведение, склейку и ⊗' };
});

показать('подгруппа кручения неабелевой группы', (g) => {
  const G = g.given('Grp.obj', { abelian: false });
  return { roots: [g.apply('torsion', [G])], пояснение: 'операция частична — это фильтр, а не недоработка' };
});

показать('несвязное условие', (g) => {
  const G = g.given('Grp.obj');
  const H = g.given('Grp.obj', { abelian: true });
  return { roots: [g.apply('center', [G]), g.apply('commutator', [H])] };
});

показать('две подгруппы с одинаковыми требованиями — разные', (g) => {
  const G = g.given('Grp.obj');
  const N = g.apply('choose-sub', [G], { props: { normal: true } });
  const M = g.apply('choose-sub', [G], { props: { normal: true } });
  return { roots: [N, M], пояснение: `ключи различны: ${N !== M}` };
});

показать('канонические морфизмы узнают сами себя', (g) => {
  const G = g.given('Grp.obj');
  const N = g.apply('choose-sub', [G], { props: { normal: true } });
  const π = g.apply('proj', [G, N]);
  const ι = g.apply('incl', [G, N]);
  return {
    roots: [g.apply('ker', [π]), g.apply('im', [ι]), g.apply('ker', [ι])],
    пояснение: 'ядро проекции, образ вложения, ядро вложения',
  };
});

показать('кросс-категорная конструкция', (g) => {
  const R = g.given('Ring.obj', {}, { имя: 'ℤ', named: true });
  return { roots: [g.apply('units', [R])], пояснение: 'сорт входа из другой категории — и всё' };
});

console.log('\nвсё построено без ошибок');
