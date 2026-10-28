import test from 'node:test';
import assert from 'node:assert/strict';

import { category, каталогКолец } from '../src/load.js';
import { построитьСхему } from '../src/scene.js';
import { рассуждать } from '../src/deduce.js';
import { вычислитьУзел } from '../src/model/instance.js';
import { ПОРАЗДЕЛАМ } from '../src/схемы.js';
import { НЕ_СЧИТАЕМ } from '../src/model/значение.js';

const cat = category('ring');
const каталог = каталогКолец();
const по = (id) => каталог.кольца.find((r) => r.id === id);
const мор = (id) => каталог.морфизмы.find((f) => f.id === id);

// Отдельной категории «алгебры» нет намеренно: алгебра над K — это кольцо A со
// структурным морфизмом K → A. Сорт Ring.mor уже есть, библиотека колец готова,
// и заводить вторую категорию значило бы объявить M₂(ℚ) дважды.

test('конечномерная алгебра над полем артинова и нётерова', () => {
  const { g, имена } = построитьСхему(cat, ПОРАЗДЕЛАМ.ring.алгебра, new Map([
    ['K', { field: true }],
    ['f', { 'finite-dim': true }],
  ]));
  const мир = рассуждать(g, [...имена.values()]);
  assert.equal(мир.знает({ p: 'artin-ring', t: имена.get('A') }), true);
  assert.equal(мир.знает({ p: 'noeth-ring', t: имена.get('A') }), true);
});

test('конечномерная алгебра без делителей нуля — тело, и ℍ это подтверждает', () => {
  const { g, имена } = построитьСхему(cat, ПОРАЗДЕЛАМ.ring.алгебра, new Map([
    ['K', { field: true }],
    ['A', { 'no-zero-div': true, 'trivial-ring': false }],
    ['f', { 'finite-dim': true }],
  ]));
  assert.equal(рассуждать(g, [...имена.values()]).знает({ p: 'division', t: имена.get('A') }), true);
  // И в библиотеке такая алгебра есть: ℍ над ℝ, четырёхмерная и не поле.
  assert.equal(мор('R→H').props['finite-dim'], true);
  assert.equal(по('H').props.division, true);
  assert.equal(по('H').props.field, false);
});

test('бесконечномерность спасает ℚ[F₂] от объявления телом', () => {
  // Делителей нуля в ℚ[F₂] нет, и будь она конечномерна, правило объявило бы её
  // телом. Телом она не является — значит в записи обязана стоять
  // бесконечномерность, иначе сверщик поймает противоречие.
  assert.equal(мор('Q→QF2').props['finite-dim'], false);
  assert.equal(по('QF2').props['no-zero-div'], true);
  assert.equal(по('QF2').props.division, false);
});

test('локализация определена только в коммутативном и по простому идеалу', () => {
  // Частичность — это само определение: вне простого идеала дополнение
  // мультипликативно замкнуто, и только тогда дроби образуют кольцо.
  const c = cat.cons.get('localize');
  assert.deepEqual(c.in[0].requires, ['comm']);
  assert.deepEqual(c.in[1].requires, ['prime']);
});

test('локализация ℚ[x] в (x) посчиталась и она локальна', () => {
  const { g, имена } = построитьСхему(cat, ПОРАЗДЕЛАМ.ring.локализация);
  const значения = new Map([
    [имена.get('R'), { вид: 'ркольцо', зап: по('Qx') }],
    [имена.get('I'), { вид: 'идеал', зап: по('Qx').идеалы.find((i) => i.id === 'Qx.x') }],
  ]);
  const L = вычислитьУзел(g, имена.get('L'), значения);
  assert.notEqual(L, НЕ_СЧИТАЕМ);
  assert.equal(L.зап.id, 'Qx_loc');
  assert.equal(L.зап.props.local, true);
  assert.equal(L.зап.props.field, false, 'локализация не поле: (x) остаётся собственным');
});

test('локализация области в нулевом идеале — её поле частных', () => {
  const { g, имена } = построитьСхему(cat, ПОРАЗДЕЛАМ.ring.локализация);
  const значения = new Map([
    [имена.get('R'), { вид: 'ркольцо', зап: по('Z') }],
    [имена.get('I'), { вид: 'идеал', зап: по('Z').идеалы.find((i) => i.id === 'Z.0') }],
  ]);
  const L = вычислитьУзел(g, имена.get('L'), значения);
  assert.equal(L.зап.id, 'Q', 'ℤ в нулевом идеале даёт ℚ');
});
