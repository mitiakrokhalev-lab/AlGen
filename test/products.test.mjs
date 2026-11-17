import test from 'node:test';
import assert from 'node:assert/strict';

import { каталогГрупп } from '../src/load.js';
import { синтезПроизведения, свойстваПроизведения, сигнатура } from '../src/model/произведения.js';
import { свойства } from '../src/model/instance.js';
import { подзначение } from '../src/model/named.js';

const каталог = каталогГрупп();
const найти = (id) => каталог.find((x) => x.id === id);

test('синтез утверждает только то, что следует из сомножителей', () => {
  const конечный = {
    abelian: false, solvable: true, 'torsion-free': false, divisible: false,
    periodic: true, 'residually-finite': true, 'fin-gen': true,
  };
  const props = свойстваПроизведения(
    { abelian: true, solvable: true, periodic: false, 'residually-finite': true, 'torsion-free': true },
    конечный,
  );
  assert.equal(props.abelian, false, 'абелевость теряется от неабелева множителя');
  assert.equal(props.solvable, true);
  assert.equal(props['torsion-free'], false, 'конечный нетривиальный множитель вносит кручение');
  assert.equal(props.divisible, false);
  assert.equal(props.finite, false);
  assert.equal(props.periodic, false, 'периодичность решает бесконечный множитель');
  assert.equal(props.nilpotent, undefined,
    'о нильпотентности сомножителей не сказано — и выдумывать её нельзя');
});

test('у двух бесконечных множителей отсутствие кручения СОХРАНЯЕТСЯ', () => {
  // ℤ × ℚ⁺ без кручения. Пока свойство было зашито в «ложь» ради конечного
  // множителя, база и модель расходились: кручение объявлялось вторым
  // множителем, хотя оно нулевое.
  const props = свойстваПроизведения(
    { 'torsion-free': true, abelian: true, divisible: false },
    { 'torsion-free': true, abelian: true, divisible: true },
  );
  assert.equal(props['torsion-free'], true);
  assert.equal(props.divisible, false, 'делимость теряется от неделимого множителя');
  assert.equal(props.abelian, true);
});

test('центр произведения объявляется характеристическим', () => {
  // ℤ × S₃: центр равен ℤ × 1, и он характеристичен. Осторожное «не
  // характеристична» тут было бы ЛОЖЬЮ, а не осторожностью.
  const з = синтезПроизведения(найти('Z'), найти('S3'));
  assert.ok(з, 'ℤ × S₃ обязана синтезироваться');
  assert.equal(з.конструкции.center, 'бесконечный');
  const центр = з.подгруппы.find((п) => п.id === 'бесконечный');
  assert.equal(центр.props.characteristic, true);
  assert.equal(центр.props.central, true);
});

test('синтезированные произведения попали в каталог и связались', () => {
  const син = каталог.filter((x) => x.синтез);
  assert.ok(син.length >= 10, `синтезировано ${син.length}`);
  for (const з of син) {
    assert.equal(з._поПодгруппе.size, 4, `${з.id}: подгрупп должно быть четыре`);
    assert.ok(з._факторы.get('бесконечный'), `${з.id}: фактор по X × 1 должен быть F`);
    assert.ok(з._факторы.get('конечный'), `${з.id}: фактор по 1 × F должен быть X`);
  }
});

test('синтез не добавляет группу со старым набором свойств', () => {
  // Отбор касается только СИНТЕЗИРОВАННЫХ: объявленные рукой оставлены все,
  // потому что у них совпадение свойств не значит совпадения строения —
  // ℚ⁺ и ℝ⁺ различаются факторами, а ⊕ℤ и ℤ^ℕ свободой как модули.
  const объявленные = каталог.filter((x) => x.бесконечная && !x.синтез);
  const занято = new Set(объявленные.map((x) => сигнатура(x.props ?? {})));
  for (const з of каталог.filter((x) => x.синтез)) {
    const s = сигнатура(з.props);
    assert.ok(!занято.has(s), `${з.имя} повторяет набор свойств уже имеющейся группы`);
    занято.add(s);
  }
});

test('произведение бесконечной на конечную стало вычислимым термом', () => {
  const Z = найти('Z');
  assert.ok(Z._произведения.size > 0, 'у ℤ обязаны быть объявленные произведения');
  const все = [...Z._произведения.keys()];
  assert.ok(все.includes('S3'), `есть: ${все.join(',')}`);
});

test('свойства синтезированной группы читаются моделью', () => {
  const з = каталог.find((x) => x.синтез && x.id.endsWith('xS3'));
  assert.ok(з);
  const v = { вид: 'имя', зап: з };
  assert.equal(свойства(v).finite, false);
  assert.equal(свойства(v).abelian, false, 'S₃ не абелева, значит и произведение');
  const конечный = подзначение(з._поПодгруппе.get('конечный'));
  assert.equal(свойства(конечный).normal, true);
  assert.equal(свойства(конечный)['finite-index'], false,
    'у конечного множителя индекс бесконечен — этим он и отличается от второго');
});
