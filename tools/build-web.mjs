// Сборка страницы в ОДИН файл: AlGen.html.
//
//   node tools/build-web.mjs
//
// Почему один файл и без сборщика: страница должна открываться двойным щелчком
// с диска, без сервера и без сети. Поэтому модули движка склеиваются в один
// <script type="module">, а база вписывается прямо в него.
//
// Склейка честная, но грубая: у ESM-модулей снимаются import/export и они
// кладутся в порядке зависимостей. Значит два модуля не имеют права объявить
// одно имя на верхнем уровне — сборщик это ПРОВЕРЯЕТ и падает, а не выдаёт
// файл, который сломается у человека.

import { readFileSync, writeFileSync, existsSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const корень = join(dirname(fileURLToPath(import.meta.url)), '..');

// Порядок — это порядок зависимостей; он задан руками, потому что их девять.
const МОДУЛИ = [
  'sorts.js', 'schema.js', 'импорт.js', 'term.js', 'facts.js',
  'normalize.js', 'deduce.js', 'statement.js', 'stop.js', 'scene.js',
  'model/значение.js', 'model/group.js', 'model/catalogue.js', 'model/произведения.js',
  'model/top.js', 'model/topinst.js',
  'model/презентация.js', 'model/синтез-свободных.js', 'model/named.js', 'model/modules.js',
  'model/произведения-колец.js', 'model/ringinst.js', 'model/fldinst.js', 'model/instance.js',
  'witness.js', 'мера-пробела.js', 'generate.js',
  // Схемы — ОДИН источник на движок и на страницу. Прежде страница несла свои
  // копии (`ЗАГОТОВКИ_*`), наборы расходились молча, и это стояло отдельным
  // долгом в плане: в командной строке схем было больше, чем на странице, и
  // всякая новая схема («башня» у полей, «длина» у модулей) про страницу
  // забывала.
  'схемы.js',
];

// `function*` — тоже объявление: на генераторе `привязки` склейка и споткнулась.
const ИМЯ_ВЕРХНЕГО =
  /^(?:export\s+)?(?:async\s+)?(?:function\s*\*?|class|const|let|var)\s+([\p{L}_$][\p{L}\p{N}_$]*)/gmu;

function снять(код, файл) {
  // Переименование при импорте («known as defaultKnown») при склейке теряется
  // МОЛЧА: имя просто перестаёт существовать, а падает это лишь в тот момент,
  // когда до него дойдёт исполнение. Поэтому такие пары превращаются в
  // обычное присваивание, а не выбрасываются.
  const псевдонимы = [];
  const без = код
    // Список имён бывает и в несколько строк — поэтому [\s\S], а не [^}].
    .replace(/^import\s*\{([\s\S]*?)\}\s*from\s*['"][^'"]*['"];?[ \t]*$/gmu, (_, список) => {
      for (const кусок of список.split(',')) {
        const m = /^\s*([\p{L}_$][\p{L}\p{N}_$]*)\s+as\s+([\p{L}_$][\p{L}\p{N}_$]*)\s*$/u.exec(кусок);
        if (m) псевдонимы.push(`const ${m[2]} = ${m[1]};`);
      }
      return '';
    })
    .replace(/^import\s[^;]*;[ \t]*$/gmu, '')
    .replace(/^export\s*\{[^}]*\};?[ \t]*$/gmu, '')
    .replace(/^export\s+(?=(?:async\s+)?(?:function\s*\*?|class|const|let|var)\s)/gmu, '');
  if (/^\s*(import|export)\s/mu.test(без)) {
    throw new Error(`${файл}: остался import/export — склейка не умеет такую форму`);
  }
  return псевдонимы.length ? `${псевдонимы.join('\n')}\n${без}` : без;
}

const части = [];
const объявлено = new Map();

for (const файл of МОДУЛИ) {
  const код = снять(readFileSync(join(корень, 'src', файл), 'utf8'), файл);
  for (const m of код.matchAll(ИМЯ_ВЕРХНЕГО)) {
    const имя = m[1];
    // Считаем только объявления на нулевом отступе — это верхний уровень.
    const начало = код.lastIndexOf('\n', m.index) + 1;
    if (код.slice(начало, m.index).trim() !== '') continue;
    if (объявлено.has(имя)) {
      throw new Error(`имя «${имя}» объявлено и в ${объявлено.get(имя)}, и в ${файл}`);
    }
    объявлено.set(имя, файл);
  }
  части.push(`// ===== src/${файл} =====\n${код.trim()}\n`);
}

const база = JSON.parse(readFileSync(join(корень, 'data', 'grp.json'), 'utf8'));
const модули = JSON.parse(readFileSync(join(корень, 'data', 'mod.json'), 'utf8'));
const кольца = JSON.parse(readFileSync(join(корень, 'data', 'rings.json'), 'utf8'));
const группы = JSON.parse(readFileSync(join(корень, 'data', 'groups.json'), 'utf8'));
const бесконечные = JSON.parse(readFileSync(join(корень, 'data', 'infinite.json'), 'utf8'));
const топология = JSON.parse(readFileSync(join(корень, 'data', 'top.json'), 'utf8'));
const базаКолец = JSON.parse(readFileSync(join(корень, 'data', 'ring.json'), 'utf8'));
const библиотекаКолец = JSON.parse(readFileSync(join(корень, 'data', 'ring-lib.json'), 'utf8'));
const базаПолей = JSON.parse(readFileSync(join(корень, 'data', 'fld.json'), 'utf8'));
const библиотекаПолей = JSON.parse(readFileSync(join(корень, 'data', 'fld-lib.json'), 'utf8'));
const пространства = JSON.parse(readFileSync(join(корень, 'data', 'top-infinite.json'), 'utf8'));
// Перенесённое из старого Генератора — отдельный файл, но на странице
// библиотека обязана быть та же, что в командной строке.
const извне = join(корень, 'data', 'top-pibase.json');
const перенос = existsSync(извне) ? JSON.parse(readFileSync(извне, 'utf8')).объекты : [];
const данные = `// ===== база =====\nconst ДАННЫЕ = ${JSON.stringify({
  grp: база,
  mod: модули,
  кольца: кольца.кольца,
  группы: группы.группы,
  бесконечные: бесконечные.объекты,
  семейства: бесконечные.семейства ?? [],
  свободные: бесконечные.свободные ?? [],
  top: топология,
  ring: базаКолец,
  кольцаБиб: библиотекаКолец,
  fld: базаПолей,
  поляБиб: библиотекаПолей,
  пространства: [...пространства.объекты, ...перенос],
})};\n`;
const страница = readFileSync(join(корень, 'web', 'страница.js'), 'utf8');

const бандл = [данные, ...части, `// ===== web/страница.js =====\n${страница}`].join('\n');

// Разбор — это мало. Склейка ломается не синтаксисом, а потерянным именем, и
// узнаётся это только в тот миг, когда до имени дойдёт исполнение. Поэтому
// собранный движок ЗАПУСКАЕТСЯ прямо здесь: грузим базу, строим граф,
// сворачиваем вырождения, прогоняем крошечный перебор.
await прогнать(данные + части.join('\n'));

async function прогнать(движок) {
  let наружу;
  try {
    // eslint-disable-next-line no-new-func
    наружу = new Function(
      `${движок}\nreturn { ДАННЫЕ, loadCategory, requireClean, импортироватьСорта, проверитьЯзыкПравил, TermGraph, normalize, генерировать,`
      + ` построитьСхему, группаПоИмени, связать };`,
    )();
  } catch (e) {
    throw new Error(`собранный движок не разбирается: ${e.message}`);
  }
  const cat = наружу.requireClean(наружу.loadCategory(наружу.ДАННЫЕ.grp));
  const g = new наружу.TermGraph(cat);
  const G = g.given('Grp.obj', { abelian: true });
  const свёрнут = наружу.normalize(g, [g.apply('center', [G])]);
  if (!свёрнут.applied.length) throw new Error('склейка: вырождения не сработали');
  // Библиотека собирается тем же кодом, что на странице, и обязана опровергать.
  const конечные = наружу.ДАННЫЕ.группы
    .map((z) => наружу.группаПоИмени(z.id, наружу.ДАННЫЕ.группы))
    .sort((a, b) => a.n - b.n);
  const { беды } = наружу.связать(наружу.ДАННЫЕ.бесконечные, конечные,
    наружу.ДАННЫЕ.семейства ?? [], [], наружу.ДАННЫЕ.свободные ?? []);
  if (беды.length) throw new Error('склейка: бесконечные группы не связались: ' + беды[0]);
  const каталог = [...конечные, ...наружу.ДАННЫЕ.бесконечные];
  const итог = await наружу.генерировать({
    cat,
    схема: {
      узлы: [
        { имя: 'A', op: 'given', sort: 'Grp.obj' },
        { имя: 'B', op: 'given', sort: 'Grp.obj' },
        { имя: 'P', op: 'prod', args: ['A', 'B'] },
      ],
    },
    границы: { объект: 1 },
    достройка: 1,
    каталог,
    примеров: 400,
  });
  if (!итог.баланс) throw new Error('склейка: баланс корзин не сошёлся');
  if (!итог.найдено.length) throw new Error('склейка: перебор ничего не нашёл');
  if (!итог.счёт['опровергается примером']) throw new Error('склейка: библиотека не опровергает');
  if (итог.противоречия.length) throw new Error('склейка: база спорит с моделью');
  console.log(
    `прогон собранного движка: задач ${итог.найдено.length}, `
    + `опровергнуто примером ${итог.счёт['опровергается примером']}, баланс сошёлся`,
  );
}

const html = readFileSync(join(корень, 'web', 'страница.html'), 'utf8');
if (!html.includes('/*СКРИПТ*/')) throw new Error('в странице нет места для скрипта');
const готово = html.replace('/*СКРИПТ*/', () => бандл);

const куда = join(корень, 'AlGen.html');
writeFileSync(куда, готово);
console.log(
  `AlGen.html: ${(готово.length / 1024).toFixed(0)} КБ ` +
  `(движок ${(части.join('').length / 1024).toFixed(0)} КБ, база ${(данные.length / 1024).toFixed(0)} КБ)`,
);
console.log(`имён на верхнем уровне: ${объявлено.size}`);
