// Приведение файлов базы к читаемому виду.
//
// Базу заполняет человек, поэтому формат важнее краткости кода: короткие
// массивы и мелкие объекты пишутся в строку, длинные переносятся. Обычный
// JSON.stringify разворачивает каждое имя свойства на отдельную строку и
// превращает файл в 700 строк там, где хватает 300.
//
//   node tools/format-data.mjs            — все файлы в data/
//   node tools/format-data.mjs путь.json  — один файл

import { readFileSync, writeFileSync, readdirSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join, resolve } from 'node:path';

const WIDTH = 116;

const isFlat = (v) =>
  v === null || typeof v !== 'object' || (Array.isArray(v) && v.every((x) => x === null || typeof x !== 'object'));

function inline(value) {
  if (Array.isArray(value)) return `[${value.map((v) => JSON.stringify(v)).join(', ')}]`;
  return `{ ${Object.entries(value)
    .map(([k, v]) => `${JSON.stringify(k)}: ${JSON.stringify(v)}`)
    .join(', ')} }`;
}

function format(value, indent = 0) {
  const pad = ' '.repeat(indent);
  const inner = ' '.repeat(indent + 2);

  if (value === null || typeof value !== 'object') return JSON.stringify(value);

  if (Array.isArray(value)) {
    if (value.length === 0) return '[]';
    if (value.every((v) => v === null || typeof v !== 'object')) {
      const one = inline(value);
      if (indent + one.length <= WIDTH) return one;
      // Массив имён свойств: по нескольку в строке, а не по одному.
      const lines = [];
      let line = '';
      for (const v of value) {
        const piece = JSON.stringify(v);
        if (line && inner.length + line.length + piece.length + 2 > WIDTH) {
          lines.push(inner + line);
          line = '';
        }
        line += (line ? ', ' : '') + piece;
      }
      if (line) lines.push(inner + line);
      return `[\n${lines.join(',\n').replace(/,\n/g, ',\n')}\n${pad}]`;
    }
    return `[\n${value.map((v) => inner + format(v, indent + 2)).join(',\n')}\n${pad}]`;
  }

  const entries = Object.entries(value);
  if (entries.length === 0) return '{}';
  // Теорема целиком в одну строку читается куда лучше, чем развёрнутая на
  // пять, поэтому объект с плоскими значениями (включая короткие массивы)
  // тоже склеивается.
  if (entries.every(([, v]) => isFlat(v))) {
    const one = `{ ${entries.map(([k, v]) => `${JSON.stringify(k)}: ${format(v, 0)}`).join(', ')} }`;
    if (indent + one.length <= WIDTH && !one.includes('\n')) return one;
  }
  const body = entries
    .map(([k, v]) => `${inner}${JSON.stringify(k)}: ${format(v, indent + 2)}`)
    .join(',\n');
  return `{\n${body}\n${pad}}`;
}

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const files = process.argv.slice(2).length
  ? process.argv.slice(2)
  : readdirSync(join(root, 'data'))
      .filter((f) => f.endsWith('.json'))
      .map((f) => join(root, 'data', f));

for (const file of files) {
  const before = readFileSync(file, 'utf8');
  const text = `${format(JSON.parse(before))}\n`;
  // Формат меняет только пробелы: проверяем, что содержимое то же самое.
  const same = JSON.stringify(JSON.parse(before)) === JSON.stringify(JSON.parse(text));
  if (!same) {
    process.stderr.write(`${file}: форматирование изменило содержимое — не записываю\n`);
    process.exitCode = 1;
    continue;
  }
  writeFileSync(file, text, 'utf8');
  process.stdout.write(`${file}: ${before.split('\n').length} → ${text.split('\n').length} строк\n`);
}

// Пустые строки между крупными разделами читать помогают, но JSON их не
// хранит — вставлять их обратно значило бы держать собственный парсер.
// Поэтому файл остаётся плотным: разделы видно по отступу.
