// Починка кодировки математического шрифта в PDF, собранном конвертером,
// который переименовал глифы в мусор.
//
//   node tools/pdf-fix-encoding.mjs вход.pdf выход.pdf
//
// Зачем. В `Downloads/groups.pdf` (задачник СПбГУ) математический шрифт
// объявлен так:
//
//   /Differences [ 11/AB/AC/AD/AE 21/AL … 58/BM/BN/BO/BP/BQ 65/BT/BU… 97/CP… ]
//
// Имена глифов — это base36(код + 360), то есть чистый мусор от конвертера.
// pdftotext про такие имена ничего не знает: «C5» он принимает за
// шестнадцатеричное число и печатает Å, а «CP» тихо выбрасывает. Отсюда
// «Пусть ⟨пусто⟩ группа, À её подгруппа индекса Ò» вместо «Пусть G группа, H
// её подгруппа индекса n».
//
// Коды при этом настоящие и принадлежат кодировке cmmi (TeX math italic):
// 11–33 греческие, 48–57 цифры, 58–62 знаки, 65–90 A–Z, 97–122 a–z. Проверено
// по самому файлу: 58/BM/BN/BO/BP/BQ — это period, comma, less, SLASH, greater,
// и именно поэтому дробь G/N печаталась как «G=N», а запятая — как «;».
//
// Что делает этот скрипт: заменяет мусорные имена на настоящие имена глифов.
// Длина файла при этом меняется, xref устаревает — poppler его перестраивает
// сам. Проверка на месте: после починки в тексте обязаны появиться одиночные
// латинские буквы и дробная черта.

import { readFileSync, writeFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';

// Кодировка cmmi. Таблица выписана целиком: догадка «тут наверняка по
// порядку» в прошлый раз стоила проекту дня.
const CMMI = {};
{
  const put = (from, names) => names.forEach((n, i) => (CMMI[from + i] = n));
  put(0, ['Gamma', 'Delta', 'Theta', 'Lambda', 'Xi', 'Pi', 'Sigma', 'Upsilon', 'Phi', 'Psi', 'Omega']);
  put(11, ['alpha', 'beta', 'gamma', 'delta', 'epsilon', 'zeta', 'eta', 'theta', 'iota', 'kappa',
    'lambda', 'mu', 'nu', 'xi', 'pi', 'rho', 'sigma', 'tau', 'upsilon', 'phi', 'chi', 'psi', 'omega']);
  put(34, ['varepsilon', 'vartheta', 'varpi', 'varrho', 'varsigma', 'varphi']);
  put(40, ['leftharpoonup', 'leftharpoondown', 'rightharpoonup', 'rightharpoondown',
    'lhook', 'rhook', 'triangleright', 'triangleleft']);
  put(48, ['zero', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight', 'nine']);
  put(58, ['period', 'comma', 'less', 'slash', 'greater', 'star', 'partialdiff']);
  for (let c = 65; c <= 90; c++) CMMI[c] = String.fromCharCode(c);
  put(91, ['flat', 'natural', 'sharp', 'slurbelow', 'slurabove', 'lscript']);
  for (let c = 97; c <= 122; c++) CMMI[c] = String.fromCharCode(c);
  put(123, ['dotlessi', 'dotlessj', 'weierstrass', 'vector', 'tie']);
}

// Имена шрифтов AMS, которых нет в списке Adobe и которые pdftotext поэтому
// молча выбрасывает. Слева — как написано в файле, справа — синоним с тем же
// смыслом, который средство знает. Потеря «⩽» дороже всех прочих: в русских
// учебниках это ЗНАК ПОДГРУППЫ, и без него «Пусть H ⩽ G» превращается в
// «Пусть H G» — условие задачи молча исчезает.
const СИНОНИМЫ = {
  lessorequalslant: 'lessequal',
  greaterorequalslant: 'greaterequal',
  propersubset: 'subset',
  reflexsubset: 'subsetequal',
};

const junkName = (n) => /^[0-9A-Z]{2}$/.test(n);

export function fixPdfEncoding(bytes) {
  const s = Buffer.from(bytes).toString('latin1');
  const re = /\/Differences(\s*)\[([^\]]*)\]/g;
  let out = '';
  let last = 0;
  const отчёт = [];
  for (let m = re.exec(s); m; m = re.exec(s)) {
    const names = [...m[2].matchAll(/\/([A-Za-z0-9.]+)/gu)].map((x) => x[1]);
    const мусора = names.filter(junkName).length;
    if (!names.length || мусора / names.length <= 0.8) {
      // Не мусорный массив — но синонимы подставить всё равно надо.
      const заменено = names.filter((n) => СИНОНИМЫ[n]).length;
      if (!заменено) continue;
      const тело = m[2].replace(/\/([A-Za-z0-9.]+)/gu, (t, n) => (СИНОНИМЫ[n] ? `/${СИНОНИМЫ[n]}` : t));
      out += s.slice(last, m.index) + `/Differences${m[1]}[${тело}]`;
      last = m.index + m[0].length;
      отчёт.push({ имён: names.length, мусора: 0, синонимов: заменено });
      continue;
    }

    // Пройти массив, ведя текущий код: числа задают код, имена его увеличивают.
    let code = 0;
    const части = [];
    const токены = m[2].match(/\d+|\/[A-Za-z0-9.]+/gu) ?? [];
    let неизвестных = 0;
    for (const t of токены) {
      if (t[0] !== '/') {
        code = Number(t);
        части.push(String(code));
        continue;
      }
      const имя = CMMI[code];
      if (имя === undefined) {
        неизвестных++;
        части.push(t); // чужое оставляем как есть, а не выдумываем
      } else {
        части.push(`/${имя}`);
      }
      code++;
    }
    out += s.slice(last, m.index) + `/Differences${m[1]}[${части.join(' ')}]`;
    last = m.index + m[0].length;
    отчёт.push({ имён: names.length, мусора, неизвестных, синонимов: 0 });
  }
  out += s.slice(last);
  return { bytes: Buffer.from(out, 'latin1'), отчёт };
}

if (import.meta.url === pathToFileURL(process.argv[1]).href) {
  const [вход, выход] = process.argv.slice(2);
  if (!вход || !выход) {
    console.error('node tools/pdf-fix-encoding.mjs вход.pdf выход.pdf');
    process.exit(2);
  }
  const { bytes, отчёт } = fixPdfEncoding(readFileSync(вход));
  writeFileSync(выход, bytes);
  if (!отчёт.length) {
    console.log('мусорных кодировок не нашлось — файл скопирован без изменений');
  }
  for (const r of отчёт) {
    console.log(`шрифт починен: имён ${r.имён}, мусорных ${r.мусора}, синонимов ${r.синонимов ?? 0}` + (r.неизвестных ? `, не опознано ${r.неизвестных}` : ''));
  }
}
