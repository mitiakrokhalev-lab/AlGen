// Крошечный статический сервер — только чтобы смотреть страницу в браузере.
// Для работы страница в нём не нуждается: AlGen.html открывается с диска.
//
//   node tools/serve.mjs [порт]

import { createServer } from 'node:http';
import { readFileSync, existsSync, statSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join, extname, normalize } from 'node:path';

const корень = join(dirname(fileURLToPath(import.meta.url)), '..');
const порт = Number(process.argv[2] ?? 8123);

const ТИПЫ = {
  '.html': 'text/html; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  '.json': 'application/json; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.txt': 'text/plain; charset=utf-8',
};

createServer((req, res) => {
  let путь = decodeURIComponent((req.url ?? '/').split('?')[0]);
  if (путь === '/') путь = '/AlGen.html';
  const файл = join(корень, normalize(путь).replace(/^(\.\.[/\\])+/u, ''));
  if (!файл.startsWith(корень) || !existsSync(файл) || statSync(файл).isDirectory()) {
    res.writeHead(404, { 'content-type': 'text/plain; charset=utf-8' });
    res.end('нет такого файла');
    return;
  }
  res.writeHead(200, { 'content-type': ТИПЫ[extname(файл)] ?? 'application/octet-stream' });
  res.end(readFileSync(файл));
}).listen(порт, () => console.log(`http://localhost:${порт}/`));
