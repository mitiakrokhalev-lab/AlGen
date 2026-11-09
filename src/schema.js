// Загрузка и проверка файла категории.
//
// Договор об именах: СТРУКТУРНЫЕ ключи латиницей (in, out, requires,
// preserves), ЧЕЛОВЕЧЕСКИЕ — по-русски (имя, фраза, ссылка). Так код не
// спотыкается о кириллицу, а данные читаются глазами.
//
// Отдельно про кириллицу: \w в JavaScript — только латиница, поэтому любая
// регулярка по нашим же данным пишется через \p{L} с флагом u.

import { closeSubsorts, fits, parseSort, свойствоПодходит } from './sorts.js';

// Выражения согласования: "X" — роль, "dom F" — домен терма в роли F.
const RELATIONS = new Set(['dom', 'cod', 'ambient', 'base']);

// Ссылка бывает и в НЕСКОЛЬКО шагов: «base dom F» — кольцо, над которым живёт
// область определения морфизма. Без этого двусортная категория не выражается:
// у подмодуля надо назвать кольцо его объемлющего модуля, а оно за два шага.
export function parseRef(expr) {
  const parts = String(expr).trim().split(/\s+/u);
  const role = parts[parts.length - 1];
  const rels = parts.slice(0, -1);
  for (const r of rels) {
    if (!RELATIONS.has(r)) throw new Error(`не разобрал ссылку «${expr}»`);
  }
  return { rel: rels.length ? rels[0] : null, rels, role };
}

export function loadCategory(raw) {
  const problems = [];
  const cat = {
    id: raw.id,
    имя: raw.имя ?? raw.id,
    sorts: new Map(Object.entries(raw.sorts ?? {})),
    up: closeSubsorts(raw.subsorts ?? []),
    props: new Map(),
    rels: new Map(),
    cons: new Map(),
    degen: raw.degenerations ?? [],
    // СВОЙСТВА ДЛЯ РАЗБОРА СЛУЧАЕВ: по ним вывод вправе разложить задачу на
    // два случая, когда прямого доказательства нет. Список данными, а не
    // кодом: в группах это тривиальность, в кольцах — нулевое кольцо, и знать
    // это может только тот, кто пишет базу. См. `разборСлучаев` в
    // src/generate.js и объяснение там же.
    случаи: raw.разбор_случаев ?? [],
    rules: raw.rules ?? [],
    examples: raw.examples ?? [],
    problems,
  };

  const knownSort = (s) => cat.sorts.has(s);

  for (const p of raw.properties ?? []) {
    if (cat.props.has(p.id)) problems.push(`свойство ${p.id} объявлено дважды`);
    // Сорт свойства бывает списком: «abelian» живёт и на объекте, и на
    // семействе, где значит «каждый член абелев».
    for (const s of Array.isArray(p.sort) ? p.sort : [p.sort]) {
      if (!knownSort(s)) problems.push(`свойство ${p.id}: неизвестный сорт ${s}`);
    }
    cat.props.set(p.id, p);
  }

  for (const c of raw.constructions ?? []) {
    if (cat.cons.has(c.id)) problems.push(`конструкция ${c.id} объявлена дважды`);
    const roles = new Map();
    for (const slot of c.in ?? []) {
      if (roles.has(slot.role)) problems.push(`${c.id}: роль ${slot.role} дважды`);
      roles.set(slot.role, slot);
      if (!knownSort(slot.sort)) {
        problems.push(`${c.id}/${slot.role}: неизвестный сорт ${slot.sort}`);
      }
      for (const req of slot.requires ?? []) {
        const prop = cat.props.get(req);
        if (!prop) problems.push(`${c.id}/${slot.role}: требует неизвестное свойство ${req}`);
        else if (!свойствоПодходит(slot.sort, prop, cat.up)) {
          problems.push(
            `${c.id}/${slot.role}: свойство ${req} живёт на ${prop.sort}, а слот ${slot.sort}`,
          );
        }
      }
      for (const key of ['ambient', 'dom', 'cod', 'base']) {
        if (slot[key] === undefined) continue;
        // Связь ВХОДА бывает и построенным термом, не только ссылкой на роль.
        // Это понадобилось соответствию Галуа: подгруппа H обязана быть
        // подгруппой ИМЕННО gal(K, L, S), а не какой-то другой группы, и
        // выразить это ссылкой на роль нечем — группы Галуа как роли нет.
        // Выход такое умел с самого начала (Int(G) живёт в Aut(G)); вход не
        // умел, и из-за этого «неподвижное поле подгруппы» нельзя было
        // объявить, не теряя согласования сортов.
        if (slot[key] && typeof slot[key] === 'object') {
          const проверить = (expr) => {
            if (expr && typeof expr === 'object') {
              if (!raw.constructions?.some((k) => k.id === expr.op)) {
                problems.push(`${c.id}/${slot.role}: неизвестная конструкция ${expr.op} в ${key}`);
              }
              for (const a of expr.args ?? []) проверить(a);
              return;
            }
            const r = parseRef(expr);
            if (!roles.has(r.role) && r.role !== slot.role) {
              problems.push(`${c.id}/${slot.role}: ${key} ссылается на роль ${r.role} раньше её`);
            }
          };
          проверить(slot[key]);
          continue;
        }
        const ref = parseRef(slot[key]);
        if (!roles.has(ref.role) && ref.role !== slot.role) {
          problems.push(`${c.id}/${slot.role}: ${key} ссылается на роль ${ref.role} раньше её`);
        }
      }
    }
    const out = typeof c.out === 'string' ? { sort: c.out } : c.out;
    if (!out || !knownSort(out.sort)) {
      problems.push(`${c.id}: неизвестный сорт выхода ${out?.sort}`);
    }
    // Выходная связь бывает и построенным термом: Int(G) живёт в Aut(G).
    const checkRef = (expr, где) => {
      if (expr && typeof expr === 'object') {
        if (!raw.constructions?.some((k) => k.id === expr.op)) {
          problems.push(`${где}: неизвестная конструкция ${expr.op}`);
        }
        for (const a of expr.args ?? []) checkRef(a, где);
        return;
      }
      const ref = parseRef(expr);
      if (!roles.has(ref.role)) problems.push(`${где}: ссылка на несуществующую роль ${ref.role}`);
    };
    for (const key of ['ambient', 'dom', 'cod', 'base']) {
      if (out?.[key] === undefined) continue;
      checkRef(out[key], `${c.id}/выход/${key}`);
    }
    cat.cons.set(c.id, { ...c, out, roles });
  }

  for (const d of cat.degen) {
    const c = cat.cons.get(d.op);
    if (!c) {
      problems.push(`вырождение: неизвестная конструкция ${d.op}`);
      continue;
    }
    for (const role of [...Object.keys(d.when ?? {}), ...Object.keys(d.pattern ?? {})]) {
      if (!c.roles.has(role)) problems.push(`вырождение ${d.op}: нет роли ${role}`);
    }
    for (const [role, want] of Object.entries(d.when ?? {})) {
      for (const p of Object.keys(want)) {
        if (!cat.props.has(p)) problems.push(`вырождение ${d.op}/${role}: нет свойства ${p}`);
      }
    }
    for (const [role, pat] of Object.entries(d.pattern ?? {})) {
      if (!cat.cons.has(pat.op)) {
        problems.push(`вырождение ${d.op}/${role}: нет конструкции ${pat.op}`);
      }
    }
    // Образец может захватить аргументы вложенного терма — тогда его имена
    // тоже годятся в результат: «ядро проекции π_N равно N».
    const связанные = new Set(c.roles.keys());
    for (const pat of Object.values(d.pattern ?? {})) {
      for (const имя of pat.bind ?? []) if (имя) связанные.add(имя);
    }
    if (typeof d.equals === 'string') {
      if (!связанные.has(d.equals)) {
        problems.push(`вырождение ${d.op}: результат ${d.equals} не роль и не захват образца`);
      }
    } else if (d.equals && typeof d.equals === 'object') {
      if (!cat.cons.has(d.equals.op)) {
        problems.push(`вырождение ${d.op}: результат — неизвестная конструкция ${d.equals.op}`);
      }
      // Результат вырождения бывает вложенным термом: «произведение всей
      // группы на всю» — это whole-sub(prod(X, Y)), и проверять надо вглубь.
      const проверитьСсылку = (a) => {
        if (a && typeof a === 'object') {
          if (!cat.cons.has(a.op)) {
            problems.push(`вырождение ${d.op}: результат — неизвестная конструкция ${a.op}`);
          }
          for (const x of a.args ?? []) проверитьСсылку(x);
          return;
        }
        const ref = parseRef(a);
        if (!связанные.has(ref.role)) {
          problems.push(`вырождение ${d.op}: результат ссылается на роль ${ref.role}`);
        }
      };
      for (const a of d.equals.args ?? []) проверитьСсылку(a);
    } else {
      problems.push(`вырождение ${d.op}: не указан результат`);
    }
  }

  // Отношения — вторая форма атома наряду со свойством: «H ⩽ N», «G ≅ H».
  // Без них не выражается ни одна задача про включение подгрупп и ни одна
  // задача на изоморфизм, а их в задачнике десятки.
  for (const r of raw.relations ?? []) {
    if (cat.rels.has(r.id)) problems.push(`отношение ${r.id} объявлено дважды`);
    for (const s of r.in ?? []) {
      if (!knownSort(s)) problems.push(`отношение ${r.id}: неизвестный сорт ${s}`);
    }
    if ((r.in ?? []).length !== 2) problems.push(`отношение ${r.id}: ожидались два сорта`);
    if (r.same && !['ambient', 'dom', 'cod', 'base'].includes(r.same)) {
      problems.push(`отношение ${r.id}: непонятное согласование ${r.same}`);
    }
    cat.rels.set(r.id, r);
  }

  for (const s of cat.sorts.keys()) parseSort(s);
  return cat;
}

// ПРАВИЛА ПРОВЕРЯЮТСЯ НА ЯЗЫК. Правило, сославшееся на свойство, которого в
// разделе нет, НЕ срабатывает никогда — и до этой проверки делало это молча.
// Поймано на живом примере: в модули было добавлено правило «полупростое
// кольцо: всякий модуль проективен», а свойства `semisimple-ring` в языке
// модулей нет вовсе (там у кольца всего пять свойств). Загрузчик сказал
// «проблем 0», правило легло в базу и ничего не делало. Такая ошибка хуже
// падения: она выглядит как сделанная работа.
export function проверитьЯзыкПравил(cat) {
  const problems = [];
  for (const r of cat.rules ?? []) {
    const где = `правило «${r.id ?? '(без id)'}»`;
    for (const a of [...(r.if ?? []), r.then]) {
      if (!a) {
        problems.push(`${где}: пустой атом`);
        continue;
      }
      if (a.rel && !cat.rels.has(a.rel)) problems.push(`${где}: нет отношения ${a.rel}`);
      if (a.p && !cat.props.has(a.p)) problems.push(`${где}: нет свойства ${a.p}`);
      if (!a.rel && !a.p) problems.push(`${где}: в атоме не названо ни свойство, ни отношение`);
      // Терм в атоме: конструкция обязана быть известна разделу.
      const термы = a.rel ? (a.args ?? []) : [a.t];
      const проверитьТерм = (t) => {
        if (!t || typeof t === 'string') return;
        if (t.op && !cat.cons.has(t.op)) problems.push(`${где}: нет конструкции ${t.op}`);
        for (const x of t.args ?? []) проверитьТерм(x);
      };
      for (const t of термы) проверитьТерм(t);
    }
  }
  return problems;
}

export function requireClean(cat) {
  if (cat.problems.length) {
    throw new Error(`категория ${cat.id}:\n  ` + cat.problems.join('\n  '));
  }
  return cat;
}

// ПОЧЕМУ ПРОВЕРКА ОТДЕЛЬНОЙ ФУНКЦИЕЙ, А НЕ ВНУТРИ `loadCategory`. Раздел полей
// ссылается в своих правилах на ГРУППОВЫЕ свойства — «группа Галуа циклична»,
// — а приходят они импортом, который делается уже после загрузки (см.
// `category` в src/load.js). Проверка внутри загрузчика объявляла все такие
// правила сломанными: язык ещё не был полон. Это ровно та ошибка порядка, из
// которой и видно, зачем импорт отдельным шагом.
