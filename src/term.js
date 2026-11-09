// Граф термов условия.
//
// Условие задачи — это DAG: в листьях вводящие узлы («пусть G — группа»,
// «ℤ»), выше конструкции. Узел, у которого есть выбор (подгруппа со
// свойствами, морфизм со свойствами), — отдельная личность: две подгруппы с
// одинаковыми требованиями это ДВЕ подгруппы, поэтому такие узлы не
// схлопываются. Детерминированные конструкции (фактор, ядро, центр) наоборот
// схлопываются по ключу — без этого одна задача выдаётся пересказами.

import { fits } from './sorts.js';
import { parseRef } from './schema.js';

// Позиции слотов, которые между собой переставимы. `commutative: true` —
// все; `commutative: ["N","M"]` — только названные.
export function commutingPositions(c) {
  const com = c?.commutative;
  if (!com) return [];
  const slots = c.in ?? [];
  if (com === true) return slots.map((_, i) => i);
  return slots.map((s, i) => (com.includes(s.role) ? i : -1)).filter((i) => i >= 0);
}

export function commutingRoles(c) {
  const slots = c?.in ?? [];
  return commutingPositions(c).map((i) => slots[i].role);
}

export class TermGraph {
  constructor(cat) {
    this.cat = cat;
    this.nodes = [];
    this.byKey = new Map();
    this.serial = 0;
  }

  get(id) {
    const n = this.nodes[id];
    if (!n) throw new Error(`нет узла ${id}`);
    return n;
  }

  // Вводящий узел: «пусть G — группа со свойствами …» либо конкретный объект.
  given(sort, props = {}, opts = {}) {
    return this.#push({
      op: opts.named ? 'named' : 'given',
      args: [],
      sort,
      props: { ...props },
      имя: opts.имя ?? null,
      объект: opts.объект ?? opts.имя ?? null,
      схемИмя: opts.схемИмя ?? null,
      rels: opts.rels ?? {},
      key: opts.named ? `@${opts.объект ?? opts.имя}` : `given#${this.serial++}`,
    });
  }

  // Узел-конструкция. props осмысленны только у выбирающих конструкций.
  apply(opId, args, opts = {}) {
    const c = this.cat.cons.get(opId);
    if (!c) throw new Error(`нет конструкции ${opId}`);
    const slots = c.in ?? [];
    if (args.length !== slots.length) {
      throw new Error(`${opId}: ждал ${slots.length} аргументов, дали ${args.length}`);
    }
    const bound = new Map();
    for (let i = 0; i < slots.length; i++) {
      const slot = slots[i];
      const arg = this.get(args[i]);
      if (!fits(arg.sort, slot.sort, this.cat.up)) {
        throw new Error(`${opId}/${slot.role}: ждал ${slot.sort}, дали ${arg.sort}`);
      }
      bound.set(slot.role, args[i]);
      for (const key of ['ambient', 'dom', 'cod', 'base']) {
        if (slot[key] === undefined) continue;
        const want = this.#resolveRef(slot[key], bound);
        const have = this.rel(args[i], key);
        if (want !== have) {
          throw new Error(
            `${opId}/${slot.role}: ${key} должен совпасть с ${slot[key]}` +
              ` (у аргумента ${have === null ? 'его нет' : have}, ждали ${want})`,
          );
        }
      }
    }

    const props = { ...(opts.props ?? {}) };
    // Коммутативность объявляется списком ролей: у пересечения подгрупп
    // переставимы N и M, но не объемлющая группа X.
    const keyArgs = args.map((a) => this.get(a).key);
    const idx = commutingPositions(c);
    if (idx.length > 1) {
      const vals = idx.map((i) => keyArgs[i]).sort();
      idx.forEach((i, k) => (keyArgs[i] = vals[k]));
    }
    let key = `${opId}(${keyArgs.join(',')})`;
    if (c.choice) {
      // Выбор — личность, а не значение.
      const tag = Object.keys(props).sort().map((k) => (props[k] ? k : `!${k}`)).join('&');
      key = `${key}{${tag}}#${this.serial++}`;
    }

    const hit = this.byKey.get(key);
    if (hit !== undefined) {
      // Тот же терм встретился дважды: навязанные посылки объединяются.
      if (!c.choice && Object.keys(props).length) {
        const узел = this.get(hit);
        узел.навязано = { ...(узел.навязано ?? {}), ...props };
      }
      return hit;
    }
    return this.#push({
      op: opId,
      args: [...args],
      sort: c.out.sort,
      // Собственные свойства бывают только у ВЫБИРАЮЩЕГО узла: «возьмём
      // нормальную подгруппу» — часть его личности. У построенного терма
      // свойства не собственные, а навязанные условием (ниже).
      props: c.choice ? props : {},
      // По умолчанию ВСЕОБЩНОСТЬ: «пусть N — подгруппа G» в математической
      // речи значит «для всякой», и ровно так же рассуждает вывод и ищет
      // контрпример перебор. Существование надо просить явно.
      // Свойства на детерминированном узле — НАВЯЗАННЫЕ: «(G : N) равно 2»
      // это посылка условия, а не часть личности терма. В ключ они не идут,
      // иначе два одинаковых терма с разными посылками стали бы разными
      // термами, и схлопывание по ключу потеряло бы смысл.
      навязано: c.choice ? null : (Object.keys(props).length ? { ...props } : null),
      quant: opts.quant ?? (c.choice ? 'forall' : null),
      имя: null,
      схемИмя: opts.схемИмя ?? null,
      rels: {},
      key,
    });
  }

  // Есть ли уже такой терм. Вывод пользуется этим, чтобы не СТРОИТЬ термы:
  // рассуждаем о том, что в условии есть, иначе мир растёт без края.
  find(opId, args) {
    const c = this.cat.cons.get(opId);
    if (!c || c.choice) return null;
    const keyArgs = args.map((a) => this.get(a).key);
    const idx = commutingPositions(c);
    if (idx.length > 1) {
      const vals = idx.map((i) => keyArgs[i]).sort();
      idx.forEach((i, k) => (keyArgs[i] = vals[k]));
    }
    const hit = this.byKey.get(`${opId}(${keyArgs.join(',')})`);
    return hit === undefined ? null : hit;
  }

  // Согласующая связь узла: ambient подгруппы, dom и cod морфизма, base модуля.
  rel(id, name) {
    const n = this.get(id);
    if (n.rels && n.rels[name] !== undefined) return n.rels[name];
    const c = this.cat.cons.get(n.op);
    if (!c || c.out[name] === undefined) return null;
    const bound = new Map();
    (c.in ?? []).forEach((slot, i) => bound.set(slot.role, n.args[i]));
    return this.#resolveRef(c.out[name], bound);
  }

  // «X» — узел в роли X, «dom F» — домен узла в роли F,
  // { op, args } — построенный терм (Int(G) живёт в Aut(G), а не в роли).
  resolve(expr, bound) {
    if (expr && typeof expr === 'object') {
      return this.apply(expr.op, (expr.args ?? []).map((a) => this.resolve(a, bound)));
    }
    const ref = parseRef(expr);
    let target = bound.get(ref.role);
    if (target === undefined) throw new Error(`ссылка на несвязанную роль ${ref.role}`);
    // Шаги применяются справа налево: «base dom F» это base(dom(F)).
    for (const r of [...(ref.rels ?? [])].reverse()) {
      if (target === null || target === undefined) return null;
      target = this.rel(target, r);
    }
    return target;
  }

  #resolveRef(expr, bound) {
    return this.resolve(expr, bound);
  }

  // Роль → узел для конструкции данного узла.
  binding(id) {
    const n = this.get(id);
    const c = this.cat.cons.get(n.op);
    const bound = new Map();
    (c?.in ?? []).forEach((slot, i) => bound.set(slot.role, n.args[i]));
    return bound;
  }

  #push(node) {
    node.id = this.nodes.length;
    this.nodes.push(node);
    this.byKey.set(node.key, node.id);
    return node.id;
  }

  // Узлы, от которых зависит терм (включая его самого), в порядке снизу вверх.
  support(id, seen = new Set()) {
    if (seen.has(id)) return seen;
    for (const a of this.get(id).args) this.support(a, seen);
    seen.add(id);
    return seen;
  }
}

// Имена участников для печати. Буквы берутся из объявления сорта; когда
// пул кончился, идут индексы — молча обрезать нельзя.
export function nameParticipants(graph, roots) {
  const used = new Map();
  const names = new Map();
  const all = new Set();
  for (const r of roots) for (const id of graph.support(r)) all.add(id);
  for (const id of [...all].sort((a, b) => a - b)) {
    const n = graph.get(id);
    if (n.имя) {
      names.set(id, n.имя);
      continue;
    }
    if (n.op !== 'given' && !(graph.cat.cons.get(n.op)?.choice)) continue;
    // Имя вершины СХЕМЫ — это имя, которое дал человек, и условие обязано
    // звать её так же, как рисунок и контрпример. Иначе человек рисует A, а
    // читает «пусть G», и сопоставить контрпример с условием не может.
    if (n.схемИмя) {
      names.set(id, n.схемИмя);
      continue;
    }
    const pool = graph.cat.sorts.get(n.sort)?.буквы ?? ['t'];
    const k = used.get(n.sort) ?? 0;
    used.set(n.sort, k + 1);
    names.set(id, k < pool.length ? pool[k] : `${pool[pool.length - 1]}${k - pool.length + 2}`);
  }
  return names;
}

export function render(graph, id, names, prec = 0) {
  const n = graph.get(id);
  if (names.has(id)) return names.get(id);
  const c = graph.cat.cons.get(n.op);
  if (!c) return n.имя ?? `?${id}`;
  const my = c.prec ?? 100;
  const bound = graph.binding(id);
  const tpl = c.формула ?? `${c.id}(${[...bound.keys()].map((r) => `%${r}`).join(', ')})`;
  // Прозрачная обёртка (as-sub, whole-sub — шаблон целиком состоит из одной
  // подстановки) не добавляет ни знака, а значит и скобок не требует:
  // «[N, N] нормальна», а не «([N, N]) нормальна».
  const одна = /^%\{([^}]+)\}$|^%(\p{L}[\p{L}\p{N}]*)$/u.exec(tpl);
  if (одна) {
    const target = одна[1] ? graph.resolve(одна[1], bound) : bound.get(одна[2]);
    return render(graph, target, names, prec);
  }
  // Две формы подстановки: %X — роль, %{dom F} — производная связь.
  // Подстановка ВНУТРИ скобок шаблона уже отделена ими, поэтому своих скобок
  // не требует: Z(G × H), а не Z((G × H)).
  const re = /%\{([^}]+)\}|%(\p{L}[\p{L}\p{N}]*)/gu;
  let s = '';
  let last = 0;
  let depth = 0;
  for (let m = re.exec(tpl); m; m = re.exec(tpl)) {
    const между = tpl.slice(last, m.index);
    for (const ch of между) {
      if ('([{'.includes(ch)) depth++;
      else if (')]}'.includes(ch)) depth--;
    }
    const target = m[1] ? graph.resolve(m[1], bound) : bound.get(m[2]);
    if (target === undefined || target === null) {
      throw new Error(`${c.id}: нечего подставить вместо ${m[1] ?? m[2]}`);
    }
    s += между + render(graph, target, names, depth > 0 ? 0 : my);
    last = m.index + m[0].length;
  }
  s += tpl.slice(last);
  if (my < prec) s = `(${s})`;
  return s;
}
