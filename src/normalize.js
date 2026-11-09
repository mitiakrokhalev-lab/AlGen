// Приведение графа к нормальной форме вырождениями.
//
// Служит сразу трём целям (СХЕМА.md §4): дедупликация выдачи, отсев
// вырожденных условий, узнавание тождеств вроде G/[G,G] = G^ab.
//
// Главное правило: вырождение с УСЛОВИЕМ (ядро тривиально, ЕСЛИ морфизм
// инъективен) применяется только когда условие известно. «Не знаем» — не
// повод сворачивать: так теряется задача.

import { TermGraph, commutingRoles } from './term.js';
import { known as defaultKnown } from './facts.js';

export function normalize(graph, roots, ask = defaultKnown) {
  const out = new TermGraph(graph.cat);
  const map = new Map();
  const applied = [];

  const rebuild = (id) => {
    if (map.has(id)) return map.get(id);
    const n = graph.get(id);
    const args = n.args.map(rebuild);
    let fresh;
    if (n.op === 'given' || n.op === 'named') {
      fresh = out.given(n.sort, n.props, { имя: n.имя, named: n.op === 'named', rels: n.rels });
    } else {
      const c = graph.cat.cons.get(n.op);
      fresh = out.apply(n.op, args, { props: c.choice ? n.props : {}, quant: n.quant });
    }
    const reduced = reduce(out, fresh, ask, applied);
    map.set(id, reduced);
    return reduced;
  };

  const newRoots = roots.map(rebuild);
  return { graph: out, roots: newRoots, map, applied };
}

// Какие вырождения СРАБОТАЛИ БЫ — без перестройки графа. Нужно перебору:
// решение «условие вырождено» принимается по выведенным фактам, а не только по
// наложенным свойствам. Иначе «φ — изоморфизм, что можно сказать про ker φ»
// уходит в выдачу как задача, хотя ядро там тривиально.
export function вырождения(graph, roots, ask = defaultKnown) {
  const узлы = new Set();
  for (const r of roots) for (const id of graph.support(r)) узлы.add(id);
  const out = [];
  for (const id of узлы) {
    const n = graph.get(id);
    const c = graph.cat.cons.get(n.op);
    if (!c) continue;
    поиск: for (const bound of bindings(graph, id, c)) {
      for (const rule of graph.cat.degen) {
        if (rule.op !== n.op) continue;
        if (matches(graph, rule, bound, ask)) {
          out.push({ узел: id, правило: rule });
          break поиск;
        }
      }
    }
  }
  return out;
}

// Свернуть узел, пока сворачивается. Ограничитель — не потолок выдачи, а
// защита от циклической пары правил в данных; про срабатывание сообщаем вслух.
function reduce(graph, id, ask, applied) {
  for (let step = 0; step < 64; step++) {
    const hit = matchAny(graph, id, ask);
    if (!hit) return id;
    applied.push({ было: id, стало: hit.id, правило: hit.rule });
    id = hit.id;
  }
  throw new Error('вырождения зациклились — проверьте правила в данных');
}

// Экспортируется ради вывода: ему нужно знать, НА ЧТО вырождается узел, чтобы
// объявить изоморфизм фактом (см. `вырожденияВФакты` в src/deduce.js).
export function matchAny(graph, id, ask) {
  const n = graph.get(id);
  const c = graph.cat.cons.get(n.op);
  if (!c) return null;
  // У коммутативной операции правило, написанное на роль N, обязано ловить и
  // случай, когда вырожден аргумент в роли M: «пересечение с тривиальной» не
  // зависит от того, какой из двух тривиален.
  for (const bound of bindings(graph, id, c)) {
    for (const rule of graph.cat.degen) {
      if (rule.op !== n.op) continue;
      const полное = matches(graph, rule, bound, ask);
      if (!полное) continue;
      const to = build(graph, rule.equals, полное);
      if (to === id) continue;
      return { id: to, rule };
    }
  }
  return null;
}

function bindings(graph, id, c) {
  const base = graph.binding(id);
  const roles = commutingRoles(c);
  if (roles.length !== 2) return [base];
  const swapped = new Map(base);
  swapped.set(roles[0], base.get(roles[1]));
  swapped.set(roles[1], base.get(roles[0]));
  return [base, swapped];
}

// Возвращает расширенную привязку ролей (или null, если правило не подошло).
// Образец умеет ЗАХВАТЫВАТЬ аргументы вложенного терма: ядро проекции π_N —
// это сама N, но у роли F подгруппы N в привязке нет, её надо достать.
function matches(graph, rule, bound, ask) {
  const extra = new Map(bound);
  for (const [role, want] of Object.entries(rule.when ?? {})) {
    const target = extra.get(role);
    for (const [prop, value] of Object.entries(want)) {
      if (ask(graph, target, prop) !== value) return null;
    }
  }
  for (const [role, pat] of Object.entries(rule.pattern ?? {})) {
    const target = graph.get(extra.get(role));
    if (target.op !== pat.op) return null;
    const args = pat.args ?? [];
    if (args.length && args.length !== target.args.length) return null;
    for (let i = 0; i < args.length; i++) {
      if (args[i] === null) continue; // пропуск: любой аргумент
      if (graph.resolve(args[i], extra) !== target.args[i]) return null;
    }
    (pat.bind ?? []).forEach((имя, i) => {
      if (имя) extra.set(имя, target.args[i]);
    });
  }
  return extra;
}

function build(graph, equals, bound) {
  if (typeof equals === 'string') return bound.get(equals);
  const args = (equals.args ?? []).map((a) => graph.resolve(a, bound));
  return graph.apply(equals.op, args);
}
