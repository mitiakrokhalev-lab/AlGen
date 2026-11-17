// Что про терм известно БЕЗ вывода.
//
// Два источника: свойства, наложенные человеком на вводящий или выбирающий
// узел, и поле `gives` конструкции — то, что верно по самому построению
// (ядро нормально, центр абелев, свободная группа без кручения). Позже сюда
// подключится вывод по теоремам; интерфейс тот же, поэтому всё остальное
// менять не придётся.
//
// Возвращает true / false / undefined. Именно undefined, а не false: «не
// знаем» и «знаем, что нет» — разные вещи, и на их смешении теряются задачи.

export function known(graph, id, prop) {
  const n = graph.get(id);
  if (Object.prototype.hasOwnProperty.call(n.props ?? {}, prop)) return n.props[prop];
  const c = graph.cat.cons.get(n.op);
  const gives = c?.gives;
  if (gives && Object.prototype.hasOwnProperty.call(gives, prop)) return gives[prop];
  return undefined;
}

// Слоты, чьё `requires` не выполнено. Это не ошибка построения, а корзина
// выдачи: «не определено». Фактор кольца по подкольцу и подгруппа кручения
// неабелевой группы сюда и попадают.
export function undefinedSlots(graph, roots, ask = known) {
  const seen = new Set();
  for (const r of roots) for (const id of graph.support(r)) seen.add(id);
  const out = [];
  for (const id of seen) {
    const n = graph.get(id);
    const c = graph.cat.cons.get(n.op);
    if (!c) continue;
    (c.in ?? []).forEach((slot, i) => {
      for (const req of slot.requires ?? []) {
        const v = ask(graph, n.args[i], req);
        if (v !== true) {
          out.push({ узел: id, op: c.id, роль: slot.role, свойство: req, статус: v === false ? 'нет' : 'неизвестно' });
        }
      }
    });
  }
  return out;
}

// Связность условия. Несвязное условие — не задача: в прошлом проекте таких
// «утверждений» было 30 312 против 34 настоящих при одной посылке.
// Рёбра — это аргументы конструкций; вводящие узлы связываются только через них.
// `edges` — дополнительные связи: посылка-ОТНОШЕНИЕ («H ≅ ℤ», «D ⩽ N») тоже
// соединяет условие, хотя никакая конструкция через неё не проходит. Без
// этого задача 3.55 объявляется несвязной, а она настоящая.
export function components(graph, roots, edges = []) {
  const nodes = new Set();
  for (const r of roots) for (const id of graph.support(r)) nodes.add(id);
  for (const [a, b] of edges) {
    for (const id of graph.support(a)) nodes.add(id);
    for (const id of graph.support(b)) nodes.add(id);
  }
  const parent = new Map([...nodes].map((id) => [id, id]));
  const find = (a) => {
    while (parent.get(a) !== a) {
      parent.set(a, parent.get(parent.get(a)));
      a = parent.get(a);
    }
    return a;
  };
  const union = (a, b) => {
    const ra = find(a);
    const rb = find(b);
    if (ra !== rb) parent.set(ra, rb);
  };
  for (const id of nodes) for (const a of graph.get(id).args) union(id, a);
  for (const [a, b] of edges) union(a, b);
  const groups = new Map();
  for (const id of nodes) {
    const r = find(id);
    if (!groups.has(r)) groups.set(r, []);
    groups.get(r).push(id);
  }
  return [...groups.values()];
}
