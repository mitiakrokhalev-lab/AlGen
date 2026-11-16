// Сорта и подсорта.
//
// Сорт — строка «Категория.вид»: Grp.obj, Grp.sub, Ring.ideal, Top.mor.
// Подсортовое отношение «Grp.sub ≤ Grp.obj» значит: где ждут группу, можно
// подставить подгруппу, и речь пойдёт о ней как об объекте. Свойства, нужные
// только подгруппе (нормальность), объявлены на Grp.sub и наверх не уходят.
//
// Отношение бывает и кросс-категорным: Ring.ideal ≤ Mod.obj — идеал кольца
// есть модуль над ним.

export function parseSort(s) {
  const dot = s.indexOf('.');
  if (dot < 0) throw new Error(`сорт без категории: ${s}`);
  return { cat: s.slice(0, dot), kind: s.slice(dot + 1) };
}

export function categoryOf(sort) {
  return parseSort(sort).cat;
}

// Транзитивное замыкание объявленных пар «подсорт ≤ надсорт».
// Вход: [["Grp.sub", "Grp.obj"], ["Ring.ideal", "Mod.obj"], …]
// Выход: Map сорт → Set сортов, куда его можно подставить (включая себя).
export function closeSubsorts(pairs) {
  const up = new Map();
  const touch = (s) => {
    if (!up.has(s)) up.set(s, new Set([s]));
    return up.get(s);
  };
  for (const [lo, hi] of pairs) {
    touch(lo).add(hi);
    touch(hi);
  }
  let changed = true;
  while (changed) {
    changed = false;
    for (const [s, set] of up) {
      for (const t of [...set]) {
        for (const u of up.get(t) ?? []) {
          if (!set.has(u)) {
            set.add(u);
            changed = true;
          }
        }
      }
      void s;
    }
  }
  return up;
}

// Годится ли терм сорта `have` в слот, объявленный сортом `want`.
export function fits(have, want, up) {
  if (have === want) return true;
  const set = up.get(have);
  return set ? set.has(want) : false;
}

// Все сорта, на которых объявленное на `sort` свойство осмысленно, —
// то есть сам сорт и все его подсорта (вниз по отношению).
export function downward(sort, up) {
  const out = new Set([sort]);
  for (const [s, set] of up) if (set.has(sort)) out.add(s);
  return out;
}

// Свойство бывает объявлено сразу на нескольких сортах. Так «abelian» живёт и
// на объекте, и на СЕМЕЙСТВЕ, где значит «каждый член абелев», — иначе весь
// список свойств пришлось бы дублировать с приставкой.
export function свойствоПодходит(sort, p, up) {
  const где = Array.isArray(p.sort) ? p.sort : [p.sort];
  return где.some((s) => fits(sort, s, up));
}
