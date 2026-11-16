// Конкретные конечные группы: таблица умножения и всё, что по ней считается.
//
// Зачем модель, а не список объектов со свойствами. Условие задачи — это ГРАФ
// построения, и опровергнуть надо утверждение про построенный терм: «G/N
// циклична», «Z(G × H) тривиален». Список объектов такого не умеет — нужна
// модель, в которой конструкции действительно вычисляются. Поэтому здесь есть
// фактор, центр, коммутант, произведение, автоморфизмы и гомоморфизмы, а не
// таблица готовых ответов.
//
// Граница честная и узкая: модель конечна. Свободное произведение, свободная
// группа, ℤ и ℚ в ней непредставимы — и там, где схема их требует, примера
// просто не будет. Молчать об этом нельзя: «опровержения не нашлось» и «искать
// было негде» — разные вещи.
//
// Соглашения: элементы — числа 0..n−1, единица всегда 0.

export function группа(n, mul, имя = null) {
  const g = { n, mul, имя, _кэш: {} };
  g.inv = new Int32Array(n);
  for (let a = 0; a < n; a++) {
    for (let b = 0; b < n; b++) {
      if (mul[a * n + b] === 0) {
        g.inv[a] = b;
        break;
      }
    }
  }
  return g;
}

const кэш = (G, ключ, считать) => (G._кэш[ключ] ??= считать());

export function умножить(G, a, b) {
  return G.mul[a * G.n + b];
}

// --- построение -------------------------------------------------------------

// Группа перестановок, порождённая данными. Перестановка — массив образов.
export function изПерестановок(генераторы, имя = null) {
  const степень = генераторы[0].length;
  const ед = Array.from({ length: степень }, (_, i) => i);
  const ключ = (p) => p.join(',');
  const есть = new Map([[ключ(ед), 0]]);
  const элементы = [ед];
  const состав = (p, q) => p.map((_, i) => p[q[i]]);
  for (let i = 0; i < элементы.length; i++) {
    for (const г of генераторы) {
      const пр = состав(элементы[i], г);
      const k = ключ(пр);
      if (!есть.has(k)) {
        есть.set(k, элементы.length);
        элементы.push(пр);
      }
    }
  }
  const n = элементы.length;
  const mul = new Int32Array(n * n);
  for (let a = 0; a < n; a++) {
    for (let b = 0; b < n; b++) {
      mul[a * n + b] = есть.get(ключ(состав(элементы[a], элементы[b])));
    }
  }
  return группа(n, mul, имя);
}

export function циклическая(n, имя = null) {
  const mul = new Int32Array(n * n);
  for (let a = 0; a < n; a++) for (let b = 0; b < n; b++) mul[a * n + b] = (a + b) % n;
  return группа(n, mul, имя ?? `C${n}`);
}

export function прямоеПроизведение(A, B, имя = null) {
  const n = A.n * B.n;
  const mul = new Int32Array(n * n);
  const код = (a, b) => a * B.n + b;
  for (let a1 = 0; a1 < A.n; a1++) {
    for (let b1 = 0; b1 < B.n; b1++) {
      for (let a2 = 0; a2 < A.n; a2++) {
        for (let b2 = 0; b2 < B.n; b2++) {
          mul[код(a1, b1) * n + код(a2, b2)] =
            код(A.mul[a1 * A.n + a2], B.mul[b1 * B.n + b2]);
        }
      }
    }
  }
  return группа(n, mul, имя ?? `${A.имя} × ${B.имя}`);
}

// --- элементы ---------------------------------------------------------------

export function порядокЭлемента(G, a) {
  let x = a;
  let k = 1;
  while (x !== 0) {
    x = умножить(G, x, a);
    k++;
  }
  return k;
}

export function порядки(G) {
  return кэш(G, 'порядки', () => {
    const out = new Int32Array(G.n);
    for (let a = 0; a < G.n; a++) out[a] = порядокЭлемента(G, a);
    return out;
  });
}

// --- подгруппы --------------------------------------------------------------

export function порождённая(G, элементы) {
  const есть = new Uint8Array(G.n);
  есть[0] = 1;
  const список = [0];
  for (const e of элементы) if (!есть[e]) (есть[e] = 1), список.push(e);
  for (let i = 0; i < список.length; i++) {
    for (let j = 0; j < список.length; j++) {
      const p = умножить(G, список[i], список[j]);
      if (!есть[p]) {
        есть[p] = 1;
        список.push(p);
      }
    }
  }
  return список.sort((a, b) => a - b);
}

export const ключПодгруппы = (H) => H.join(',');

// Все подгруппы: начиная с тривиальной, добавляем по элементу и замыкаем.
// Дороговато, но честно и для наших порядков (до ~60) быстро.
export function подгруппы(G) {
  return кэш(G, 'подгруппы', () => {
    const найдено = new Map();
    const очередь = [[0]];
    найдено.set('0', [0]);
    for (let i = 0; i < очередь.length; i++) {
      const H = очередь[i];
      const вH = new Uint8Array(G.n);
      for (const h of H) вH[h] = 1;
      for (let g = 1; g < G.n; g++) {
        if (вH[g]) continue;
        const K = порождённая(G, [...H, g]);
        const k = ключПодгруппы(K);
        if (!найдено.has(k)) {
          найдено.set(k, K);
          очередь.push(K);
        }
      }
    }
    return [...найдено.values()].sort((a, b) => a.length - b.length || ключПодгруппы(a).localeCompare(ключПодгруппы(b)));
  });
}

export function нормальна(G, H) {
  const вH = new Uint8Array(G.n);
  for (const h of H) вH[h] = 1;
  for (let g = 0; g < G.n; g++) {
    for (const h of H) {
      const сопр = умножить(G, умножить(G, g, h), G.inv[g]);
      if (!вH[сопр]) return false;
    }
  }
  return true;
}

export function характеристична(G, H) {
  const вH = new Uint8Array(G.n);
  for (const h of H) вH[h] = 1;
  for (const φ of автоморфизмыКакОтображения(G)) {
    for (const h of H) if (!вH[φ[h]]) return false;
  }
  return true;
}

export function центр(G) {
  return кэш(G, 'центр', () => {
    const out = [];
    for (let a = 0; a < G.n; a++) {
      let центральный = true;
      for (let b = 0; b < G.n && центральный; b++) {
        if (умножить(G, a, b) !== умножить(G, b, a)) центральный = false;
      }
      if (центральный) out.push(a);
    }
    return out;
  });
}

export function коммутант(G) {
  return кэш(G, 'коммутант', () => {
    const коммутаторы = [];
    for (let a = 0; a < G.n; a++) {
      for (let b = 0; b < G.n; b++) {
        коммутаторы.push(
          умножить(G, умножить(G, G.inv[a], G.inv[b]), умножить(G, a, b)),
        );
      }
    }
    return порождённая(G, коммутаторы);
  });
}

export function централизатор(G, H) {
  const out = [];
  for (let a = 0; a < G.n; a++) {
    let годится = true;
    for (const h of H) if (умножить(G, a, h) !== умножить(G, h, a)) годится = false;
    if (годится) out.push(a);
  }
  return out;
}

export function нормализатор(G, H) {
  const вH = new Uint8Array(G.n);
  for (const h of H) вH[h] = 1;
  const out = [];
  for (let a = 0; a < G.n; a++) {
    let годится = true;
    for (const h of H) {
      if (!вH[умножить(G, умножить(G, a, h), G.inv[a])]) годится = false;
    }
    if (годится) out.push(a);
  }
  return out;
}

export function пересечение(A, B) {
  const вB = new Set(B);
  return A.filter((x) => вB.has(x));
}

export function кручение(G) {
  // В конечной группе все элементы конечного порядка, поэтому подгруппа
  // кручения — вся группа. Операция всё равно определена только для абелевых.
  return Array.from({ length: G.n }, (_, i) => i);
}

// --- фактор ------------------------------------------------------------------

export function фактор(G, N) {
  const слой = new Int32Array(G.n).fill(-1);
  const представители = [];
  for (let g = 0; g < G.n; g++) {
    if (слой[g] >= 0) continue;
    const номер = представители.length;
    представители.push(g);
    for (const h of N) слой[умножить(G, g, h)] = номер;
  }
  const m = представители.length;
  const mul = new Int32Array(m * m);
  for (let i = 0; i < m; i++) {
    for (let j = 0; j < m; j++) {
      mul[i * m + j] = слой[умножить(G, представители[i], представители[j])];
    }
  }
  // Единица фактора обязана быть нулём: смежный класс самой N.
  const ноль = слой[0];
  if (ноль !== 0) {
    const переставить = (x) => (x === ноль ? 0 : x === 0 ? ноль : x);
    const mul2 = new Int32Array(m * m);
    for (let i = 0; i < m; i++) {
      for (let j = 0; j < m; j++) {
        mul2[i * m + j] = переставить(mul[переставить(i) * m + переставить(j)]);
      }
    }
    return { группа: группа(m, mul2), слой: Array.from(слой, переставить) };
  }
  return { группа: группа(m, mul), слой: Array.from(слой) };
}

// --- морфизмы -----------------------------------------------------------------

// Небольшой порождающий набор — чтобы гомоморфизмы перебирать по образам
// образующих, а не по всем отображениям.
export function образующие(G) {
  return кэш(G, 'образующие', () => {
    const по = порядки(G);
    const порядокУбыв = Array.from({ length: G.n - 1 }, (_, i) => i + 1)
      .sort((a, b) => по[b] - по[a]);
    const набор = [];
    let текущая = [0];
    for (const g of порядокУбыв) {
      if (текущая.includes(g)) continue;
      набор.push(g);
      текущая = порождённая(G, набор);
      if (текущая.length === G.n) break;
    }
    return набор;
  });
}

// Все гомоморфизмы G → H как массивы образов. Перебор по образам образующих
// с проверкой корректности продолжения.
let счётчикГрупп = 0;
const uid = (G) => (G._uid ??= ++счётчикГрупп);

export function гомоморфизмы(G, H) {
  G._гом ??= new Map();
  const k = uid(H);
  if (G._гом.has(k)) return G._гом.get(k);
  const итог = посчитатьГомоморфизмы(G, H);
  G._гом.set(k, итог);
  return итог;
}

function посчитатьГомоморфизмы(G, H) {
  const ген = образующие(G);
  const out = [];
  const образы = new Array(ген.length);
  const идти = (i) => {
    if (i === ген.length) {
      const φ = продолжить(G, H, ген, образы);
      if (φ) out.push(φ);
      return;
    }
    for (let h = 0; h < H.n; h++) {
      образы[i] = h;
      идти(i + 1);
    }
  };
  идти(0);
  return out;
}

// Продолжение по образующим: идём по словам, проверяя согласованность.
function продолжить(G, H, ген, образы) {
  const φ = new Int32Array(G.n).fill(-1);
  φ[0] = 0;
  const очередь = [0];
  for (let i = 0; i < очередь.length; i++) {
    const g = очередь[i];
    for (let k = 0; k < ген.length; k++) {
      const gg = умножить(G, g, ген[k]);
      const обр = умножить(H, φ[g], образы[k]);
      if (φ[gg] === -1) {
        φ[gg] = обр;
        очередь.push(gg);
      } else if (φ[gg] !== обр) {
        return null;
      }
    }
  }
  if (очередь.length !== G.n) return null;
  // Проверка на всякий случай: продолжение обязано быть гомоморфизмом.
  for (let a = 0; a < G.n; a++) {
    for (let b = 0; b < G.n; b++) {
      if (φ[умножить(G, a, b)] !== умножить(H, φ[a], φ[b])) return null;
    }
  }
  return Array.from(φ);
}

export function ядро(G, φ) {
  const out = [];
  for (let g = 0; g < G.n; g++) if (φ[g] === 0) out.push(g);
  return out;
}

export function образ(G, φ) {
  return [...new Set(φ)].sort((a, b) => a - b);
}

export function автоморфизмыКакОтображения(G) {
  return кэш(G, 'авто', () => {
    const все = гомоморфизмы(G, G);
    return все.filter((φ) => new Set(φ).size === G.n);
  });
}

export function группаАвтоморфизмов(G) {
  return кэш(G, 'Aut', () => {
    const авт = автоморфизмыКакОтображения(G);
    if (авт.length === 1) return циклическая(1, 'Aut');
    return изПерестановок(авт, `Aut(${G.имя ?? '?'})`);
  });
}

export function изоморфны(A, B) {
  if (A.n !== B.n) return false;
  const пA = [...порядки(A)].sort().join(',');
  const пB = [...порядки(B)].sort().join(',');
  if (пA !== пB) return false;
  return гомоморфизмы(A, B).some((φ) => new Set(φ).size === A.n);
}

// --- свойства -------------------------------------------------------------------

export function абелева(G) {
  return кэш(G, 'абелева', () => {
    for (let a = 0; a < G.n; a++) {
      for (let b = a + 1; b < G.n; b++) {
        if (умножить(G, a, b) !== умножить(G, b, a)) return false;
      }
    }
    return true;
  });
}

export function циклична(G) {
  return [...порядки(G)].some((p) => p === G.n);
}

export function разрешима(G) {
  let H = Array.from({ length: G.n }, (_, i) => i);
  for (let шаг = 0; шаг < 64; шаг++) {
    if (H.length === 1) return true;
    const под = подгруппаКакГруппа(G, H);
    const K = коммутант(под.группа).map((x) => под.назад[x]);
    if (K.length === H.length) return false;
    H = K;
  }
  return false;
}

export function нильпотентна(G) {
  // Верхний центральный ряд: Z_0 = 1, Z_{i+1}/Z_i = Z(G/Z_i).
  let Z = [0];
  for (let шаг = 0; шаг < 64; шаг++) {
    if (Z.length === G.n) return true;
    const ф = фактор(G, Z);
    const ц = центр(ф.группа);
    const вЦ = new Set(ц);
    const следующий = [];
    for (let g = 0; g < G.n; g++) if (вЦ.has(ф.слой[g])) следующий.push(g);
    if (следующий.length === Z.length) return false;
    Z = следующий;
  }
  return false;
}

// Классы сопряжённости — они же дают дешёвую проверку простоты.
export function классыСопряжённости(G) {
  return кэш(G, 'классы', () => {
    const класс = new Int32Array(G.n).fill(-1);
    const представители = [];
    for (let a = 0; a < G.n; a++) {
      if (класс[a] >= 0) continue;
      const номер = представители.length;
      представители.push(a);
      for (let g = 0; g < G.n; g++) {
        класс[умножить(G, умножить(G, g, a), G.inv[g])] = номер;
      }
    }
    return представители;
  });
}

export function нормальноеЗамыкание(G, элементы) {
  const все = [];
  for (const a of элементы) {
    for (let g = 0; g < G.n; g++) все.push(умножить(G, умножить(G, g, a), G.inv[g]));
  }
  return порождённая(G, все);
}

// Простота через нормальные замыкания, а НЕ через перебор всех подгрупп:
// у группы порядка 3600 подгрупп столько, что перебор не кончается, а
// замыканий надо ровно по одному на класс сопряжённости.
export function проста(G) {
  return кэш(G, 'проста', () => {
    if (G.n === 1) return false;
    for (const a of классыСопряжённости(G)) {
      if (a === 0) continue;
      if (нормальноеЗамыкание(G, [a]).length !== G.n) return false;
    }
    return true;
  });
}

// Подгруппа как самостоятельная группа плюс перевод номеров обратно.
export function подгруппаКакГруппа(G, H) {
  const вперёд = new Map(H.map((h, i) => [h, i]));
  const m = H.length;
  const mul = new Int32Array(m * m);
  for (let i = 0; i < m; i++) {
    for (let j = 0; j < m; j++) mul[i * m + j] = вперёд.get(умножить(G, H[i], H[j]));
  }
  // Единица подгруппы — это 0 группы, и в H он стоит первым.
  return { группа: группа(m, mul), назад: H, вперёд };
}

// Полный набор свойств — ровно тех, что объявлены в data/grp.json.
// Разложима ли группа: есть ли пара СОБСТВЕННЫХ нормальных подгрупп с
// тривиальным пересечением и произведением порядков, равным порядку группы.
// Этого достаточно: такие две подгруппы порождают всю группу и перестановочны
// поэлементно, значит G — их внутреннее прямое произведение.
export function разложима(G) {
  return кэш(G, 'разложима', () => {
    if (G.n <= 1) return false;
    const норм = подгруппы(G).filter((H) => H.length > 1 && H.length < G.n && нормальна(G, H));
    for (let i = 0; i < норм.length; i++) {
      for (let k = i + 1; k < норм.length; k++) {
        if (норм[i].length * норм[k].length !== G.n) continue;
        if (пересечение(норм[i], норм[k]).length === 1) return true;
      }
    }
    return false;
  });
}

export function свойстваГруппы(G) {
  return кэш(G, 'свойства', () => посчитатьСвойства(G));
}

function посчитатьСвойства(G) {
  const тривиальна = G.n === 1;
  return {
    trivial: тривиальна,
    abelian: абелева(G),
    cyclic: циклична(G),
    finite: true,
    'fin-gen': true,
    free: тривиальна, // свободная группа конечна только если она тривиальна
    simple: проста(G),
    solvable: разрешима(G),
    nilpotent: нильпотентна(G),
    perfect: коммутант(G).length === G.n,
    indecomposable: !разложима(G),
    'torsion-free': тривиальна,
    periodic: true,
    divisible: тривиальна, // конечная делимая группа тривиальна
    centerless: центр(G).length === 1,
    'residually-finite': true,
  };
}

export function свойстваПодгруппы(G, H) {
  return {
    normal: нормальна(G, H),
    characteristic: характеристична(G, H),
    maximal: H.length < G.n && !подгруппы(G).some((K) => K.length > H.length && K.length < G.n && содержит(K, H)),
    whole: H.length === G.n,
    central: H.every((h) => центр(G).includes(h)),
    'finite-index': true,
  };
}

export function свойстваМорфизма(G, H, φ) {
  const инъективен = new Set(φ).size === G.n;
  const сюръективен = new Set(φ).size === H.n;
  return {
    injective: инъективен,
    surjective: сюръективен,
    iso: инъективен && сюръективен,
    'zero-mor': φ.every((x) => x === 0),
  };
}

export function содержит(K, H) {
  const вK = new Set(K);
  return H.every((h) => вK.has(h));
}
