// Модель топологических пространств.
//
// Ключ ко всему: КОНЕЧНОЕ топологическое пространствоП — это в точности
// предпорядок. Открытые множества суть множества, замкнутые вниз по
// специализации (x ≤ y, если всякое открытоПе, содержащее y, содержит x).
// Поэтому конечные пространства не берутся по рецептам, как конечные группы, —
// они ПЕРЕЧИСЛЯЮТСЯ целиком: все предпорядки на 1…4 точках с точностью до
// изоморфизма. Это и полнее списка, и дешевле: на 4 точках их 33.
//
// Пространство хранится матрицей достижимости `le`: le[x][y] = 1 значит x ≤ y.
// Открытое множество — то, что замкнутоП ВНИЗ: если y ∈ U и x ≤ y, то x ∈ U.
//
// Цена модели названа в data/top.json и в README: у конечных пространств
// половина свойств вырождается (T₁ равносильно дискретности, метризуемость
// тоже, вторая аксиома счётности верна всегда). Ради нетривиальных ответов
// нужны ОБЪЯВЛЕННЫЕ бесконечные пространства — ℝ, ℚ, Зоргенфрей, — и они
// живут в data/top-infinite.json ровно так же, как бесконечные группы.

import { НЕ_СЧИТАЕМ } from './значение.js';

// --- конечные пространства ------------------------------------------------------

export function пространствоП(n, le, имя = null) {
  return { n, le, имя, _кэш: {} };
}

const кэшП = (X, ключ, считать) => (X._кэш[ключ] ??= считать());

// Открыто ли множество (набор номеров точек): замкнутоП ли оно вниз.
export function открытоП(X, U) {
  const в = new Uint8Array(X.n);
  for (const y of U) в[y] = 1;
  for (const y of U) {
    for (let x = 0; x < X.n; x++) if (X.le[x][y] && !в[x]) return false;
  }
  return true;
}

export function замкнутоП(X, U) {
  const в = new Uint8Array(X.n);
  for (const y of U) в[y] = 1;
  const доп = [];
  for (let x = 0; x < X.n; x++) if (!в[x]) доп.push(x);
  return открытоП(X, доп);
}

// Замыкание: всё, что выше по ≤ (x ∈ cl A ⟺ ∃ a ∈ A: x ≥ a … в нашей
// записи cl A = { x : ∃ a ∈ A, a ≤ x }? Нет: открытые замкнуты вниз, значит
// замкнутые замкнуты ВВЕРХ, и cl A = { x : ∃ a ∈ A, x ≥ a } неверно.
// Разберём честно: наименьшее замкнутоПе, содержащее A, — это множество всех x,
// каждое открытоПе окружение которых пересекает A. Окрестности x — это
// открытые, содержащие x, наименьшая из них U_x = { z : z ≤ x }. Значит
// x ∈ cl A ⟺ U_x ∩ A ≠ ∅ ⟺ ∃ a ∈ A: a ≤ x.
export function замыканиеП(X, A) {
  const out = [];
  for (let x = 0; x < X.n; x++) {
    if (A.some((a) => X.le[a][x])) out.push(x);
  }
  return out;
}

// Внутренность: наибольшее открытоПе внутри A, то есть { x ∈ A : U_x ⊆ A }.
export function внутренностьП(X, A) {
  const в = new Uint8Array(X.n);
  for (const a of A) в[a] = 1;
  const out = [];
  for (const x of A) {
    let годится = true;
    for (let z = 0; z < X.n; z++) if (X.le[z][x] && !в[z]) { годится = false; break; }
    if (годится) out.push(x);
  }
  return out;
}

// Связность: считаем компоненты по симметризованному отношению.
export function связноП(X) {
  return кэшП(X, 'связноП', () => {
    if (X.n <= 1) return true;
    const цвет = new Int32Array(X.n).fill(-1);
    цвет[0] = 0;
    const стек = [0];
    while (стек.length) {
      const x = стек.pop();
      for (let y = 0; y < X.n; y++) {
        if (цвет[y] >= 0) continue;
        if (X.le[x][y] || X.le[y][x]) { цвет[y] = 0; стек.push(y); }
      }
    }
    return цвет.every((c) => c === 0);
  });
}

export const дискретно = (X) => кэшП(X, 'дискретно', () => {
  for (let x = 0; x < X.n; x++) for (let y = 0; y < X.n; y++) if (x !== y && X.le[x][y]) return false;
  return true;
});

export const антидискретно = (X) => кэшП(X, 'антидискретно', () => {
  for (let x = 0; x < X.n; x++) for (let y = 0; y < X.n; y++) if (!X.le[x][y]) return false;
  return true;
});

// T₀ — это в точности антисимметричность предпорядка.
export const T0 = (X) => кэшП(X, 'T0', () => {
  for (let x = 0; x < X.n; x++) {
    for (let y = x + 1; y < X.n; y++) if (X.le[x][y] && X.le[y][x]) return false;
  }
  return true;
});

// ПодпространствоП: точки A с наведённым порядком.
export function подпростр(X, A) {
  const le = A.map((x) => A.map((y) => X.le[x][y]));
  return пространствоП(A.length, le, null);
}

export function произведениеП(X, Y) {
  const n = X.n * Y.n;
  const le = Array.from({ length: n }, () => new Uint8Array(n));
  for (let a = 0; a < n; a++) {
    for (let b = 0; b < n; b++) {
      le[a][b] = X.le[Math.floor(a / Y.n)][Math.floor(b / Y.n)] && Y.le[a % Y.n][b % Y.n] ? 1 : 0;
    }
  }
  return пространствоП(n, le, null);
}

export function суммаП(X, Y) {
  const n = X.n + Y.n;
  const le = Array.from({ length: n }, () => new Uint8Array(n));
  for (let a = 0; a < X.n; a++) for (let b = 0; b < X.n; b++) le[a][b] = X.le[a][b];
  for (let a = 0; a < Y.n; a++) for (let b = 0; b < Y.n; b++) le[X.n + a][X.n + b] = Y.le[a][b];
  return пространствоП(n, le, null);
}

// Фактор по подпространству: A стягивается в точку. Предпорядок на фактор-
// множестве — транзитивное замыканиеП образа исходного.
export function стянутьП(X, A) {
  if (!A.length) return X;
  const вA = new Uint8Array(X.n);
  for (const a of A) вA[a] = 1;
  const номер = new Int32Array(X.n).fill(-1);
  let k = 0;
  const точкаA = k++;
  for (let x = 0; x < X.n; x++) номер[x] = вA[x] ? точкаA : k++;
  const n = k;
  const le = Array.from({ length: n }, () => new Uint8Array(n));
  for (let i = 0; i < n; i++) le[i][i] = 1;
  for (let x = 0; x < X.n; x++) {
    for (let y = 0; y < X.n; y++) if (X.le[x][y]) le[номер[x]][номер[y]] = 1;
  }
  // Транзитивное замыканиеП: склейка точек рвёт транзитивность.
  for (let m = 0; m < n; m++) {
    for (let i = 0; i < n; i++) {
      if (!le[i][m]) continue;
      for (let j = 0; j < n; j++) if (le[m][j]) le[i][j] = 1;
    }
  }
  return пространствоП(n, le, null);
}

// Непрерывные отображенияП: сохраняющие предпорядок. Для конечных пространств
// непрерывность — это в точности монотонность, и перебирать их можно прямо.
export function отображенияП(X, Y, предел = 4096) {
  return кэшП(X, `отоб:${Y.n}:${ключПространства(Y)}`, () => {
    const out = [];
    const φ = new Int32Array(X.n);
    const годится = (до) => {
      for (let x = 0; x <= до; x++) {
        for (let y = 0; y <= до; y++) {
          if (X.le[x][y] && !Y.le[φ[x]][φ[y]]) return false;
        }
      }
      return true;
    };
    const идти = (i) => {
      if (out.length >= предел) return;
      if (i === X.n) { out.push(Array.from(φ)); return; }
      for (let v = 0; v < Y.n; v++) {
        φ[i] = v;
        if (годится(i)) идти(i + 1);
      }
    };
    идти(0);
    return out;
  });
}

export const ключПространства = (X) => кэшП(X, 'ключ', () => `${X.n}:${X.le.map((r) => Array.from(r).join('')).join('|')}`);

// Гомеоморфны ли: изоморфизм предпорядков. Перебор перестановок годится, пока
// точек немного, а больше пяти у нас и не бывает.
export function гомеоморфны(X, Y) {
  if (X.n !== Y.n) return false;
  const п = new Int32Array(X.n);
  const занято = new Uint8Array(X.n);
  const идти = (i) => {
    if (i === X.n) {
      for (let a = 0; a < X.n; a++) {
        for (let b = 0; b < X.n; b++) if (X.le[a][b] !== Y.le[п[a]][п[b]]) return false;
      }
      return true;
    }
    for (let v = 0; v < X.n; v++) {
      if (занято[v]) continue;
      занято[v] = 1; п[i] = v;
      if (идти(i + 1)) return true;
      занято[v] = 0;
    }
    return false;
  };
  return идти(0);
}

// --- свойства конечного пространства ---------------------------------------------

export function свойстваПространства(X) {
  return кэшП(X, 'свойства', () => {
    const д = дискретно(X);
    const св = связноП(X);
    return {
      point: X.n === 1,
      finite: true,
      countable: true,
      // В конечном пространстве T₁ равносильно дискретности, а T₂, T₃, T₄ и
      // метризуемость — ей же. Это не упрощение модели, а теорема.
      T0: T0(X),
      T1: д,
      T2: д,
      T3: д,
      T4: д,
      metrizable: д,
      discrete: д,
      indiscrete: антидискретно(X),
      connected: св,
      // Конечное связноПе пространствоП линейно связноП (путь строится по цепочке
      // сравнимых точек), поэтому здесь связноПсть и линейная связноПсть — одно.
      'path-connected': св,
      'totally-disconnected': д,
      compact: true,
      'locally-compact': true,
      'first-countable': true,
      'second-countable': true,
      separable: true,
    };
  });
}

export function свойстваПодпространства(X, A) {
  const как = подпростр(X, A);
  return {
    ...свойстваПространства(как),
    open: открытоП(X, A),
    closed: замкнутоП(X, A),
    dense: замыканиеП(X, A).length === X.n,
    whole: A.length === X.n,
  };
}

export function свойстваОтображения(X, Y, φ) {
  const образ = new Set(φ);
  const инъ = образ.size === φ.length;
  const сюр = образ.size === Y.n;
  return {
    injective: инъ,
    surjective: сюр,
    constant: образ.size === 1,
    // Непрерывная биекция конечных пространств — гомеоморфизм тогда и только
    // тогда, когда обратное тоже монотонно.
    homeo: инъ && сюр && обратноеМонотонно(X, Y, φ),
  };
}

function обратноеМонотонно(X, Y, φ) {
  const назад = new Int32Array(Y.n).fill(-1);
  φ.forEach((v, i) => { назад[v] = i; });
  for (let a = 0; a < Y.n; a++) {
    for (let b = 0; b < Y.n; b++) {
      if (Y.le[a][b] && !X.le[назад[a]][назад[b]]) return false;
    }
  }
  return true;
}

// --- перечисление всех конечных пространств -------------------------------------

// Все предпорядки на n точках с точностью до изоморфизма. Перебираем матрицы
// рефлексивных транзитивных отношений; на четырёх точках их 355, классов 33.
export function всеПространства(n) {
  const пары = [];
  for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if (i !== j) пары.push([i, j]);
  const le = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i === j ? 1 : 0)));
  const найдено = [];
  const виденные = new Set();

  const транзитивно = () => {
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        if (!le[i][j]) continue;
        for (let k = 0; k < n; k++) if (le[j][k] && !le[i][k]) return false;
      }
    }
    return true;
  };

  const идти = (i) => {
    if (i === пары.length) {
      if (!транзитивно()) return;
      const X = пространствоП(n, le.map((r) => Uint8Array.from(r)));
      if (найдено.some((Y) => гомеоморфны(X, Y))) return;
      const k = ключПространства(X);
      if (виденные.has(k)) return;
      виденные.add(k);
      найдено.push(X);
      return;
    }
    const [a, b] = пары[i];
    le[a][b] = 0;
    идти(i + 1);
    le[a][b] = 1;
    идти(i + 1);
    le[a][b] = 0;
  };
  идти(0);
  return найдено;
}

export { НЕ_СЧИТАЕМ };
