"""Компактные минимальные условия без изменения их порядка и значений.

Перебор выдаёт внутри каждой длины посылок возрастающие пары (посылки, цель).
Храним их кодами без коллизий и поддержкой в числовых массивах; принадлежность
проверяется двоичным поиском. Порядок длин сохраняется (нулевые посылки идут
последними, как в enumerate_form). Здесь нет отбора или ограничения условий.
"""

from array import array
from bisect import bisect_left
from collections.abc import Mapping


def _uint(maximum):
    for code in ("B", "H", "I", "Q"):
        if maximum < 1 << (8 * array(code).itemsize):
            return code
    raise OverflowError("значение не помещается в беззнаковый массив")


class PackedConditions(Mapping):
    """Добавление упорядоченных условий и чтение как отображения.

    Длины образуют отдельные возрастающие массивы. Повтор последнего ключа
    обновляет значение, как dict; нарушение порядка явно останавливает прогон.
    Произвольный порядок целей обслуживает прежний словарь в enumerate_form.
    """

    def __init__(self, literals, max_premises, max_support):
        self.width = max(1, (max(1, literals) - 1).bit_length())
        self.mask = (1 << self.width) - 1
        self.key_type = _uint((1 << (self.width * (max_premises + 1) + 1)) - 1)
        self.support_type = _uint(max_support)
        self.literals = literals
        self.max_premises = max_premises
        self.max_support = max_support
        self.blocks = {}
        self.size = 0

    def empty_like(self):
        return type(self)(self.literals, self.max_premises, self.max_support)

    def _encode(self, prem, goal):
        if len(prem) > self.max_premises or any(
                j < 0 or j >= self.literals for j in (*prem, goal)):
            raise KeyError((prem, goal))
        code = 1  # маркер длины: ведущие нули литералов не теряются
        for j in prem:
            code = (code << self.width) | int(j)
        return (code << self.width) | int(goal)

    def __setitem__(self, key, support):
        prem, goal = key
        code = self._encode(prem, goal)
        if not 0 <= support <= self.max_support:
            raise ValueError("поддержка вне числа строк библиотеки")
        block = self.blocks.get(len(prem))
        if block is None:
            block = self.blocks[len(prem)] = (array(self.key_type), array(self.support_type))
        keys, values = block
        if keys and code <= keys[-1]:
            if code != keys[-1]:
                raise ValueError("условия одной длины пришли не по возрастанию")
            values[-1] = support
            return
        keys.append(code)
        values.append(support)
        self.size += 1

    def __getitem__(self, key):
        prem, goal = key
        code = self._encode(prem, goal)
        block = self.blocks.get(len(prem))
        if block is not None:
            keys, values = block
            i = bisect_left(keys, code)
            if i < len(keys) and keys[i] == code:
                return int(values[i])
        raise KeyError(key)

    def __len__(self):
        return self.size

    def items(self):
        width, mask = self.width, self.mask
        for n, (keys, values) in self.blocks.items():
            for code, support in zip(keys, values):
                goal = code & mask
                code >>= width
                prem = []
                for _ in range(n):
                    prem.append(code & mask)
                    code >>= width
                yield (tuple(reversed(prem)), goal), int(support)

    def __iter__(self):
        for key, _ in self.items():
            yield key

    @property
    def nbytes(self):
        return sum(len(a) * a.itemsize for block in self.blocks.values() for a in block)


def empty_like(conditions):
    return conditions.empty_like() if isinstance(conditions, PackedConditions) else {}
