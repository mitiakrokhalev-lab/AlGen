"""Ленивый отдельный SAT-решатель Search без изменения формата native-кэшей.

Табличные формы используют Search для образов/фактов, но не запрашивают его
SAT. Конструктор настоящего Search переиспользуется через адаптер фабрики;
после конструктора его T — исходная Theory, а не адаптер. library.py и
отпечаток существующих native-таблиц не меняются.
"""

import os


class DeferredSolver:
    """Свой solver при первом обращении. Удалённый handle не возрождается.

    Служебные probes не открывают SAT; сериализовать solver-handle нельзя,
    как и исходный native solver. Каркас сохраняет search=None отдельно.
    """

    def __init__(self, factory):
        self._factory = factory
        self._solver = None
        self._closed = False

    @property
    def materialized(self):
        """Фабрика уже была успешно вызвана (в том числе до delete)."""
        return self._solver is not None

    def _open(self):
        if self._closed:
            raise RuntimeError("SAT-решатель уже удалён")
        if self._solver is None:
            self._solver = self._factory()
        return self._solver

    def __getattr__(self, name):
        if name.startswith("_"):
            raise AttributeError(name)
        return getattr(self._open(), name)

    def delete(self):
        if self._closed:
            return
        self._closed = True
        self._factory = None
        if self._solver is not None:
            self._solver.delete()

    def __enter__(self):
        if self._closed:
            raise RuntimeError("SAT-решатель уже удалён")
        return self

    def __exit__(self, *args):
        self.delete()

    def __getstate__(self):
        raise TypeError("SAT-решатель не сериализуется; каркас сохраняется без search")


class _TheoryFactory:
    def __init__(self, theory):
        self._original = theory

    def solver(self):
        return DeferredSolver(self._original.solver)

    def __getattr__(self, name):
        return getattr(self._original, name)


def make_search(graph, theory, lib, *, constructor=None, **options):
    """Обычный Search с отложенным собственным solver; теория уже построена."""
    from .library import Search
    constructor = Search if constructor is None else constructor
    # Подменённый конструктор — существующая точка расширения SchemeForm.
    # Адаптер применим к штатному Search; подмена получает исходную Theory.
    if constructor is not Search or os.environ.get("ALGEN_EAGER_SEARCH", "0") == "1":
        return constructor(graph, theory, lib, **options)
    search = Search(graph, _TheoryFactory(theory), lib, **options)
    search.T = theory
    return search
