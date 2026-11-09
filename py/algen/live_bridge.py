"""Подключение постоянных строк библиотеки к полному перебору схем.

ALGEN_DYNAMIC_DB и ALGEN_DYNAMIC_CONTEXT задаются вместе. Старые таблицы не
перезаписываются: строки добавляются к виду схемы. Отпечаток прогона включает
контекст, ревизию и реализацию моста; SAT-кэш зависит от прежней теории.
"""

import hashlib
import json
import os
from pathlib import Path

from .live import LiveArchive, dumps


def settings():
    path, ctx = os.environ.get("ALGEN_DYNAMIC_DB", ""), os.environ.get("ALGEN_DYNAMIC_CONTEXT", "")
    if bool(path) != bool(ctx):
        raise ValueError("ALGEN_DYNAMIC_DB и ALGEN_DYNAMIC_CONTEXT нужны вместе")
    if not path:
        return None
    if not Path(path).is_file():
        raise ValueError("динамический архив не существует")
    with LiveArchive(path) as a:
        rec = a.db.execute("SELECT header,revision FROM contexts WHERE id=?", (ctx,)).fetchone()
        if rec is None:
            raise ValueError("нет динамического контекста")
        header, revision, content = json.loads(rec["header"]), rec["revision"], a.fingerprint(ctx)
    implementation = hashlib.sha256(Path(__file__).read_bytes() + Path(__file__).with_name("live.py").read_bytes()).hexdigest()[:16]
    return {"path": path, "context": ctx, "revision": revision, "content": content, "header": header,
            "fingerprint": f":dynamic:{ctx}:{revision}:{content}:{implementation}"}


def append_rows(form, config, base, cls, theory):
    """Проверенные частичные значения дают лишь настоящие контрпримеры.

    Образы новых объектов не выдумываются: для такой строки _image возвращает
    None, текст и свидетельство берутся из сохранённой подстановки. Дополнительные
    значения выводятся обычным _derive; совместность с теорией обязательна.
    """
    import numpy as np
    from . import enumerate as E
    if not E.CLOSE_MARKED:
        raise ValueError("динамические строки пока требуют CLOSE_MARKED=True (помеченные факты тоже закрывают условия)")
    header = config["header"]
    if (header["base"] != base or header["class"] != cls or header["theory"] != theory
            or header.get("fixed", []) != sorted({E.lit_name(a, v) for a, v in form.fixed_lits})
            or header.get("variables", []) != sorted(str(v) for v in form.search.vars)):
        raise ValueError("динамический контекст не совпадает с базой, классом, теорией или fixed")
    names = {E.atom_name(a): a for a in form.atoms if a[0] != "pair"}
    projected, extra = [], {}
    start = form.m.shape[0]
    with LiveArchive(config["path"]) as archive:
        archive.db.execute("BEGIN")  # согласованный снимок ревизии и всех строк
        try:
            revision = archive.db.execute("SELECT revision FROM contexts WHERE id=?", (config["context"],)).fetchone()[0]
            if revision != config["revision"] or archive.fingerprint(config["context"]) != config["content"]:
                raise ValueError("динамическая библиотека изменилась: нужно перепланировать прогон")
            for packet in archive.active_examples(config["context"]):
                facts = {names[name]: value for name, value in packet["facts"].items() if name in names}
                assumptions = []
                for atom, value in facts.items():
                    lit = form.sc.T.lit(atom, value)
                    if lit is False:
                        raise ValueError("динамическая строка отрицает тождество: " + packet["key"])
                    if lit is not None:
                        assumptions.append(lit)
                if not form.sc.s.solve(assumptions=assumptions):
                    raise ValueError("динамическая строка противоречит теории: " + packet["key"])
                row = form._derive(facts)
                projected.append(row)
                extra[start + len(projected) - 1] = dict(packet, atom_facts=facts)
        finally:
            archive.db.execute("ROLLBACK")
    if projected:
        matrix = form._matrix(projected)
        form.m, form.s, form.e = (np.concatenate([mat, matrix]) for mat in (form.m, form.s, form.e))
        form.envs = list(form.envs) + [{} for _ in projected]
        form._live_rows = extra
        # Общая G-таблица может быть старой и не знать нового контрпримера.
        # Отбор generic_filter тогда небезопасен; остаются лишние вопросы,
        # а instances пользуется обновлённой матрицей самой схемы.
        form.generic = None
    return {"context": config["context"], "revision": config["revision"], "rows": len(projected)}
