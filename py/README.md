# Новый движок AlGen (Python)

План переделки — [docs/ПЕРЕДЕЛКА.md](../docs/ПЕРЕДЕЛКА.md).

Нужны Python 3.11+, `pip install python-sat pyyaml` и GAP 4.12 с библиотекой
SmallGroups (`apt install gap`).
Команды запускаются из этой папки.

```bash
# таблица конечных групп до порядка 100 (около часа на 4 ядрах)
python3 -m algen.finite --до 100

# проверка всех правил раздела групп на этой таблице
node ../tools/dump-rules.mjs grp > ../data/vocab/grp.json
python3 -m algen.check_rules ../data/vocab/grp.json

# эталон через вывод на SAT
python3 -m algen.etalon

# тесты
python3 -m unittest discover tests
```

Вывод — `algen/logic.py`: правила базы заземляются на граф условия и решаются
SAT-решателем. Словарь берётся из выгрузки `data/vocab/<раздел>.json` (её
пишет `tools/dump-rules.mjs` из старых `data/*.json`) с поправками
`data/new/<раздел>.json`: что снято и почему, что добавлено и с каким
статусом. Отчёт — [docs/вывод-sat.md](../docs/вывод-sat.md).

`data/pibase/pibase.json` — импорт π-Base: `python3 -m algen.pibase <клон pi-base/data>`; сверка старых пространств с ним — `python3 -m algen.audit_top`.

`data/finite/grp-small.jsonl` лежит в репозитории готовым, поэтому для проверки
правил GAP не нужен.
