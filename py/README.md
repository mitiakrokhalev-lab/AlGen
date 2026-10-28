# Новый движок AlGen (Python)

План переделки — [docs/ПЕРЕДЕЛКА.md](../docs/ПЕРЕДЕЛКА.md).

Нужны Python 3.11+ и GAP 4.12 с библиотекой SmallGroups (`apt install gap`).
Команды запускаются из этой папки.

```bash
# таблица конечных групп до порядка 100 (около часа на 4 ядрах)
python3 -m algen.finite --до 100

# проверка всех правил раздела групп на этой таблице
node ../tools/dump-rules.mjs grp > /tmp/grp-rules.json
python3 -m algen.check_rules /tmp/grp-rules.json
```

`data/finite/grp-small.jsonl` лежит в репозитории готовым, поэтому для проверки
правил GAP не нужен.
