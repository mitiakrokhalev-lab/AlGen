# Прямые произведения в таблице конечных групп: для каждой пары групп
# SmallGroup(a), SmallGroup(b) с |a|·|b| ⩽ HI — ключ их произведения.
# Переменные HI и OUT задаются заранее (см. py/algen/finite.py).

Key := G -> Concatenation(String(Size(G)), ":", String(IdGroup(G)[2]));
STREAM := OutputTextFile(OUT, false);
SetPrintFormattingStatus(STREAM, false);
keys := Concatenation(List([1..HI], n -> List([1..NrSmallGroups(n)], i -> [n, i])));
for x in keys do
  for y in keys do
    if x <= y and x[1] * y[1] <= HI then
      AppendTo(STREAM, Concatenation("{\"a\":\"", String(x[1]), ":", String(x[2]),
        "\",\"b\":\"", String(y[1]), ":", String(y[2]), "\",\"prod\":\"",
        Key(DirectProduct(SmallGroup(x[1], x[2]), SmallGroup(y[1], y[2]))), "\"}\n"));
    fi;
  od;
od;
CloseStream(STREAM);
QUIT;
