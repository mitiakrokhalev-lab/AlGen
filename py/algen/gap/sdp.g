# Полупрямые произведения N ⋊_φ Q для пар групп SmallGroup с |N|, |Q| ⩽ HI
# и |N|·|Q| ⩽ 100 (больше в таблице конечных групп почти ничего нет):
# для каждого класса гомоморфизмов φ : Q → Aut(N) (с точностью до сопряжения
# в Aut(N)) — ключ N ⋊_φ Q. В записи — различные ключи, первый — N × Q
# (тривиальное действие). Переменные HI и OUT задаются заранее (см. py/algen/finite.py).

Key := G -> Concatenation(String(Size(G)), ":", String(IdGroup(G)[2]));
STREAM := OutputTextFile(OUT, false);
SetPrintFormattingStatus(STREAM, false);
keys := Concatenation(List([1..HI], n -> List([1..NrSmallGroups(n)], i -> [n, i])));
for x in keys do
  N := SmallGroup(x[1], x[2]);
  A := AutomorphismGroup(N);
  for y in Filtered(keys, y -> x[1] * y[1] <= 100) do
    Q := SmallGroup(y[1], y[2]);
    out := [Key(DirectProduct(N, Q))];  # тривиальное действие — первым
    for f in AllHomomorphismClasses(Q, A) do
      k := Key(SemidirectProduct(Q, f, N));
      if not k in out then Add(out, k); fi;
    od;
    AppendTo(STREAM, Concatenation("{\"N\":\"", String(x[1]), ":", String(x[2]),
      "\",\"Q\":\"", String(y[1]), ":", String(y[2]), "\",\"semi\":[",
      JoinStringsWithSeparator(List(out, k -> Concatenation("\"", k, "\"")), ","), "]}\n"));
  od;
od;
CloseStream(STREAM);
QUIT;
