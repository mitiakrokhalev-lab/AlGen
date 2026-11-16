# Дополняемость подгрупп конечных групп таблицы: для каждого класса
# сопряжённых подгрупп N (в порядке ConjugacyClassesSubgroups, как в groups.g) —
# есть ли B ⩽ G с N ∩ B = 1 и |N|·|B| = |G| (тогда NB = G).
#
# Вызов: gap -q -o 8g compl.g с KEYS и OUT (см. finite.py, «--дополнения»).
# Строка вывода: {"key": "n:i", "complemented": [true, false, …]} или null,
# если классов больше MAXCLASSES.

if not IsBound(MAXCLASSES) then MAXCLASSES := 300; fi;
Key := G -> Concatenation(String(Size(G)), ":", String(IdGroup(G)[2]));

Complemented := function(G, N, reps)
  local B, m, D, d;
  m := Size(G) / Size(N);
  for B in Filtered(reps, B -> Size(B) = m) do
    # нужен сопряжённый B^g с N ∩ B^g = 1; перебираем по двойным смежным классам N\G/B
    for D in DoubleCosetRepsAndSizes(G, N, B) do
      d := D[1];
      if Size(Intersection(N, B^d)) = 1 then return true; fi;
    od;
  od;
  return false;
end;

Record1 := function(G, out)
  local cls, reps, s, i;
  if Length(LatticeSubgroups(G)!.conjugacyClassesSubgroups) > MAXCLASSES then
    AppendTo(out, Concatenation("{\"key\":\"", Key(G), "\",\"complemented\":null}\n"));
    return;
  fi;
  cls := ConjugacyClassesSubgroups(G);
  reps := List(cls, Representative);
  s := Concatenation("{\"key\":\"", Key(G), "\",\"complemented\":[");
  for i in [1..Length(reps)] do
    if i > 1 then Append(s, ","); fi;
    Append(s, ShallowCopy(String(Complemented(G, reps[i], reps))));
  od;
  # для сверки с groups.g: тип и размер класса каждой подгруппы
  Append(s, "],\"check\":[");
  for i in [1..Length(reps)] do
    if i > 1 then Append(s, ","); fi;
    Append(s, Concatenation("[\"", Key(reps[i]), "\",", String(Size(cls[i])), "]"));
  od;
  Append(s, "]}\n");
  AppendTo(out, s);
end;

STREAM := OutputTextFile(OUT, false);
SetPrintFormattingStatus(STREAM, false);
for k in KEYS do Record1(SmallGroup(k[1], k[2]), STREAM); od;
CloseStream(STREAM);
QUIT;
