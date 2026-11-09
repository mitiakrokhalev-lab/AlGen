# H ∩ K, ⟨H, K⟩ и [H, K] для пар представителей классов подгрупп конечных групп таблицы.
#
# Представители — Representative(c) для c в ConjugacyClassesSubgroups (как в groups.g).
# Для пары i ⩽ j (номера классов с 0) пишутся три числа: класс H ∩ K, ⟨H, K⟩ и [H, K].
# Число c ⩾ 0 значит, что результат — ровно представитель класса c (или класс c
# состоит из одной подгруппы); −c − 1 — что результат лежит в классе c, но не
# совпадает с его представителем.
#
# Вызов: gap -q -o 8g hk.g с KEYS и OUT (см. finite.py, «--пересечения»).
# Строка вывода: {"key": "n:i", "hk": [m, j, c, m, j, c, …] по парам (0,0), (0,1), …, (0,n−1), (1,1), …,
# "check": [[тип, размер класса], …]}, или "hk": null, если классов больше MAXCLASSES.

if not IsBound(MAXCLASSES) then MAXCLASSES := 100; fi;
Key := G -> Concatenation(String(Size(G)), ":", String(IdGroup(G)[2]));

Record1 := function(G, out)
  local scls, reps, n, s, i, j, first, H, K, Find, bysize;
  if Length(LatticeSubgroups(G)!.conjugacyClassesSubgroups) > MAXCLASSES then
    AppendTo(out, Concatenation("{\"key\":\"", Key(G), "\",\"hk\":null}\n"));
    return;
  fi;
  scls := ConjugacyClassesSubgroups(G);
  reps := List(scls, Representative);
  n := Length(reps);
  Find := function(X)
    local c;
    for c in [1..n] do
      if Size(reps[c]) = Size(X) then
        if X = reps[c] then return c - 1; fi;
        if Size(scls[c]) > 1 and X in scls[c] then return -c; fi;
      fi;
    od;
    Error("класс не найден");
  end;
  s := Concatenation("{\"key\":\"", Key(G), "\",\"hk\":[");
  first := true;
  for i in [1..n] do
    for j in [i..n] do
      H := reps[i]; K := reps[j];
      if not first then Append(s, ","); fi;
      first := false;
      Append(s, Concatenation(String(Find(Intersection(H, K))), ",", String(Find(ClosureGroup(H, K))), ",",
                              String(Find(CommutatorSubgroup(H, K)))));
    od;
  od;
  Append(s, "],\"check\":[");
  for i in [1..n] do
    if i > 1 then Append(s, ","); fi;
    Append(s, Concatenation("[\"", Key(Representative(scls[i])), "\",", String(Size(scls[i])), "]"));
  od;
  Append(s, "]}\n");
  AppendTo(out, s);
end;

STREAM := OutputTextFile(OUT, false);
SetPrintFormattingStatus(STREAM, false);
for k in KEYS do Record1(SmallGroup(k[1], k[2]), STREAM); od;
CloseStream(STREAM);
QUIT;
