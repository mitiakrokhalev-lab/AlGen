# Перестановочность представителей классов подгрупп конечных групп таблицы.
#
# HK = KH ⇔ |⟨H, K⟩| = |H||K| / |H ∩ K|. Представители — Representative(c) для
# c в ConjugacyClassesSubgroups (как в groups.g и elts.g); пара с нормальной
# подгруппой перестановочна всегда и не считается.
#
# Вызов: gap -q -o 8g perm.g с KEYS и OUT (см. finite.py, «--перестановочность»).
# Строка вывода: {"key": "n:i", "nonperm": [[i, j], …], "check": [[тип, размер класса], …]}
# (пары номеров классов i < j, чьи представители не перестановочны), или
# "nonperm": null, если классов подгрупп больше MAXCLASSES.

if not IsBound(MAXCLASSES) then MAXCLASSES := 300; fi;
Key := G -> Concatenation(String(Size(G)), ":", String(IdGroup(G)[2]));

Record1 := function(G, out)
  local scls, reps, nrm, s, i, j, first, H, K;
  if Length(LatticeSubgroups(G)!.conjugacyClassesSubgroups) > MAXCLASSES then
    AppendTo(out, Concatenation("{\"key\":\"", Key(G), "\",\"nonperm\":null}\n"));
    return;
  fi;
  scls := ConjugacyClassesSubgroups(G);
  reps := List(scls, Representative);
  nrm := List(scls, c -> Size(c) = 1);
  s := Concatenation("{\"key\":\"", Key(G), "\",\"nonperm\":[");
  first := true;
  for i in [1..Length(reps)] do
    for j in [i + 1..Length(reps)] do
      if nrm[i] or nrm[j] then continue; fi;
      H := reps[i]; K := reps[j];
      if Size(ClosureGroup(H, K)) * Size(Intersection(H, K)) <> Size(H) * Size(K) then
        if not first then Append(s, ","); fi;
        first := false;
        Append(s, Concatenation("[", String(i - 1), ",", String(j - 1), "]"));
      fi;
    od;
  od;
  Append(s, "],\"check\":[");
  for i in [1..Length(scls)] do
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
