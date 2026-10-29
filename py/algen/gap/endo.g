# Вполне инвариантные подгруппы конечных групп таблицы: для каждого класса
# сопряжённых подгрупп H (в порядке ConjugacyClassesSubgroups, как в groups.g) —
# φ(H) ⩽ H для всех эндоморфизмов φ группы G.
#
# Абелева G: End(G) аддитивно порождён отображениями e_ij (x_j ↦ x_i^k,
# k = |x_i| / НОД(|x_i|, |x_j|), прочие образующие ↦ 1) по независимым образующим,
# поэтому хватает проверить их. Неабелева: представители AllHomomorphismClasses
# (с точностью до внутренних автоморфизмов образа; для нормальных H этого хватает,
# ненормальная подгруппа не вполне инвариантна).
#
# Вызов: gap -q -o 8g endo.g с KEYS и OUT (см. finite.py, «--эндоморфизмы»).
# Строка вывода: {"key": "n:i", "fully_invariant": [true, …], "end_classes": m,
# "check": [[тип, размер класса], …]} или null вместо списка, если группа велика.

if not IsBound(MAXCLASSES) then MAXCLASSES := 300; fi;
if not IsBound(MAXNONAB) then MAXNONAB := 512; fi;
Key := G -> Concatenation(String(Size(G)), ":", String(IdGroup(G)[2]));

AbelianEndGens := function(G)
  local gens, o, maps, i, j, imgs;
  gens := IndependentGeneratorsOfAbelianGroup(G);
  o := List(gens, Order);
  maps := [];
  for i in [1..Length(gens)] do
    for j in [1..Length(gens)] do
      imgs := List(gens, x -> One(G));
      imgs[j] := gens[i]^(o[i] / Gcd(o[i], o[j]));
      Add(maps, GroupHomomorphismByImagesNC(G, G, gens, imgs));
    od;
  od;
  return maps;
end;

Record1 := function(G, out)
  local cls, reps, maps, s, i, H, ok, f;
  if Length(LatticeSubgroups(G)!.conjugacyClassesSubgroups) > MAXCLASSES
     or (not IsAbelian(G) and Size(G) > MAXNONAB) then
    AppendTo(out, Concatenation("{\"key\":\"", Key(G), "\",\"fully_invariant\":null}\n"));
    return;
  fi;
  cls := ConjugacyClassesSubgroups(G);
  reps := List(cls, Representative);
  if IsAbelian(G) then
    maps := AbelianEndGens(G);
  else
    maps := AllHomomorphismClasses(G, G);
  fi;
  s := Concatenation("{\"key\":\"", Key(G), "\",\"end_classes\":", String(Length(maps)),
                     ",\"fully_invariant\":[");
  for i in [1..Length(reps)] do
    H := reps[i];
    ok := Size(cls[i]) = 1;
    if ok then
      for f in maps do
        if not IsSubset(H, Image(f, H)) then ok := false; break; fi;
      od;
    fi;
    if i > 1 then Append(s, ","); fi;
    Append(s, ShallowCopy(String(ok)));
  od;
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
