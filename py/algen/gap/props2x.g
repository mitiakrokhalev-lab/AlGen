# props2 для построенных конечных групп библиотеки (Aut, Out, G′, /Z, /Φ от малых групп
# и их композиции), которых нет в таблице малых групп (этап 2а.3, 8.11).
# Вызов: gap -q -o 8g props2x.g с JOBS (список [ключ, выражение GAP]) и OUT.
# Строка — как в props2.g, ключ — ключ библиотеки.

OnBreak := function() FORCE_QUIT_GAP(1); end;

OutGroup := function(A)
  return Image(NaturalHomomorphismByNormalSubgroup(A, InnerAutomorphismsAutomorphismGroup(A)));
end;
QuotientBy := function(G, N)
  return Image(NaturalHomomorphismByNormalSubgroup(G, N));
end;
AsPc := function(G)
  if IsSolvableGroup(G) and not IsPcGroup(G) then
    return Image(IsomorphismPcGroup(G));
  fi;
  if not IsPermGroup(G) and not IsPcGroup(G) then
    return Image(IsomorphismPermGroup(G));
  fi;
  return G;
end;

P2Key := G -> Concatenation(String(Size(G)), ":", String(IdGroup(G)[2]));
P2B := b -> ShallowCopy(String(b));

# Нижняя оценка d(G): ранг абелианизации (наибольшее число инвариантов при одном p).
P2AbLower := function(G)
  local inv, ps;
  inv := AbelianInvariants(G);
  inv := Filtered(inv, x -> x > 1);
  if inv = [] then return 0; fi;
  ps := Set(Flat(List(inv, x -> Set(Factors(x)))));
  return Maximum(List(ps, p -> Number(inv, x -> x mod p = 0)));
end;

P2Rank := function(G)
  local lb, k, i, gens;
  if IsTrivial(G) then return [0, true]; fi;
  if IsCyclic(G) then return [1, true]; fi;
  if IsSolvableGroup(G) then return [Length(MinimalGeneratingSet(G)), true]; fi;
  lb := Maximum(2, P2AbLower(G));
  # неразрешимая: ищем порождающее множество из lb элементов случайно
  for k in [lb .. lb + 2] do
    for i in [1 .. 3000] do
      gens := List([1 .. k], j -> PseudoRandom(G));
      if Size(Subgroup(G, gens)) = Size(G) then
        if k = lb then return [k, true]; fi;
        return [k, false];
      fi;
    od;
  od;
  return [fail, false];  # не нашли: ранг неизвестен (MinimalGeneratingSet для неразрешимых не зовём)
end;

P2Record := function(G, out, key)
  local n, cls, ords, ded, r, sizes, mx, e, s;
  n := Size(G);
  cls := ConjugacyClasses(G);
  ords := Set(List(cls, c -> Order(Representative(c))));
  ded := ForAll(cls, c -> IsNormal(G, Subgroup(G, [Representative(c)])));
  r := P2Rank(G);
  sizes := Set(List(ConjugacyClassesSubgroups(G), c -> Size(Representative(c))));
  if n = 1 then mx := []; else mx := MaximalSubgroupClassReps(G); fi;
  e := Exponent(G);
  s := Concatenation("{\"key\":\"", key, "\"");
  if r[2] then
    Append(s, Concatenation(",\"rank\":", String(r[1]), ",\"rank_exact\":true",
                            ",\"two-generated\":", P2B(r[1] <= 2)));
  elif r[1] = fail then
    Append(s, ",\"rank\":null,\"rank_exact\":false");
  else
    Append(s, Concatenation(",\"rank\":null,\"rank_exact\":false,\"rank_le\":", String(r[1])));
  fi;
  Append(s, Concatenation(
    ",\"clt\":", P2B(ForAll(DivisorsInt(n), d -> d in sizes)),
    ",\"dedekind\":", P2B(ded),
    ",\"prime-orders\":", P2B(ForAll(ords, o -> o = 1 or IsPrimeInt(o))),
    ",\"proper-subs-abelian\":", P2B(ForAll(mx, IsAbelian)),
    ",\"proper-subs-nilpotent\":", P2B(ForAll(mx, IsNilpotentGroup)),
    ",\"proper-subs-cyclic\":", P2B(ForAll(mx, IsCyclic)),
    ",\"metabelian\":", P2B(IsSolvableGroup(G) and DerivedLength(G) <= 2),
    ",\"class-2\":", P2B(IsSubgroup(Centre(G), DerivedSubgroup(G))),
    ",\"exponent\":", String(e),
    ",\"exponent-4\":", P2B(4 mod e = 0),
    ",\"exponent-6\":", P2B(6 mod e = 0), "}\n"));
  AppendTo(out, s);
end;


STREAM := OutputTextFile(OUT, false);
SetPrintFormattingStatus(STREAM, false);
QZ := X -> QuotientBy(X, Centre(X));
QF := X -> QuotientBy(X, FrattiniSubgroup(X));
for j in JOBS do
  G := AsPc(EvalString(j[2]));
  if Size(G) <> Int(SplitString(j[1], ":")[1]) then
    AppendTo(STREAM, Concatenation("{\"key\":\"", j[1], "\",\"skipped\":true,\"reason\":\"order\"}\n"));
  else
    P2Record(G, STREAM, j[1]);
  fi;
od;
CloseStream(STREAM);
QUIT;
