# Свойства конечных групп библиотеки, которых не было в таблице: ранг d(G),
# двупорождённость, обратная теорема Лагранжа, дедекиндовость, простые порядки
# элементов, свойства всех собственных подгрупп, метабелевость, G′ ⩽ Z(G),
# экспонента.
#
# Вызов: gap -q -o 8g props2.g с KEYS и OUT (см. finite.py, «--свойства2»).
# Строка: {"key": "n:i", "rank": d, "rank_exact": true|false, "two-generated": …,
#   "clt": …, "dedekind": …, "prime-orders": …, "proper-subs-abelian": …,
#   "proper-subs-nilpotent": …, "proper-subs-cyclic": …, "metabelian": …,
#   "class-2": …, "exponent": e, "exponent-4": …, "exponent-6": …}
# rank_exact = false — найдено только порождающее множество (верхняя оценка) и
# нижняя оценка не совпала: тогда "rank" — null, "rank_le": верхняя оценка.

Key := G -> Concatenation(String(Size(G)), ":", String(IdGroup(G)[2]));
B := b -> ShallowCopy(String(b));

# Нижняя оценка d(G): ранг абелианизации (наибольшее число инвариантов при одном p).
AbLower := function(G)
  local inv, ps;
  inv := AbelianInvariants(G);
  inv := Filtered(inv, x -> x > 1);
  if inv = [] then return 0; fi;
  ps := Set(Flat(List(inv, x -> Set(Factors(x)))));
  return Maximum(List(ps, p -> Number(inv, x -> x mod p = 0)));
end;

Rank := function(G)
  local lb, k, i, gens;
  if IsTrivial(G) then return [0, true]; fi;
  if IsCyclic(G) then return [1, true]; fi;
  if IsSolvableGroup(G) then return [Length(MinimalGeneratingSet(G)), true]; fi;
  lb := Maximum(2, AbLower(G));
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
  return [Length(MinimalGeneratingSet(G)), true];
end;

Record1 := function(G, out)
  local n, cls, ords, ded, r, sizes, mx, e, s;
  n := Size(G);
  cls := ConjugacyClasses(G);
  ords := Set(List(cls, c -> Order(Representative(c))));
  ded := ForAll(cls, c -> IsNormal(G, Subgroup(G, [Representative(c)])));
  r := Rank(G);
  sizes := Set(List(ConjugacyClassesSubgroups(G), c -> Size(Representative(c))));
  if n = 1 then mx := []; else mx := MaximalSubgroupClassReps(G); fi;
  e := Exponent(G);
  s := Concatenation("{\"key\":\"", Key(G), "\"");
  if r[2] then
    Append(s, Concatenation(",\"rank\":", String(r[1]), ",\"rank_exact\":true",
                            ",\"two-generated\":", B(r[1] <= 2)));
  else
    Append(s, Concatenation(",\"rank\":null,\"rank_exact\":false,\"rank_le\":", String(r[1])));
    if r[1] <= 2 then Append(s, ",\"two-generated\":true"); fi;
  fi;
  Append(s, Concatenation(
    ",\"clt\":", B(ForAll(DivisorsInt(n), d -> d in sizes)),
    ",\"dedekind\":", B(ded),
    ",\"prime-orders\":", B(ForAll(ords, o -> o = 1 or IsPrimeInt(o))),
    ",\"proper-subs-abelian\":", B(ForAll(mx, IsAbelian)),
    ",\"proper-subs-nilpotent\":", B(ForAll(mx, IsNilpotentGroup)),
    ",\"proper-subs-cyclic\":", B(ForAll(mx, IsCyclic)),
    ",\"metabelian\":", B(IsSolvableGroup(G) and DerivedLength(G) <= 2),
    ",\"class-2\":", B(IsSubgroup(Centre(G), DerivedSubgroup(G))),
    ",\"exponent\":", String(e),
    ",\"exponent-4\":", B(4 mod e = 0),
    ",\"exponent-6\":", B(6 mod e = 0), "}\n"));
  AppendTo(out, s);
end;

STREAM := OutputTextFile(OUT, false);
SetPrintFormattingStatus(STREAM, false);
for k in KEYS do Record1(SmallGroup(k[1], k[2]), STREAM); od;
CloseStream(STREAM);
QUIT;
