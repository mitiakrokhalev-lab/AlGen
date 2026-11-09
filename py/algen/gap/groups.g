# Данные о конечных группах для AlGen: свойства группы, классы сопряжённых
# подгрупп, свойства вложения, факторы и канонические подгруппы.
#
# Вызов: gap -q -o 4g groups.g  с переменными LO, HI, OUT, заданными заранее
# (см. py/algen/finite.py). Каждая строка вывода — один JSON-объект.
#
# Группа называется ключом "n:i" = SmallGroup(n, i). Подгруппы и факторы
# ссылаются на группу по такому же ключу, поэтому свойства подгруппы как
# группы не дублируются, а берутся из её собственной записи.

if not IsBound(MAXCLASSES) then MAXCLASSES := 300; fi;

Key := G -> Concatenation(String(Size(G)), ":", String(IdGroup(G)[2]));

B := b -> ShallowCopy(String(b));   # true/false как в JSON

ObjProps := function(G)
  local n;
  n := Size(G);
  return [
    ["trivial", n = 1],
    ["abelian", IsAbelian(G)],
    ["cyclic", IsCyclic(G)],
    ["finite", true],
    ["fin-gen", true],
    ["free", n = 1],
    ["simple", n > 1 and IsSimpleGroup(G)],
    ["solvable", IsSolvableGroup(G)],
    ["nilpotent", IsNilpotentGroup(G)],
    ["perfect", IsPerfectGroup(G)],
    ["torsion-free", n = 1],
    ["periodic", true],
    ["divisible", n = 1],
    ["centerless", Size(Centre(G)) = 1],
    ["residually-finite", true],
    ["indecomposable", n = 1 or Length(DirectFactorsOfGroup(G)) = 1]
  ];
end;

JsonProps := function(ps)
  local s, i;
  s := "{";
  for i in [1..Length(ps)] do
    if i > 1 then Append(s, ","); fi;
    Append(s, Concatenation("\"", ps[i][1], "\":", B(ps[i][2])));
  od;
  Append(s, "}");
  return s;
end;

JsonList := function(l)
  local s, i;
  s := "[";
  for i in [1..Length(l)] do
    if i > 1 then Append(s, ","); fi;
    if IsString(l[i]) then Append(s, Concatenation("\"", l[i], "\""));
    else Append(s, String(l[i])); fi;
  od;
  Append(s, "]");
  return s;
end;

Record1 := function(G, out)
  local cls, reps, ClassOf, maxs, Z, D, F, A, s, i, N, Q, inner, props, ismax;
  if MAXCLASSES > 0 and Length(LatticeSubgroups(G)!.conjugacyClassesSubgroups) > MAXCLASSES then
    # Слишком много классов подгрупп (так у элементарных абелевых 2-групп):
    # группа идёт в таблицу только свойствами, без подгрупп. Читатель
    # таблицы видит "subs": null и не выдаёт такие привязки за проверенные.
    AppendTo(out, Concatenation("{\"key\":\"", Key(G), "\",\"order\":", String(Size(G)),
      ",\"name\":\"", StructureDescription(G), "\",\"props\":", JsonProps(ObjProps(G)),
      ",\"subs\":null}\n"));
    return;
  fi;
  cls := ConjugacyClassesSubgroups(G);
  reps := List(cls, Representative);
  ClassOf := function(H)
    local j;
    for j in [1..Length(reps)] do
      if Size(reps[j]) = Size(H) and H in cls[j] then return j - 1; fi;
    od;
    Error("class not found");
  end;
  maxs := List(MaximalSubgroupClassReps(G), ClassOf);
  Z := Centre(G); D := DerivedSubgroup(G); F := FrattiniSubgroup(G);
  A := AutomorphismGroup(G);
  s := Concatenation("{\"key\":\"", Key(G), "\",\"order\":", String(Size(G)),
    ",\"name\":\"", StructureDescription(G), "\",\"props\":", JsonProps(ObjProps(G)),
    ",\"center\":", String(ClassOf(Z)), ",\"commutator\":", String(ClassOf(D)),
    ",\"frattini\":", String(ClassOf(F)), ",\"aut_order\":", String(Size(A)),
    ",\"subs\":[");
  for i in [1..Length(reps)] do
    N := reps[i];
    if i > 1 then Append(s, ","); fi;
    ismax := (i - 1) in maxs;
    props := [
      ["normal", IsNormal(G, N)],
      ["characteristic", IsNormal(G, N) and IsCharacteristicSubgroup(G, N)],
      ["maximal", ismax],
      ["whole", Size(N) = Size(G)],
      ["central", IsSubset(Z, N)],
      ["finite-index", true]
    ];
    Append(s, Concatenation("{\"group\":\"", Key(N), "\",\"index\":",
      String(Index(G, N)), ",\"class_size\":", String(Size(cls[i])),
      ",\"props\":", JsonProps(props)));
    if IsNormal(G, N) then
      Q := Image(NaturalHomomorphismByNormalSubgroup(G, N));
      Append(s, Concatenation(",\"quotient\":\"", Key(Q), "\""));
    fi;
    Append(s, Concatenation(",\"normalizer\":", String(ClassOf(Normalizer(G, N))),
      ",\"centralizer\":", String(ClassOf(Centralizer(G, N))),
      ",\"core\":", String(ClassOf(Core(G, N))),
      ",\"normal_closure\":", String(ClassOf(NormalClosure(G, N))),
      ",\"le\":", JsonList(Filtered([0..Length(reps) - 1], j -> Size(reps[j + 1]) mod Size(N) = 0 and IsSubset(reps[j + 1], N))), "}"));
  od;
  Append(s, "]}\n");
  AppendTo(out, s);
end;

STREAM := OutputTextFile(OUT, false);
SetPrintFormattingStatus(STREAM, false);
if IsBound(KEYS) then
  # Отдельные группы порядка выше таблицы: KEYS = [[n, i], ...].
  for k in KEYS do Record1(SmallGroup(k[1], k[2]), STREAM); od;
else
  for n in [LO..HI] do
    for i in [1..NrSmallGroups(n)] do
      Record1(SmallGroup(n, i), STREAM);
    od;
  od;
fi;
CloseStream(STREAM);
QUIT;
