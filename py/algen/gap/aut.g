# Группы автоморфизмов конечных групп таблицы: Aut(G), Inn(G), Out(G).
#
# Вызов: gap -q -o 8g aut.g  с переменными KEYS (список [n, i]) и OUT, заданными
# заранее (см. py/algen/finite.py, команда «авт»). Строка вывода — JSON:
#   key, aut_order, aut (ключ "n:i" или null, если IdGroup недоступен),
#   aut_props (свойства Aut(G) как группы), inn_whole (Inn = Aut),
#   inn_central (Inn ⩽ Z(Aut)), out_order, out (ключ Out(G) или null), out_props.

Key := G -> Concatenation(String(Size(G)), ":", String(IdGroup(G)[2]));
B := b -> ShallowCopy(String(b));
KeyOrNull := function(G)
  if IdGroupsAvailable(Size(G)) then return Concatenation("\"", Key(G), "\""); fi;
  return "null";
end;

Props := function(G)
  local n, ps;
  n := Size(G);
  ps := [
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
    ["residually-finite", true]
  ];
  if n <= 100000 then
    Add(ps, ["indecomposable", n = 1 or Length(DirectFactorsOfGroup(G)) = 1]);
  fi;
  return ps;
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

AutName := function(P)
  if Size(P) <= 100000 then return StructureDescription(P); fi;
  return Concatenation("order ", String(Size(P)));
end;

Record1 := function(G, out)
  local A, P, I, O, s;
  A := AutomorphismGroup(G);
  P := Image(IsomorphismPermGroup(A));
  I := Image(IsomorphismPermGroup(A), InnerAutomorphismsAutomorphismGroup(A));
  O := P / I;
  s := Concatenation("{\"key\":\"", Key(G), "\",\"aut_order\":", String(Size(P)),
    ",\"aut\":", KeyOrNull(P), ",\"aut_name\":\"", AutName(P), "\"",
    ",\"aut_props\":", JsonProps(Props(P)),
    ",\"inn_whole\":", B(Size(I) = Size(P)),
    ",\"inn_central\":", B(IsSubset(Centre(P), I)),
    ",\"out_order\":", String(Size(O)), ",\"out\":", KeyOrNull(O),
    ",\"out_props\":", JsonProps(Props(O)), "}\n");
  AppendTo(out, s);
end;

STREAM := OutputTextFile(OUT, false);
SetPrintFormattingStatus(STREAM, false);
for k in KEYS do Record1(SmallGroup(k[1], k[2]), STREAM); od;
CloseStream(STREAM);
QUIT;
