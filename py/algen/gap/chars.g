# Характеристические подгруппы и Aut/Out конечных групп без полной таблицы
# подгрупп (порядок > 100: SmallGroup вне таблицы и образы Aut/Out малых групп).
#
# Вызов: gap -q -o 8g chars.g с заранее заданными JOBS (список [ключ, n, i, вид],
# вид — "G", "Aut" или "Out" от SmallGroup(n, i)) и OUT (см. finite.py, «--характеристические»).
# Строка вывода — JSON:
#   key; subs — подгруппы 1, Z(G), G′, Φ(G), G без повторов: порядок, ключ (n:i или null),
#   свойства как группы, свойства вложения, порядок и ключ фактора, свойства фактора, над (номера);
#   center, commutator, frattini — номера в subs; aut/out — как в aut.g.

B := b -> ShallowCopy(String(b));
KeyOrNull := function(G)
  if IdGroupsAvailable(Size(G)) then
    return Concatenation("\"", String(Size(G)), ":", String(IdGroup(G)[2]), "\"");
  fi;
  return "null";
end;

Props := function(G)
  local n, ps;
  n := Size(G);
  ps := [
    ["trivial", n = 1], ["abelian", IsAbelian(G)], ["cyclic", IsCyclic(G)],
    ["finite", true], ["fin-gen", true], ["free", n = 1],
    ["simple", n > 1 and IsSimpleGroup(G)], ["solvable", IsSolvableGroup(G)],
    ["nilpotent", IsNilpotentGroup(G)], ["perfect", IsPerfectGroup(G)],
    ["torsion-free", n = 1], ["periodic", true], ["divisible", n = 1],
    ["centerless", Size(Centre(G)) = 1], ["residually-finite", true],
    ["exponent-2", Exponent(G) in [1, 2]], ["exponent-3", Exponent(G) in [1, 3]],
    ["exponent-4", 4 mod Exponent(G) = 0], ["exponent-6", 6 mod Exponent(G) = 0]
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

Build := function(job)
  local H, A, P, I;
  H := SmallGroup(job[2], job[3]);
  if job[4] = "G" then return H; fi;
  A := AutomorphismGroup(H);
  P := Image(IsomorphismPermGroup(A));
  if job[4] = "Aut" then return P; fi;
  I := Image(IsomorphismPermGroup(A), InnerAutomorphismsAutomorphismGroup(A));
  return Image(SmallerDegreePermutationRepresentation(Image(NaturalHomomorphismByNormalSubgroup(P, I))));
end;

Record1 := function(job, out)
  local G, Z, D, F, list, idx, s, i, j, H, Q, hom, A, P, I, O, first;
  G := Build(job);
  if IsPermGroup(G) and Size(G) <= 50000 and IsSolvableGroup(G) then
    G := Image(IsomorphismPcGroup(G));
  fi;
  Z := Centre(G); D := DerivedSubgroup(G); F := FrattiniSubgroup(G);
  list := [TrivialSubgroup(G)];
  for H in [Z, D, F, G] do
    if not ForAny(list, X -> X = H) then Add(list, H); fi;
  od;
  idx := H -> PositionProperty(list, X -> X = H) - 1;
  s := Concatenation("{\"key\":\"", job[1], "\",\"order\":", String(Size(G)), ",\"subs\":[");
  for i in [1..Length(list)] do
    H := list[i];
    hom := NaturalHomomorphismByNormalSubgroup(G, H);
    Q := Image(hom);
    if i > 1 then Append(s, ","); fi;
    Append(s, Concatenation("{\"order\":", String(Size(H)), ",\"group\":", KeyOrNull(H),
      ",\"gprops\":", JsonProps(Props(H)),
      ",\"props\":{\"normal\":true,\"characteristic\":true,\"maximal\":", B(Size(Q) > 1 and IsSimpleGroup(Q)),
      ",\"whole\":", B(Size(H) = Size(G)), ",\"central\":", B(IsSubset(Z, H)), ",\"finite-index\":true}",
      ",\"qorder\":", String(Size(Q)), ",\"quotient\":", KeyOrNull(Q), ",\"qprops\":", JsonProps(Props(Q)),
      ",\"le\":["));
    first := true;
    for j in [1..Length(list)] do
      if IsSubset(list[j], H) then
        if not first then Append(s, ","); fi;
        Append(s, String(j - 1)); first := false;
      fi;
    od;
    Append(s, "]}");
  od;
  Append(s, Concatenation("],\"center\":", String(idx(Z)), ",\"commutator\":", String(idx(D)),
    ",\"frattini\":", String(idx(F))));
  if Size(G) <= 20000 then
    A := AutomorphismGroup(G);
    P := Image(IsomorphismPermGroup(A));
    I := Image(IsomorphismPermGroup(A), InnerAutomorphismsAutomorphismGroup(A));
    O := P / I;
    Append(s, Concatenation(",\"aut_order\":", String(Size(P)), ",\"aut\":", KeyOrNull(P),
      ",\"aut_props\":", JsonProps(Props(P)), ",\"inn_whole\":", B(Size(I) = Size(P)),
      ",\"inn_central\":", B(IsSubset(Centre(P), I)), ",\"out_order\":", String(Size(O)),
      ",\"out\":", KeyOrNull(O), ",\"out_props\":", JsonProps(Props(O))));
  fi;
  Append(s, "}\n");
  AppendTo(out, s);
end;

STREAM := OutputTextFile(OUT, false);
SetPrintFormattingStatus(STREAM, false);
for job in JOBS do Record1(job, STREAM); od;
CloseStream(STREAM);
QUIT;
