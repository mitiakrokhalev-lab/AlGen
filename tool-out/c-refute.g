
BreakOnError := false;  # ошибка в предикате — в CALL_WITH_CATCH, не в цикл прерывания
QuotientBy := function(X, N) return Image(NaturalHomomorphismByNormalSubgroup(X, N)); end;
OutP := function(X) local A;
  A := AutomorphismGroup(X);
  return Image(IsomorphismPermGroup(QuotientBy(A, InnerAutomorphismsAutomorphismGroup(A))));
end;
OrderPQ := function(n) local f; f := Factors(n); return Length(f) = 2 and f[1] <> f[2]; end;
OrderP2 := function(n) local f; f := Factors(n); return Length(f) = 2 and f[1] = f[2]; end;
PrimeOrders := X -> ForAll(ConjugacyClasses(X), c -> Order(Representative(c)) = 1 or IsPrimeInt(Order(Representative(c))));
MaxAll := function(X, test)
  if Size(X) = 1 then return true; fi;
  return ForAll(MaximalSubgroupClassReps(X), test);
end;
Indec := X -> Size(X) = 1 or Length(DirectFactorsOfGroup(X)) = 1;
IsoG := function(X, Y)
  if Size(X) <> Size(Y) then return false; fi;
  if Size(X) = 1 then return true; fi;
  if IdGroupsAvailable(Size(X)) then return IdGroup(X) = IdGroup(Y); fi;
  return IsomorphismGroups(X, Y) <> fail;
end;
EmbedsG := function(X, Y)
  if Size(X) = 1 then return true; fi;
  if Size(Y) mod Size(X) <> 0 then return false; fi;
  if Size(X) = Size(Y) then return IsoG(X, Y); fi;
  return IsomorphicSubgroups(Y, X) <> [];
end;
AutP := X -> Image(IsomorphismPermGroup(AutomorphismGroup(X)));
TwoGen := function(X)
  if Size(X) = 1 or IsCyclic(X) then return true; fi;
  if IsSolvableGroup(X) then return Length(MinimalGeneratingSet(X)) <= 2; fi;
  return Length(SmallGeneratingSet(X)) <= 2;  # верхняя оценка: «не 2-порождена» здесь — лишь кандидат
end;
CLT := X -> Set(List(ConjugacyClassesSubgroups(X), c -> Size(Representative(c)))) = DivisorsInt(Size(X));
InnQ := X -> QuotientBy(X, Centre(X));

P0 := function(G)
  local t1, t2, t3, t4;
  t1 := FrattiniSubgroup(G);
  if not (Size(Centre(t1)) = 1) then return false; fi;
  if not (IsOddInt(Size(G))) then return false; fi;
  t2 := QuotientBy(G, t1);
  if not not (Size(Centre(t2)) = 1) then return false; fi;
  t3 := Centre(G);
  t4 := QuotientBy(G, t3);
  if not not (Indec(t4)) then return false; fi;
  return true;
end;
P1 := function(G)
  local t1, t2, t3, t4;
  t1 := FrattiniSubgroup(G);
  t2 := QuotientBy(G, t1);
  if not (Size(Centre(t2)) = 1) then return false; fi;
  if not (IsOddInt(Size(G))) then return false; fi;
  t3 := Centre(G);
  t4 := QuotientBy(G, t3);
  if not not (IsoG(G, t4)) then return false; fi;
  if not not (MaxAll(t4, IsCyclic)) then return false; fi;
  return true;
end;
P2 := function(G)
  local t1, t2, t3, t4;
  if not (IsOddInt(Size(G))) then return false; fi;
  t1 := Centre(G);
  t2 := QuotientBy(G, t1);
  if not (IsPerfectGroup(t2)) then return false; fi;
  t3 := FrattiniSubgroup(G);
  if not not (IsCyclic(t3)) then return false; fi;
  t4 := QuotientBy(G, t3);
  if not not (IsoG(t3, t4)) then return false; fi;
  return true;
end;
P3 := function(G)
  local t1, t2;
  t1 := FrattiniSubgroup(G);
  if not (Gcd(Size(t1), Index(G, t1)) = 1) then return false; fi;
  if not (Indec(G)) then return false; fi;
  t2 := G;
  if not (IsOddInt(Size(t2))) then return false; fi;
  if not not (PrimeOrders(G)) then return false; fi;
  return true;
end;
P4 := function(G)
  local t1, t2;
  t1 := FrattiniSubgroup(G);
  if not (Gcd(Size(t1), Index(G, t1)) = 1) then return false; fi;
  t2 := G;
  if not (IsOddInt(Size(t2))) then return false; fi;
  if not not (IsAbelian(DerivedSubgroup(G))) then return false; fi;
  return true;
end;
P5 := function(G)
  local t1, t2, t3;
  t1 := FrattiniSubgroup(G);
  t2 := QuotientBy(G, t1);
  t3 := InnQ(t2);
  if not (EmbedsG(t2, t3)) then return false; fi;
  if not (IsOddInt(Size(G))) then return false; fi;
  if not not (2 mod Exponent(t1) = 0) then return false; fi;
  if not not (MaxAll(G, IsCyclic)) then return false; fi;
  return true;
end;
P6 := function(G)
  local t1, t2, t3, t4;
  t1 := FrattiniSubgroup(G);
  t2 := QuotientBy(G, t1);
  if not (Size(Centre(t2)) = 1) then return false; fi;
  t3 := DerivedSubgroup(G);
  t4 := QuotientBy(G, t3);
  if not (6 mod Exponent(t4) = 0) then return false; fi;
  if not (IsOddInt(Size(G))) then return false; fi;
  if not not (Size(Centre(G)) = 1) then return false; fi;
  return true;
end;
P8 := function(G)
  local t1, t2, t3, t4;
  t1 := DerivedSubgroup(G);
  t2 := QuotientBy(G, t1);
  if not (EmbedsG(t1, t2)) then return false; fi;
  if not (IsOddInt(Size(G))) then return false; fi;
  t3 := FrattiniSubgroup(G);
  if not not (Size(t3) = 1) then return false; fi;
  t4 := QuotientBy(G, t3);
  if not not (MaxAll(t4, IsNilpotentGroup)) then return false; fi;
  return true;
end;
P9 := function(G)
  local t1, t2, t3, t4;
  t1 := DerivedSubgroup(G);
  t2 := QuotientBy(G, t1);
  t3 := FrattiniSubgroup(G);
  t4 := QuotientBy(G, t3);
  if not (EmbedsG(t2, t4)) then return false; fi;
  if not (Indec(t2)) then return false; fi;
  if not (IsOddInt(Size(G))) then return false; fi;
  if not not (IsoG(G, t4)) then return false; fi;
  return true;
end;
P11 := function(G)
  local t1, t2, t3, t4;
  if not (2 mod Exponent(G) = 0) then return false; fi;
  t1 := FrattiniSubgroup(G);
  t2 := QuotientBy(G, t1);
  if not (IsCyclic(t2)) then return false; fi;
  if not not (Index(G, t1) = 2) then return false; fi;
  t3 := DerivedSubgroup(G);
  t4 := QuotientBy(G, t3);
  if not not (IsOddInt(Size(t4))) then return false; fi;
  return true;
end;
P13 := function(G)
  local t1, t2, t3;
  t1 := DerivedSubgroup(G);
  t2 := AutP(t1);
  if not (EmbedsG(t2, G)) then return false; fi;
  if not (IsOddInt(Size(G))) then return false; fi;
  t3 := InnQ(t1);
  if not not (IsoG(t2, t3)) then return false; fi;
  return true;
end;
P14 := function(G)
  local t1;
  if not (2 mod Exponent(G) = 0) then return false; fi;
  if not (TwoGen(G)) then return false; fi;
  t1 := AutP(G);
  if not not (OrderPQ(Size(t1))) then return false; fi;
  if not not (IsPrimeInt(Size(G))) then return false; fi;
  return true;
end;
P15 := function(G)
  local t1;
  if not (Size(G) = 1) then return false; fi;
  if not (true) then return false; fi;
  t1 := AutP(G);
  if not not (IsPrimeInt(Size(t1))) then return false; fi;
  if not not (IsPrimeInt(Size(G))) then return false; fi;
  return true;
end;
P16 := function(G)
  local t1;
  if not (Size(G) = 1) then return false; fi;
  if not (Indec(G)) then return false; fi;
  t1 := AutP(G);
  if not not (IsPrimeInt(Size(t1))) then return false; fi;
  if not not (IsPrimeInt(Size(G))) then return false; fi;
  return true;
end;
P19 := function(G)
  local t1, t2, t3, t4;
  t1 := OutP(G);
  t2 := Centre(t1);
  t3 := QuotientBy(t1, t2);
  t4 := InnQ(G);
  if not (EmbedsG(t3, t4)) then return false; fi;
  if not (IsOddInt(Size(G))) then return false; fi;
  if not (MaxAll(G, IsAbelian)) then return false; fi;
  if not not (MaxAll(t4, IsCyclic)) then return false; fi;
  return true;
end;
P20 := function(G)
  local t1, t2;
  t1 := DirectProduct(G, G);
  if not (IsAbelian(t1)) then return false; fi;
  t2 := t1;
  if not (Size(t2) = 1) then return false; fi;
  if not (true) then return false; fi;
  if not not (Size(G) = 1) then return false; fi;
  return true;
end;
P21 := function(G)
  local t1, t2;
  t1 := DirectProduct(G, G);
  if not (IsAbelian(t1)) then return false; fi;
  if not (Indec(G)) then return false; fi;
  t2 := t1;
  if not not (EmbedsG(t1, t2)) then return false; fi;
  if not not (true) then return false; fi;
  return true;
end;
P22 := function(G)
  local t1;
  t1 := DirectProduct(G, G);
  if not (IsAbelian(t1)) then return false; fi;
  if not (IsPGroup(G)) then return false; fi;
  if not (true) then return false; fi;
  if not not (true) then return false; fi;
  return true;
end;

QS := [[0, P0, false, true], [1, P1, false, true], [2, P2, false, true], [3, P3, false, false], [4, P4, false, false], [5, P5, false, true], [6, P6, false, true], [8, P8, false, true], [9, P9, false, true], [11, P11, false, false], [13, P13, true, true], [14, P14, true, false], [15, P15, true, false], [16, P16, true, false], [19, P19, true, true], [20, P20, false, false], [21, P21, false, false], [22, P22, false, false]];
FOUND := List(QS, q -> 0);
OUT := OutputTextFile("/tmp/tmpmlbjn850/hits.jsonl", false);
SetPrintFormattingStatus(OUT, false);
for n in [2..2000] do
  # порядок без библиотеки малых групп (512, 1024, … в пакете дистрибутива) — пропуск, а не обрыв перебора
  if SmallGroupsAvailable(n) and NrSmallGroups(n) <= 2000 then
    for i in [1..NrSmallGroups(n)] do
      G := SmallGroup(n, i);
      for j in [1..Length(QS)] do
        q := QS[j];
        if FOUND[j] < 2 and (n <= 1000 or (q[4] and IsOddInt(n) and n <= 2000))
           and (not q[3] or n <= 300) and (not q[4] or IsOddInt(n)) then
          r := CALL_WITH_CATCH(q[2], [G]);
          if r[1] = true and r[2] = true then
            FOUND[j] := FOUND[j] + 1;
            AppendTo(OUT, "{\"k\":", q[1], ",\"n\":", n, ",\"i\":", i, "}\n");
          fi;
        fi;
      od;
    od;
  fi;
od;
CloseStream(OUT);
QUIT;
