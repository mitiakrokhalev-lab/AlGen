# Классы сопряжённых элементов конечных групп таблицы.
#
# Для каждого класса: порядок элемента, размер класса, вещественный ли (x ~ x⁻¹),
# коммутатор ли (по таблице характеров: Σ χ(x)/χ(1) ≠ 0), класс x⁻¹, класс x²,
# номера классов подгрупп ⟨x⟩ и C(x) в ConjugacyClassesSubgroups (как в groups.g),
# есть ли в классе элемент, не перестановочный с x («nc»).
#
# Вызов: gap -q -o 8g elts.g с KEYS и OUT (см. finite.py, «--элементы»).
# Строка вывода: {"key": "n:i", "classes": [{…}, …], "check": [[тип, размер класса], …]}
# или "classes": null, если классов подгрупп больше MAXCLASSES.

if not IsBound(MAXCLASSES) then MAXCLASSES := 300; fi;
Key := G -> Concatenation(String(Size(G)), ":", String(IdGroup(G)[2]));
B := b -> ShallowCopy(String(b));

SubClass := function(cls, H)
  return PositionProperty(cls, c -> Size(Representative(c)) = Size(H) and H in c) - 1;
end;

Record1 := function(G, out)
  local scls, ecls, irr, s, i, x, c, comm, inv, sq, reps, nc;
  if Length(LatticeSubgroups(G)!.conjugacyClassesSubgroups) > MAXCLASSES then
    AppendTo(out, Concatenation("{\"key\":\"", Key(G), "\",\"classes\":null}\n"));
    return;
  fi;
  scls := ConjugacyClassesSubgroups(G);
  ecls := ConjugacyClasses(G);
  irr := Irr(CharacterTable(G));
  # Irr(CharacterTable(G)) нумерует классы как ConjugacyClasses(CharacterTable(G)); сверяем
  reps := List(ConjugacyClasses(CharacterTable(G)), Representative);
  s := Concatenation("{\"key\":\"", Key(G), "\",\"classes\":[");
  for i in [1..Length(ecls)] do
    x := Representative(ecls[i]);
    c := PositionProperty(reps, r -> r in ecls[i]);
    comm := Sum(irr, chi -> chi[c] / chi[1]) <> 0;
    inv := PositionProperty(ecls, k -> x^-1 in k) - 1;
    sq := PositionProperty(ecls, k -> x^2 in k) - 1;
    # есть ли сопряжённый с x элемент, не перестановочный с x
    nc := ForAny(AsList(ecls[i]), y -> x * y <> y * x);
    if i > 1 then Append(s, ","); fi;
    Append(s, Concatenation("{\"ord\":", String(Order(x)), ",\"size\":", String(Size(ecls[i])),
      ",\"real\":", B(inv = i - 1), ",\"nc\":", B(nc), ",\"comm\":", B(comm), ",\"inv\":", String(inv),
      ",\"sq\":", String(sq), ",\"gen\":", String(SubClass(scls, Subgroup(G, [x]))),
      ",\"cent\":", String(SubClass(scls, Centralizer(G, x))), "}"));
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
