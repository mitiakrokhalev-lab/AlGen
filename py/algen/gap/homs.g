# Эндоморфизмы конечных групп таблицы: представители классов (AllHomomorphismClasses,
# с точностью до внутренних автоморфизмов образа), кроме нулевого и внутренних
# автоморфизмов. У абелевых — степенные отображения x ↦ x^k.
#
# Для каждого представителя φ: номера классов подгрупп ker φ и im φ (в порядке
# ConjugacyClassesSubgroups, как в groups.g), инъективен, сюръективен,
# идемпотентен (φ∘φ = φ), внутренний автоморфизм.
#
# Вызов: gap -q -o 8g homs.g с KEYS и OUT (см. finite.py, «--гомоморфизмы»).
# Строка: {"key": "n:i", "endos": [{"ker": i, "im": j, "inj": …, "surj": …, "idem": …, "inner": …}, …],
# "check": [[тип, размер класса], …]} или "endos": null, если группа велика.

if not IsBound(MAXCLASSES) then MAXCLASSES := 300; fi;
if not IsBound(MAXNONAB) then MAXNONAB := 100; fi;
if not IsBound(MAXENDO) then MAXENDO := 40; fi;
Key := G -> Concatenation(String(Size(G)), ":", String(IdGroup(G)[2]));
B := b -> ShallowCopy(String(b));

SubClass := function(cls, H)
  return PositionProperty(cls, c -> Size(Representative(c)) = Size(H) and H in c) - 1;
end;

Record1 := function(G, out)
  local scls, maps, s, f, first, k, e, n, gens;
  if Length(LatticeSubgroups(G)!.conjugacyClassesSubgroups) > MAXCLASSES
     or (not IsAbelian(G) and Size(G) > MAXNONAB) then
    AppendTo(out, Concatenation("{\"key\":\"", Key(G), "\",\"endos\":null}\n"));
    return;
  fi;
  scls := ConjugacyClassesSubgroups(G);
  gens := GeneratorsOfGroup(G);
  if IsAbelian(G) then
    e := Exponent(G);
    maps := List([2..Maximum(2, e - 1)], k -> GroupHomomorphismByImagesNC(G, G, gens, List(gens, x -> x^k)));
  else
    maps := AllHomomorphismClasses(G, G);
  fi;
  s := Concatenation("{\"key\":\"", Key(G), "\",\"endos\":[");
  first := true; n := 0;
  for f in maps do
    if n >= MAXENDO then break; fi;
    if Size(Image(f)) = 1 then continue; fi;                         # нулевой
    if IsBijective(f) and IsInnerAutomorphism(f) then continue; fi;   # класс тождественного
    if not first then Append(s, ","); fi;
    first := false; n := n + 1;
    Append(s, Concatenation("{\"ker\":", String(SubClass(scls, Kernel(f))),
      ",\"im\":", String(SubClass(scls, Image(f))),
      ",\"inj\":", B(IsInjective(f)), ",\"surj\":", B(IsSurjective(f)),
      ",\"idem\":", B(ForAll(gens, x -> Image(f, Image(f, x)) = Image(f, x))),
      ",\"inner\":", B(IsBijective(f) and IsInnerAutomorphism(f)), "}"));
  od;
  Append(s, "],\"check\":[");
  for k in [1..Length(scls)] do
    if k > 1 then Append(s, ","); fi;
    Append(s, Concatenation("[\"", Key(Representative(scls[k])), "\",", String(Size(scls[k])), "]"));
  od;
  Append(s, "]}\n");
  AppendTo(out, s);
end;

STREAM := OutputTextFile(OUT, false);
SetPrintFormattingStatus(STREAM, false);
for k in KEYS do Record1(SmallGroup(k[1], k[2]), STREAM); od;
CloseStream(STREAM);
QUIT;
