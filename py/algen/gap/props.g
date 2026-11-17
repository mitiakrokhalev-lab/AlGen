# Свойства конечных групп таблицы, которых нет в groups.g: метабелевость, ступень
# нильпотентности ⩽ 2, экспонента, порядки элементов, дедекиндовость.
#
# Вызов: gap -q -o 8g props.g с KEYS и OUT (см. finite.py, «--свойства»).
# Строка: {"key": "n:i", "metabelian": …, "class-2": …, "exponent": e,
#          "orders": [порядки классов], "dedekind": …}

Key := G -> Concatenation(String(Size(G)), ":", String(IdGroup(G)[2]));
B := b -> ShallowCopy(String(b));

Record1 := function(G, out)
  local cls, ords, ded, s;
  cls := ConjugacyClasses(G);
  ords := Set(List(cls, c -> Order(Representative(c))));
  # все подгруппы нормальны ⇔ все циклические нормальны (⟨x⟩ по представителям классов)
  ded := ForAll(cls, c -> IsNormal(G, Subgroup(G, [Representative(c)])));
  s := Concatenation("{\"key\":\"", Key(G), "\"",
    ",\"metabelian\":", B(IsSolvableGroup(G) and DerivedLength(G) <= 2),
    ",\"class-2\":", B(IsNilpotentGroup(G) and NilpotencyClassOfGroup(G) <= 2),
    ",\"exponent\":", String(Exponent(G)),
    ",\"orders\":", String(ords),
    ",\"dedekind\":", B(ded), "}\n");
  AppendTo(out, s);
end;

STREAM := OutputTextFile(OUT, false);
SetPrintFormattingStatus(STREAM, false);
for k in KEYS do Record1(SmallGroup(k[1], k[2]), STREAM); od;
CloseStream(STREAM);
QUIT;
