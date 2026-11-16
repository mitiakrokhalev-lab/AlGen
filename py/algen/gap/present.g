# Конечно заданные группы из карточек архива: порядок и тип (IdGroup).
#
# Вызов: gap -q -o 8g present.g с TASKS и OUT (см. finite.py, «--копредставления»).
# TASKS — список [id, ["a", "b", …], "a^2, b^3, (ab)^3"] (соотношения — как в ParseRelators).
# Строка вывода: {"id": …, "order": n или null (перечисление смежных классов
# не закончилось в пределе — группа бесконечна или велика), "key": "n:i" или null}.

MAXCOSETS := 200000;

Record1 := function(t, out)
  local F, gens, rels, T, n, P, key, s, i;
  F := FreeGroup(t[2]);
  gens := GeneratorsOfGroup(F);
  rels := ParseRelators(gens, t[3]);
  T := fail;
  T := CosetTableFromGensAndRels(gens, rels, [] : max := MAXCOSETS, silent := true);
  s := Concatenation("{\"id\":\"", t[1], "\"");
  if T = fail then
    Append(s, ",\"order\":null,\"key\":null}\n");
  else
    n := Length(T[1]);
    P := Group(List([1..Length(gens)], i -> PermList(T[2 * i - 1])), ());
    key := "null";
    if n > 0 and IdGroupsAvailable(n) then
      key := Concatenation("\"", String(n), ":", String(IdGroup(P)[2]), "\"");
    fi;
    Append(s, Concatenation(",\"order\":", String(n), ",\"key\":", key, "}\n"));
  fi;
  AppendTo(out, s);
end;

STREAM := OutputTextFile(OUT, false);
SetPrintFormattingStatus(STREAM, false);
for t in TASKS do Record1(t, STREAM); od;
CloseStream(STREAM);
QUIT;
