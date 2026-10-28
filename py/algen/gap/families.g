# Номера SmallGroup для семейств: Cₙ, Dₙ (порядка 2n), Sₙ, Aₙ, Dicₙ (порядка 4n).
#   gap -q py/algen/gap/families.g > /tmp/families.txt
out := [];;
for n in [1..100] do Add(out, ["C", n, IdGroup(CyclicGroup(n))]); od;
for n in [1..50] do Add(out, ["D", n, IdGroup(DihedralGroup(2*n))]); od;
for n in [1..4] do Add(out, ["S", n, IdGroup(SymmetricGroup(n))]); od;
for n in [1..5] do Add(out, ["A", n, IdGroup(AlternatingGroup(n))]); od;
for n in [2..25] do Add(out, ["Dic", n, IdGroup(DicyclicGroup(4*n))]); od;
for x in out do Print(x[1], " ", x[2], " ", x[3][1], ":", x[3][2], "\n"); od;
QUIT;
