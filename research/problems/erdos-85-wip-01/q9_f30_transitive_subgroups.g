# GAP certificate generator for CubicVT[80,30].
#
# The four permutations are independently checked by the companion Python
# verifier to generate the full order-960 automorphism group of census graph
# ordinal 30.  GAP enumerates conjugacy classes of subgroups and emits one
# compact representative for every transitive class.

g1 := (2,3)(5,7)(6,9)(11,19)(12,21)(13,15)(14,17)(16,20)(18,22)(23,35)(24,37)(25,31)(26,33)(27,43)(28,45)(29,39)(30,41)(32,36)(34,38)(40,44)(42,46)(47,57)(48,49)(50,53)(51,54)(52,62)(55,64)(56,65)(58,63)(59,67)(60,68)(61,66)(71,73)(72,75)(74,76)(78,79);
g2 := (5,6)(7,9)(8,10)(11,12)(13,14)(15,17)(16,18)(19,21)(20,22)(23,28)(24,27)(25,30)(26,29)(31,41)(32,42)(33,39)(34,40)(35,45)(36,46)(37,43)(38,44)(47,52)(48,51)(49,54)(50,53)(55,60)(56,59)(57,62)(58,61)(63,66)(64,68)(65,67)(69,70)(71,73)(72,74)(75,76);
g3 := (2,4,3)(5,8,7)(6,10,9)(11,16,15)(12,18,17)(13,20,19)(14,22,21)(23,32,31)(24,34,33)(25,36,35)(26,38,37)(27,40,39)(28,42,41)(29,44,43)(30,46,45)(48,55,63)(49,58,64)(50,59,65)(51,60,66)(53,56,67)(54,61,68)(69,72,75)(70,74,76)(77,78,79);
g4 := (1,2)(3,5)(4,6)(7,11)(8,12)(9,13)(10,14)(15,23)(16,24)(17,25)(18,26)(19,27)(20,28)(21,29)(22,30)(31,47)(32,48)(33,49)(34,50)(35,51)(36,52)(37,53)(38,54)(39,55)(40,56)(41,57)(42,58)(43,59)(44,60)(45,61)(46,62)(63,69)(64,70)(65,71)(66,72)(67,73)(68,74)(75,77)(76,78)(79,80);

G := Group([g1,g2,g3,g4]);
SizeScreen([100000, 100000]);
if Size(G) <> 960 then Error("wrong automorphism group size"); fi;
classes := ConjugacyClassesSubgroups(G);
if Length(classes) <> 132 then Error("wrong subgroup class count"); fi;
trans := Filtered(classes, c -> IsTransitive(Representative(c), [1..80]));
if Length(trans) <> 5 then Error("wrong transitive subgroup class count"); fi;

Print("META|960|132|5\n");
for c in trans do
  H := Representative(c);
  Print("H|", Size(H), "|", Size(c), "|");
  first := true;
  for gen in GeneratorsOfGroup(H) do
    if not first then Print(";"); fi;
    first := false;
    Print(JoinStringsWithSeparator(List([1..80], i -> String(i^gen)), ","));
  od;
  Print("\n");
od;
QUIT;
