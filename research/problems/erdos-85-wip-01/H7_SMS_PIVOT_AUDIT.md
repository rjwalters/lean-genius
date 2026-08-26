# H7 canonical completion: SAT-modulo-symmetries pivot audit

Date: 2026-08-26

## Trigger

The hard canonical parent `cube_F6_t2` remained `UNKNOWN` under bounded
Kissat runs after deterministic splitting to depths one, two, and three:
all `2 + 4 + 8` leaves exhausted 60 seconds, with roughly 1.4--1.7 million
conflicts per depth-three leaf.  No depth-four split is authorized by this
audit.  The missing link is operational proof production, not another CNF or
Lean composition socket.

## Outside mechanisms

The closest published computation is the recent `R(C4,K1,39)=46` work.  Its
144 graph instances were solved by CaDiCaL in 2--424 seconds, while its authors
explicitly report Kissat as much slower on the same family:

<https://github.com/zach7036/c4-star-ramsey/blob/main/R_C4_K1_39.md>

SAT Modulo Symmetries (SMS) adds a canonical-minimality propagator to CaDiCaL
and accepts an ordinary DIMACS encoding provided its edge-variable numbering
is correct:

<https://sat-modulo-symmetries.readthedocs.io/en/latest/>

The verified LeanSMS pipeline separates symmetry discovery from proof replay:
SMS emits symmetry clauses, Lean verifies those clauses, and ordinary CaDiCaL
then emits the final LRAT:

<https://github.com/leansolving/leansms>

The accompanying formal-methods paper is:

<https://doi.org/10.1007/978-3-032-32589-1_8>

## Exact compatibility found

SMS numbers undirected edges row-wise across the upper triangle.  The compact
H7 CNF's variables `1..861` use exactly the same order on the 42 low vertices
(`choose(42,2) = 861`), via `sevenHighT0CanonicalLowEdgePairs` and
`sevenHighT0CanonicalLowEdgeId`.  Auxiliary variables begin after that range.
Therefore no edge-variable permutation is needed for a plain 42-vertex SMS
input.

## Soundness trap

Running `smsg -v 42` directly is **not sound** for the canonical CNF.  The 42
low vertices have three semantic classes:

* seven empty-support vertices;
* fourteen singleton-support vertices (`Fin 7 x Fin 2`);
* twenty-one pair-support vertices (`Sym2 (Fin 7)`).

The known invariance is only the simultaneous action induced by one
permutation of the seven high labels.  After an empty-mask cube is fixed, it
shrinks further to the automorphism group of that mask.  A normal SMS initial
partition would allow arbitrary, independent permutations inside its blocks;
that group is strictly larger and could learn invalid blocking clauses.

## Two bounded probes

### P1: CaDiCaL control

Before changing the encoding, run stock CaDiCaL for 60 seconds on the best and
worst depth-three F6/t2 leaves.  Compare verdict, conflicts, propagations, and
resident memory with the recorded Kissat signal.  If neither terminates but
CaDiCaL is materially faster, extend the time on one leaf only.  If there is
no qualitative gain, cut this control.

### P2: template-automorphism SMS

Represent the semantic low-vertex roles as a fixed auxiliary relational
template whose automorphism group is precisely the permitted simultaneous
high-label action (and, for a cube, the stabilizer of its empty mask).  Two
implementation candidates deserve a tiny-instance test:

1. an SMS multigraph: layer zero is the unknown low graph; a fixed second
   layer encodes membership in empty/singleton/pair roles and label incidence;
2. a 49-vertex graph encoding with the seven high vertices and all high-low
   incidences present as fixed structure, while only low-low edges remain
   free.

The probe passes only if all of the following are demonstrated on a small
instance before H7 is attempted:

1. the template automorphism group equals the intended simultaneous label
   action (no extra within-block permutations);
2. each SMS symmetry clause is either verified through LeanSMS or translated
   into a separately checked dominance certificate;
3. adding the verified clauses preserves the existing compact CNF's SAT
   semantics and exact cube units;
4. ordinary CaDiCaL can emit LRAT for the augmented CNF, and the existing Lean
   `LRAT.check` path accepts it.

## Decision

Blind adaptive splitting is cut at depth three.  P1 is the immediate bounded
control.  P2 is the preferred structural experiment if P1 does not close a
leaf.  A direct SMS run with only `-v 42` or a coarse initial partition is
explicitly forbidden because its symmetry group is unsound for this encoding.
