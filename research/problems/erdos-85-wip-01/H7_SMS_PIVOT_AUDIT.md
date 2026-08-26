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

## Bounded probes

### P1: CaDiCaL control

Stock CaDiCaL was run for 60 seconds on the lowest- and highest-conflict
depth-three F6/t2 leaves.  Both remained unknown.  It processed more conflicts
and propagations than Kissat, but produced no qualitative gain, so this control
is cut without a longer run.

### P2: template-automorphism SMS (source-audited NO-GO)

Represent the semantic low-vertex roles as a fixed auxiliary relational
template whose automorphism group is precisely the permitted simultaneous
high-label action (and, for a cube, the stabilizer of its empty mask).  Two
implementation candidates deserve a tiny-instance test:

1. an SMS multigraph: layer zero is the unknown low graph; a fixed second
   layer encodes membership in empty/singleton/pair roles and label incidence;
2. a 49-vertex graph encoding with the seven high vertices and all high-low
   incidences present as fixed structure, while only low-low edges remain
   free.

Inspection of SMS's `minimalityCheck.cpp`, multiple-adjacency-matrix checker,
and `--initial-partition` implementation closes this proposal as stated.  The
multigraph checker simultaneously permutes all layers, but fixing one labeled
template with CNF unit clauses does not restrict the checker to automorphisms
of that template.  A permutation can produce a lexicographically smaller
template labeling that violates those unit clauses, and SMS may then prune the
only CNF-allowed labeling.  The property given to the symmetry propagator is
not permutation invariant, so that use would be unsound.

`--initial-partition` does not repair the issue.  Its source semantics is a
sequence of blocks and the checker considers arbitrary permutations preserving
block membership.  It cannot express that one permutation of seven labels must
act diagonally and simultaneously on empty, singleton-copy, and pair indices.

A direct SMS run is therefore a no-go unless the entire encoding is rebuilt so
that every labeling of the relational template is accepted, or the minimality
checker is extended to accept the exact permitted permutation group.

### P3: residual stabilizer lex leaders

There is a smaller sound symmetry target that does not require generic SMS.
For each pinned seven-vertex empty mask:

1. enumerate its stabilizer inside the 5040 permutations of `Fin 7`;
2. induce each stabilizer element on all 42 canonical low indices using the
   already formalized `sevenHighT0LowIndexPerm` action;
3. add lex-leader constraints on the first 861 low-edge variables only for
   that stabilizer;
4. run CaDiCaL on the strengthened cube.

Every permutation used here is a genuine symmetry of that exact cube, unlike
the coarse SMS partition.  Proof production still requires one of two sound
bridges:

* verify the generated dominance clauses using LeanSMS's
  `verifyDominationFull`; or
* prove an H7-specific orbit-minimal representative theorem and show its edge
  valuation satisfies the emitted lex constraints.

The probe passes only if all of the following are demonstrated on a small
instance before H7 is attempted:

1. every emitted permutation fixes the parent empty mask and agrees with the
   formal low-index action;
2. each symmetry clause is either verified through LeanSMS or translated
   into a separately checked dominance certificate;
3. adding the verified clauses preserves the existing compact CNF's SAT
   semantics and exact cube units;
4. ordinary CaDiCaL can emit LRAT for the augmented CNF, and the existing Lean
   `LRAT.check` path accepts it.

## Decision

Blind adaptive splitting is cut at depth three.  P1 showed no qualitative
gain: two 60-second CaDiCaL leaves remained unknown despite somewhat higher
conflict/propagation throughput than Kissat.  P2 is source-audited no-go.  P3
is the remaining bounded structural experiment.  A direct SMS run with only
`-v 42`, a coarse initial partition, or fixed multigraph-template units is
explicitly forbidden because its symmetry group is unsound for this encoding.
