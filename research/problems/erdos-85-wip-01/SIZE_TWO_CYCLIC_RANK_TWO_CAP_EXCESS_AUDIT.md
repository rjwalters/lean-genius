# Rank-two cap-excess audit

Node: positive-variance amplification after the cap-free q8 sharp-source
threshold.

## Diagnostic

For a same-fibre unordered pair `p`, let `c(p)` be its number of common
targets.  Define

```text
capExcess = sum_p max(c(p)-1,0).                       (1)
```

Thus `capExcess=0` is exactly the full family of same-fibre caps.  The full
probe now exposes:

```text
--dump-collision-separations
--minimize-cap-excess
--max-cap-excess K
```

The dump groups pair count, collision mass, occupied owner pairs, and (1) by
endpoint fibre and cyclic base separation.  The optimization/bound modes are
native-Z3 diagnostics; DIMACS export is deliberately rejected because their
current arithmetic objective is not a pure Boolean PB encoding.

## Attained cap-free V=128 stratum

At q8, `--min-sharp-sources 32 --no-caps` attains the cap-free lower stratum
with total block energy `V=128`, hence total collision mass `V/2=64`.

For `a=1`, one witness is extremely concentrated:

```text
fibre 0, separation 4: mass 8 on 4 pairs, excess 4
fibre 3, separation 1: mass 16 on 8 pairs, excess 8
fibre 4, separation 1: mass 16 on 8 pairs, excess 8
fibre 7, separation 4: mass 8 on 4 pairs, excess 4
```

The remaining collision mass is cap-respecting, so this witness has total
`capExcess=24`.

The phenomenon is not forced to be this concentrated.  At `a=2`, a solver
witness distributes the same mass over separations 1,2,3,4 and has only

```text
capExcess = 8.
```

Running the new bounded diagnostic confirms that the q8 a2 rank-two stratum
is SAT with `--max-cap-excess 8`.  Bounds 1,2,4 remained UNKNOWN at 180
seconds, so 8 is an attained upper bound on the minimum, not a proved exact
minimum.

## Consequence

The cap does not merely oppose large scalar variance.  Even at the smallest
known cap-free energy, the affine and reciprocal incidence constraints can
force repeated use of a small number of owner pairs while leaving most of
the nominal capacity `choose(q,2)` unused.  Therefore a useful amplification
statement should track

```text
collision mass - number of distinct occupied owner pairs,                (2)
```

possibly resolved by cyclic separation, rather than compare collision mass
only with the total pair capacity.

This is evidence and a probe interface, not a q-generic inequality.  The a2
witness also cuts any claim that minimum-rank collisions must lie only at
separation 1 or the antipodal separation: its cap-respecting mass occurs at
separations 2 and 3 as well.  The surviving target is to prove that (2) is
positive (or grows under the defect-rank ladder) for every reciprocal affine
realization in the relevant low-energy strata.

## Equality owner-fibre and edge census

The stronger exact interface `sum_p r(p)<=64` isolates equality at q8.  A
fresh a1 equality witness resolves its 64 collision tokens into eight
owner-fibre layers, each of mass eight.  Every layer is individually simple.
At endpoint fibres 3 and 4, however, two different owner fibres use the same
complete separation-2 support, so their union repeats all eight owner pairs.

The sharp/nonsharp adjacency census of this witness is

```text
sharp sources 32, nonsharp sources 16
SS edges 64, SN edges 64, NN edges 16
sharp vertices:     sharp-neighbour degrees 3 (16 times), 5 (16 times)
nonsharp vertices:  sharp-neighbour degree 4 (16 times).
```

Thus the nonsharp sources are not an independent transversal: they induce a
2-regular graph.  A cocycle-frustration proof cannot assume that every
obstructing cycle meets a nonsharp source only as an isolated boundary.

At a2 an equality witness is less uniform (`SS=66,SN=60,NN=18`), and its
owner-fibre layers use separations 1,2,3,4.  Two antipodal layers already
repeat pairs within one owner fibre, while other repeats can occur only after
owner fibres are united.

## Singleton and pair cap-fibre discriminator

The probe also exposes `--cap-fibres`, which imposes all pair caps only in
the listed endpoint fibres.  With full reciprocity and `sum r<=64` at q8:

```text
a=1: singleton cap fibre 3 or 4 is UNSAT;
     singleton 0,2,5,7 is SAT.

a=2: every singleton cap fibre is SAT;
     cap-fibre pairs {0,3},{0,4},{0,7},{3,7},{4,7} are UNSAT;
     the other ten pairs are SAT.
```

Therefore the equality stratum can be killed by one collision graph in one
hole placement, but no uniform one-fibre theorem is possible.  Already at
the same order a different hole placement requires genuinely coupled caps
from two endpoint fibres.  This is a sharper proof-design constraint than a
timeout-dependent multi-cap core.
