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

