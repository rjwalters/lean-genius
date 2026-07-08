# Current State

**Phase**: ACT
**Since**: 2026-07-08T00:00:00Z
**Iteration**: 3

## Current Focus

Reducing the `NoFiveCollinear` obligation for growing constructions to a
clean 3-point height certificate.

## Active Approach

Path B (explicit constructions). The frontier obstruction identified last
iteration was: a general-n growing witness needs a clean "no five
collinear" proof, but `NoFiveCollinear` quantifies over five distinct
points, which is awkward to discharge for a parametric family. This
iteration removes that obstruction.

## Progress This Iteration (VERIFIED, 0-axiom)

Added two general theorems to `Proofs/Erdos101OQ04.lean` (build-verified,
3062 jobs; only the two pre-existing OPEN construction sorries remain):

- `noFiveCollinear_of_height_certificate` — **NoFiveCollinear from a
  3-point height certificate.** If (H1) every horizontal line `y = c`
  meets `P` in at most four points, and (H2) no three points of `P` with
  pairwise-distinct second coordinates are collinear, then `P` is
  no-five-collinear. Proof: a horizontal anchor forces all five points
  into the height fibre at `a.2`, contradicting H1 (≤4); a non-horizontal
  anchor gives `a, b, c` pairwise-distinct heights, so H2 refutes
  `collinear a b c` directly.

- `isLowerBoundConstruction_of_rows` — **frontier template.** Combines the
  counting engine (`fourPointLineCount_ge_of_injOn_family`) with the
  height reduction: an injective family of `k` four-point collinear
  subsets of `P`, plus (H1, H2), yields `IsLowerBoundConstruction P k`.

Together these collapse the entire five-point `NoFiveCollinear` case
analysis into a single 3-point arithmetic hypothesis H2 (H1 is immediate
for any row construction). A future growing-witness PR now only has to
supply the four-point lines and prove H2 — never re-derive the five-point
plumbing.

## Blockers

The two OPEN construction sorries are unchanged and remain the frontier:
- `grunbaum_lower_bound_three_halves` (Ω(n^{3/2}))
- `solymosi_stojakovic_lower_bound` (n^{2−o(1)})

The remaining obligation for a general-n growing witness is now isolated
to hypothesis **H2** of `isLowerBoundConstruction_of_rows`: "no three
points with pairwise-distinct heights are collinear" — the arithmetic
"no accidental cross-row alignment" certificate. For a super-increasing
offset family this is a Vandermonde-type non-vanishing that grows with the
row count; formalising it for all `n` is the next hard step.

## Next Action

Instantiate `isLowerBoundConstruction_of_rows` with a concrete growing row
family (k horizontal 4-point segments at distinct heights with
super-increasing x-offsets). Supply the `k` four-point lines via the
family `L`, and discharge H2 through the offset non-vanishing argument.
This would turn the constant floor (currently 10, from `gridSet`) into a
growing Ω(k) lower bound.

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 2
- Approaches tried: 1
