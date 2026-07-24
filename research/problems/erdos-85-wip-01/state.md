# Research State: erdos-85-wip-01

> **S-f15f16 (2026-07-24, researcher-2): FIFTH + SIXTH SURGERY RUNGS —
> `f(15), f(16) ∈ {4, 5}`, docker GREEN first try (0 ax / 0 sorry).**
> Sections Fifteen + Sixteen: `petersen14` (= f(14) surgery 0-4-3
> materialised) and `petersen15` (= f(15) surgery 0-5-7 materialised) as
> explicit edge lists with kernel `decide` checks; abstract surgery configs
> `0-5-7` and `6-8-5`; counting bound `15,16 ≤ 5·4` above. Python-verified
> before writing (min degree, common ≤ 1, triangle-free path edges) — both
> rungs compiled first try. f(17)..f(20) are cheap future rungs: petersen16
> edge list + seven valid 16→17 configs pre-enumerated in knowledge.md.
> Upper halves 14..20 remain blocked on ex(n;C₄); next tight point 21.
> See PR (S-f15f16) and knowledge.md.

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-07-09T17:33:20-07:00
**Iteration**: 1

## Current Focus
Initial problem understanding. Read problem.md and gather context.

## Active Approach
None yet.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action
Read problem.md thoroughly and acquire full context.
Then move to ORIENT phase to explore literature and related proofs.

## Status (researcher-1, 2026-07-23) — abstract surgery engine + f(13) ≥ 4

(The template header above predates the real work — see knowledge.md for the full
session history; the exact table f(1..12) is complete on main.)

This session: the vertex-adding surgery is now an ABSTRACT lemma set in
`Erdos85Problem.lean` (section Surgery): `surgery G a b c : SimpleGraph (Option V)`
with degree preservation, common-neighbour ≤ 1 preservation (hypotheses: a~b, b~c,
a≁c, a≠c, edges ab/bc triangle-free), generic `four_le_minDegreeForC4_of_witness`,
and `finSuccEquiv` transport. Applied to petersen12 (a=4, b=9, c=7):
**f(13) ≥ 4**, hence f(13) ∈ {4,5} (`minDegreeForC4_thirteen_mem`) — first rung
beyond the counting range, no 13-vertex decide.

## Status (researcher-2, 2026-07-24) — **f(13) = 4 PROVED** (friendship theorem)

The f(13) ≤ 4 blocker is RESOLVED by a materially new mechanism — not a Reiman
edge bound, but equality analysis of the cherry count at the projective-plane
parameter point 13 = 4·3+1 (`13·C(4,2) = C(13,2) = 78` exactly): tightness forces
4-regularity + surjectivity of the cherry→endpoint-pair map, i.e. the friendship
condition, and `Theorems100.friendship_theorem` (Mathlib Archive, importable in
this toolchain!) yields a degree-12 politician — contradiction with 4-regularity.
`minDegreeForC4_thirteen : minDegreeForC4 13 = 4` — exact table now 1..13.
0 sorries, 0 axioms. See knowledge.md session 2026-07-24.

## Status (researcher-3, 2026-07-24) — **tight-point theorem: f(k(k−1)+1) ≤ k ∀ k ≥ 3**

The "generalization f(k²−k+1) ≤ k is a candidate target" blocker item is DONE:
new section `TightPoints` in `Erdos85Problem.lean` (+208 LOC, 0 sorries,
0 axioms, docker-verified) parameterises the entire `Thirteen` argument over k:

- `choose_two_tight : C(k(k−1)+1, 2) = (k(k−1)+1)·C(k,2)` — exact tightness at
  every projective-plane parameter (two-line proof reusing `two_dvd_mul_pred`).
- `containsC4_of_tight_minDegree (hk : 3 ≤ k)` — every graph on k(k−1)+1
  vertices with δ ≥ k contains C₄. Same skeleton as `Thirteen`: cherry count
  exactly tight ⟹ k-regular + cherry→pair surjective ⟹ `Theorems100.Friendship`
  ⟹ politician degree k(k−1) ≠ k (needs k ≥ 3). Literal constants (78, 6, 72,
  10, 12) replaced by atom-level arithmetic omega handles: Pascal
  `(k+1).choose 2 = k.choose 2 + k` for the regularity pinch, `Nat.succ_mul`
  for the sum split, `Nat.mul_le_mul_left` (2 ≤ k−1) for the final clash.
- `minDegreeForC4_le_tight (hk : 3 ≤ k) : minDegreeForC4 (k*(k-1)+1) ≤ k` —
  infinitely many upper bounds one vertex beyond the counting range.
- NEW concrete values beyond the exact table: `minDegreeForC4_twentyone_le :
  f(21) ≤ 5`, `minDegreeForC4_thirtyone_le : f(31) ≤ 6` (k = 5, 6 instances,
  `simpa` numerals); the k = 4 instance re-derives f(13) ≤ 4 as an `example`.

Session memo: `sessions/2026-07-24-tight-points-generalization.md`.

## Blockers
- Upper bounds at NON-tight n > 13: the friendship mechanism only covers
  n = k(k−1)+1 exactly (now formalized ∀ k ≥ 3); other n still need real
  ex(n;C₄) edge-extremal input. Reopen: formalize a Reiman-type bound.
- Matching lower bounds at tight points: f(21) ≥ 5 would need a C₄-free
  4-regular-ish witness on 21 vertices (incidence graph route) — the surgery
  engine gives f(14) ≥ 4 as the next accessible rung instead.
- General ∀ n ≥ 10 f(n) ≥ 4: needs config EXISTENCE (edge pair ab, bc both
  triangle-free, a≁c) in iterated witnesses — not automatic in arbitrary
  C₄-free min-deg-3 graphs. Reopen: invariant-maintaining induction or
  disjoint-union route (needs base cases 13..19 + graph-sum infrastructure).
- Deep: KST asymptotics; monotonicity core (the actual Erdős #85) OPEN.
