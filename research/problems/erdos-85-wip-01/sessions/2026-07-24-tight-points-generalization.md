# Session 2026-07-24 (researcher-3) — tight-point theorem: f(k(k−1)+1) ≤ k for all k ≥ 3

## Result

The candidate target named in state.md's Blockers ("generalization f(k²−k+1) ≤ k")
is proved. New section `TightPoints` in `Proofs/Erdos85Problem.lean` (+208 LOC,
0 sorries, 0 axioms; docker build 8577 jobs, exit 0, zero warnings in the new
section, first try):

- `choose_two_tight (k) : (k*(k-1)+1).choose 2 = (k*(k-1)+1) * k.choose 2`
- `containsC4_of_tight_minDegree {k} (hk : 3 ≤ k) (G : SimpleGraph (Fin (k*(k-1)+1)))
  [DecidableRel G.Adj] (hmin : k ≤ G.minDegree) : containsC4 _ G`
- `minDegreeForC4_le_tight {k} (hk : 3 ≤ k) : minDegreeForC4 (k*(k-1)+1) ≤ k`
- `minDegreeForC4_twentyone_le : minDegreeForC4 21 ≤ 5` — NEW value beyond the
  exact table f(1..13)
- `minDegreeForC4_thirtyone_le : minDegreeForC4 31 ≤ 6` — ditto
- `example : minDegreeForC4 13 ≤ 4` — k = 4 instance recovers the Thirteen result

## Method — parameterising the `Thirteen` section

The f(13) proof structure survives verbatim; only the literals needed lemmas:

| f(13) literal | general form | mechanism |
|---|---|---|
| `T.card = 78` (decide) | `T.card = (k(k−1)+1)·C(k,2)` | `choose_two_tight` via `Nat.choose_two_right` + `Nat.add_sub_cancel` + `Nat.mul_div_assoc _ (two_dvd_mul_pred k)` (helper already in file at line 807) |
| `6 = C(4,2)` per-vertex bound | `k.choose 2` kept as an atom | `Nat.choose_le_choose 2` |
| `10 = C(5,2)` regularity pinch | `(k+1).choose 2 = k.choose 2 + k` | Pascal: `Nat.choose_succ_succ` + `Nat.choose_one_right` + `Nat.add_comm` |
| `72 = 12·6` erase-sum bound | `(k(k−1))·C(k,2)` | `sum_const` over `univ.erase` + `Nat.add_sub_cancel` |
| final `omega` on literals | `omega` on atoms | supply `hmul : (k(k−1)+1)·A = (k(k−1))·A + A := Nat.succ_mul _ _` so omega's atom abstraction sees only linear facts |
| politician degree `12` | `k(k−1)` | `Nat.add_sub_cancel` on the card; clash via `h2k : k*2 ≤ k*(k−1) := Nat.mul_le_mul_left k (2 ≤ k−1)` + omega |

Statement uses `k * (k - 1) + 1` (NOT `k^2 - k + 1`) so that `n − 1 = k*(k−1)`
is `Nat.add_sub_cancel` and all arithmetic stays linear-in-atoms for omega —
no nonlinear nat-subtraction identities needed anywhere.

**omega + nonlinear atoms**: omega abstracts `(k*(k-1))*(k.choose 2)` and
`(k*(k-1)+1)*(k.choose 2)` as opaque atoms; providing their relation explicitly
(`Nat.succ_mul`) lets it close the tightness pinches. This worked first try.

The friendship half (Classical-vs-synthesized Fintype `convert hone using 2`
bridge) is dimension-independent and copied unchanged.

## Why k ≥ 3

k = 0,1,2 degenerate: the politician clash needs k(k−1) ≠ k, i.e. k ≠ 2 and
k ≠ 0-trivialities; f(3) ≤ 2 etc. are already covered by the elementary bounds.
The hypothesis is consumed only in the final omega (via `2 ≤ k − 1`).

## Interpretation

Infinitely many upper bounds one vertex beyond the crude counting range
`n ≤ k(k−1)` (`minDegreeForC4_le_of_le_mul_pred`). At tight points the bound
beats the closed form `f(n) ≤ √n + 2` by 1: e.g. √21+2 = 6 vs f(21) ≤ 5,
√31+2 = 7 vs f(31) ≤ 6. These are exactly the projective-plane parameters:
when a projective plane of order k−1 exists, its incidence structure is the
conjectured extremal configuration, so these bounds are plausibly exact
(f(21) = 5 would need a matching lower-bound witness — see Blockers).

## Next steps

- f(14) ≥ 4 via the surgery engine (next accessible lower-bound rung).
- Matching lower bounds at tight points (incidence-graph witnesses on 21/31
  vertices — heavier: needs a C₄-free min-degree-(k−1)... construction).
- Reiman-type ex(n;C₄) bound for non-tight n.
