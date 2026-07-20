# Knowledge Base: erdos-98-wip-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session (researcher-1, 2026-07-20) — first machine-checked theorems (axiom-free)

Created `proofs/Proofs/Erdos98WIP01.lean` (5 theorems, 0 sorry, 0 axiom;
host-verified `bin/lake env lean` exit 0, `#print axioms` = `[propext,
Classical.choice, Quot.sound]` on all — no `sorryAx`, no `ofReduceBool`). The
scaffold `Erdos98Problem.lean` had only definitions; this file proves the first
structural facts about `numDistinctDistances` and `h`.

The **counting envelope** that any analysis of `h(n)` sits inside:

- `numDistinctDistances_le_offDiag` — `numDistinctDistances P ≤ n·(n−1)`. A
  positive distance forces `P i ≠ P j` (`dist_pos`), hence `i ≠ j`, so the
  distinct positive distances embed into `Finset.image f univ.offDiag`; count via
  `Finset.offDiag_card` and `Nat.mul_sub_one`.
- `numDistinctDistances_eq_zero_of_le_one` — degenerate floor `n ≤ 1 ⟹ 0`.
- `one_le_numDistinctDistances_of_injective` — for injective `P`, `2 ≤ n ⟹ ≥ 1`
  (exhibit indices `0 ≠ 1`, distinct images, positive distance).
- `InGeneralPosition.injective` — general position ⟹ injective (first conjunct).
- `h_le_of_inGeneralPosition` — `h n ≤ numDistinctDistances P` via `Nat.sInf_le
  ⟨P, hgp, rfl⟩`: every general-position configuration is an upper-bound witness
  for the minimum. This is the membership hook every known upper-bound
  construction (Pach `n^{log₂3}`, Erdős–Füredi–Pach `n·exp(c√log n)`) supplies.

### Verification
Parent `Erdos98Problem.lean` fresh-built to olean host-side (Mathlib-only, v4.31,
docker-free), then child compiled against it. Exit 0, no warnings.

### Next Steps
- ~~Sharpen the upper envelope to `numDistinctDistances P ≤ n.choose 2`~~ — DONE
  this session (see below).
- A lower bound beyond `1`: the elementary Erdős pigeonhole `≥ √(n − 3/4) − 1/2`
  distinct distances (needs the max-degree-of-a-distance argument) would be the
  first genuinely superconstant floor.

---

## Session (researcher-1, 2026-07-20 #2) — sharp ceiling + comment→statement conversion

Extended `Erdos98WIP01.lean` (now 13 theorems/defs, 0 sorry, 0 axiom;
`#print axioms` = `[propext, Classical.choice, Quot.sound]` on the new results —
no `sorryAx`, no `native_decide`). Two kinds of progress:

**1. Sharp unordered-pair ceiling.**
`numDistinctDistances_le_choose_two` — `numDistinctDistances P ≤ n.choose 2`,
halving the crude `n·(n−1)` bound from session #1. Key idea: `dist` is symmetric,
so the distance map `f (i,j) = dist (P i) (P j)` factors as `g ∘ Sym2.mk.uncurry`
with `g = Sym2.lift ⟨fun a b => dist (P a) (P b), dist_comm⟩`. Then
`(univ.offDiag).image f = ((univ.offDiag).image Sym2.mk.uncurry).image g`
(`Finset.image_image`), and `Sym2.card_image_offDiag` counts the off-diagonal
`Sym2` image as `(#univ).choose 2 = n.choose 2`. This is the correct
(unordered-pair) ceiling of the `h(n)` envelope.

**2. Comment-only bounds → typed Lean `Prop`s** (the stated mission of this
problem: "from comments to checkable statements"). Added, over the gallery `h`:
- `PachUpperBound` — `∀ᶠ n, (h n:ℝ) < n ^ logb 2 3` (imported assumption).
- `EFPUpperBound` — `∃ c>0, ∀ᶠ n, (h n:ℝ) < n·exp(c·√(log n))` (assumption).
- `GuthKatzBaseline` — `∃ c>0, ∀ᶠ n, c·n/log n ≤ h n` (assumption; Ω(n/log n)).
- `Erdos98WeakConjecture` — `∀ᶠ n, n ≤ h n` (OPEN).
- `Erdos98StrongConjecture` — `Tendsto (fun n => (h n:ℝ)/n) atTop atTop` (OPEN).

And two **machine-checked** relations proving the typed statements are correctly
wired (not independent guesses):
- `strong_imp_weak` — strong ⟹ weak (`one_le_div` + `eventually_ge_atTop 1`).
- `weak_imp_tendsto` — weak already forces `h(n)→∞` (`tendsto_atTop_mono'`),
  a non-vacuity sanity check.

### Verification
Host-side `bin/lake env lean Proofs/Erdos98WIP01.lean`, exit 0, no warnings
(Mathlib v4.31, docker-free). Axioms confirmed via `#print axioms`. Isolated
worktree (`researcher-1-erdos98`) because the shared main worktree's concurrent
Aristotle-integration automation was sweeping in-flight edits into its commits.

### Next Steps (unchanged core gap)
- The elementary Erdős pigeonhole lower bound `≥ √(n − 3/4) − 1/2` remains the
  first genuinely superconstant floor and the natural next proved theorem; it
  needs the max-multiplicity-of-a-single-distance counting argument.
- Everything deeper (Pach construction, EFP, Guth–Katz, either conjecture) stays
  an imported assumption / open — out of scope for host formalization.
