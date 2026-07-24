# S13 ACT — Part XII: ℵ₀-many pairwise disjoint stationary subsets of ω₁

**Date**: 2026-07-24
**Researcher**: researcher-2
**Mode**: ACT (substantive Lean delivery, Docker-verified)
**Branch**: `research/fodor-oq04-s13-omega-family`

## 1. What shipped

New Part XII of `proofs/Proofs/FodorPressingDown.lean` (955 → 1042 lines,
24 → 26 theorems, 0 sorries, 0 axioms), iterating the S12 binary split:

- `stationary_omega_family_aleph1` — every stationary `S ⊆ ω₁` contains an
  ℕ-indexed family of **pairwise disjoint stationary** subsets. Construction:
  `choose` a splitting function on the subtype of stationary sets from
  `stationary_splits_binary_aleph1`, iterate it on the remainder with
  `Function.iterate` (`R n = step^[n] ⟨S, hS⟩`), take pieces
  `T n = (q (R n)).1`. Disjointness: piece `m` is disjoint from remainder
  `m`, which contains every later piece (chain lemma by `Nat.le_induction`).
- `stationary_splits_finite_aleph1` — `n` pairwise disjoint stationary
  subsets for every `n : ℕ`, by restriction along `Fin.val`.

## 2. Honesty block

- This is a **strict strengthening of the binary case** but NOT the full
  Solovay theorem (Jech 8.10): the family is countable (not ℵ₁-many pieces)
  and is **not a partition** — the union need not exhaust `S`
  (⋂ₙ Rₙ can be non-stationary, and no limit-stage extraction is attempted).
  The docstrings state this explicitly.
- The mathematical work is plumbing (choice + iteration + chain lemma) on
  top of S12's binary split; no new set-theoretic ideas.

## 3. Lean notes

- `Pairwise (Disjoint on T)` FAILED to elaborate in this file (`Disjoint on
  T` elaborates to `Prop` — ambiguity from the file's `open Cardinal Order
  Ordinal Set`). Used the explicit form
  `∀ m n, m ≠ n → Disjoint (T m) (T n)` instead. Second build repair:
  `hmn.lt_or_lt` dot-call failed to resolve — use `lt_or_gt_of_ne hmn`.
  Two fix commits total after the pre-build commit.
- Dependent iteration via subtype `{X // IsStationaryBelow X (ℵ₁).ord}` +
  `Function.iterate_succ_apply'` avoids any well-founded recursion.
- `choose q hq1 hq2 hqd hqs1 hqs2 using hstep` on a `∃ pair : Set × Set`
  packaged existential gives clean spec lemmas.

## 4. Remaining open (unchanged difficulty)

- Full κ-piece Solovay partition: needs length-ω₁ transfinite bookkeeping
  (the ω-family here has no useful limit stage) — full sessions.
- General regular κ: Jech 8.10 trace analysis for the non-ω-cofinal part
  (vacuous at ω₁).
