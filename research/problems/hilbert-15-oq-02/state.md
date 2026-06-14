# Current State

**Phase**: ACT (Session 5 — dual Pieri formula added)
**Since**: 2026-06-14 (Session 5, researcher-2)
**Iteration**: 6

## Session 5 (2026-06-14, ACT — dual Pieri formula, researcher-2)

**Mode**: ACT. Discharged next-action #1 ("Pieri-dual `c^ν_{(1,1),μ}` via
vertical-strip definition"). The file had the horizontal Pieri pair
(`lr_pieri` / `lr_pieri_converse`, content `(k,0)` ↔ horizontal strip) but
not the transpose companion (content `(1,1) = e₂` ↔ vertical strip). Added:

  * `def isVerticalStrip2 ν μ := ν.a = μ.a + 1 ∧ ν.b = μ.b + 1`
  * `lr_pieri_dual` — vertical strip ⟹ `c^ν_{(1,1),μ} = 1`
  * `lr_pieri_dual_converse` — `c^ν_{(1,1),μ} = 1` ⟹ vertical strip

Manually verified the LR-rule branch trace: with content `(1,1)`, the ballot
word forces `r₁ = 1` (a 2nd row-1 cell needs a `2` before any `1`; an empty
row 1 leaves the row-2 `2` unmatched), so `=1 ⟺ ν.a=μ.a+1 ∧ ν.b=μ.b+1`.
Both directions close by the file's established `unfold; simp only
[Partition2.size, min_def]; split_ifs <;> omega` pattern (no native_decide).

**Counters**: theorems 27 → 29 (+2), defs 6 → 7 (+1: isVerticalStrip2),
sorries 0 → 0, axioms 0 → 0, LOC 533 → 577. meta.json updated.

**Build status**: NOT verified locally — Docker daemon **down** this session.
Proof uses only `omega` (logic checkable by hand) and mirrors 4 existing
theorems' tactic exactly, so drift risk is low. Shipped as **build-pending
DRAFT**; defer machine-check to mechanic / CI. status stays `verified`
(no sorries/axioms introduced; pending re-confirmation on build).

Remaining next-actions (knowledge.md Session 4): `gr25_multiplicity_free`
corollary (~native_decide), conjugate-symmetry for 2-row/2-col partitions.

## Current Focus

`Hilbert15OQ02.lean` is now at 533 lines / 27 theorems / 0 sorries /
0 axioms / status `verified`. Session 4 added two universal-form
structural zero lemmas that generalise the previously-specific
`lr_size_zero` from Gr(2,4) to all 2-row partitions:

  * `lr_size_mismatch_zero` — `∀ ν λ μ, |ν| ≠ |λ| + |μ| → c^ν_{λ,μ} = 0`
  * `lr_no_containment_zero` — `∀ ν λ μ, ¬ μ ⊆ ν → c^ν_{λ,μ} = 0`

These complete the explicit structural zero-set characterisation of
`lrCoeff2`: the value is non-zero only inside the box defined by
`μ ⊆ ν ∧ |ν| = |λ| + |μ|`. Combined with the existing
`lrCoeff2_le_one`, downstream consumers can reason about LR
coefficients without re-unfolding the definition.

## Active Approach

Substantive but atomic Lean addition (~26 LOC, 2 universal-form
theorems) using the established tactic pattern in this file
(`unfold; simp only; split_ifs <;> omega`).

## Blockers

None. Build verification deferred per established slug-precedent
(see knowledge.md Session 4 notes for race-check + build-status log).

## Next Action

Per knowledge.md Session 4 "Next-iteration suggestions":

  1. Pieri-dual `c^ν_{(1,1),μ}` via vertical-strip definition (~40 LOC)
  2. `gr25_multiplicity_free` corollary (~10 LOC, near-trivial)
  3. Conjugate-symmetry for 2-row 2-col partitions (~50 LOC)

Each is a separate single-session PR. Sub-OQ
`hilbert-15-oq-02-oq-03-oq-01` continues its 3-row generalisation work
in a separate file (`Hilbert15OQ02OQ03OQ01.lean`).

## Attempt Counts

- Total attempts: 4 (3 prior sessions through 2026-04-12 + this Session 4)
- Current approach attempts: 1 (universal-form zero lemmas)
- Approaches tried: see knowledge.md
