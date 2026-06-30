# Erdős #131 — Rank-2 Davenport Lower Bound `D(ℤ/aℤ ⊕ ℤ/bℤ) ≥ a + b − 1`

**Slug:** `erdos-131-oq-01-oq-01-oq-01-oq-04`
**Lean file:** `proofs/Proofs/Erdos131DavenportRank2.lean` (namespace `Erdos131DavenportRank2`)
**Status:** verified · 0 axioms · 0 sorries · 4 theorems · 3 definitions · 180 lines

## Summary

The **Davenport constant** `D(G)` of a finite abelian group `G` is the least `d` such
that every length-`d` sequence over `G` has a nonempty zero-sum subsequence. For
**cyclic** groups it is elementary — `D(ℤ/nℤ) = n` (companion entry
`erdos-131-oq-01-oq-01-oq-01-oq-03`). The non-trivial theory lives in higher **rank**:
Olson's theorem states

> `D(ℤ/aℤ ⊕ ℤ/bℤ) = a + b − 1`   (for `a ∣ b`),

whose *upper* bound is a substantial combinatorial theorem (not in Mathlib). This entry
formalizes the matching **lower** bound — completely elementary and unconditional:

> `davenport_rank2_lower : IsLeast (DavenportSet (ZMod a × ZMod b)) d → a + b − 1 ≤ d`.

## Proof architecture

Two reusable pieces, both stated for the group-agnostic predicate
`HasZeroSumSubseq f := ∃ s, s.Nonempty ∧ ∑ i ∈ s, f i = 0` and the set
`DavenportSet G := {m | ∀ f : Fin m → G, HasZeroSumSubseq f}`:

1. **`witness` + `davenport_rank2_witness` (the extremal sequence).**
   `witness a b : Fin (a−1+(b−1)) → ZMod a × ZMod b` is `e₁ = (1,0)` repeated `a−1`
   times then `e₂ = (0,1)` repeated `b−1` times (length `a+b−2`). It has no nonempty
   zero-sum subsequence: for a nonempty index set `s`, the two coordinates of
   `∑_{i∈s} witness a b i` are `(|s₁| : ZMod a)` and `(|s₂| : ZMod b)` where
   `s₁ = s ∩ block₁`, `s₂ = s ∩ block₂` (via `Prod.fst_sum`/`Prod.snd_sum` then
   `Finset.sum_boole`). Vanishing forces `a ∣ |s₁|`, `b ∣ |s₂|`; with `|s₁| ≤ a−1`
   and `|s₂| ≤ b−1` (each block injects into `Finset.range` by `Fin.val` resp.
   `Fin.val − (a−1)`), both cardinalities are `0`, so `s = ∅` — contradiction.

2. **`davenport_set_mono` (upward closure).** `m ≤ m'` and `m ∈ DavenportSet G ⟹
   m' ∈ DavenportSet G`: restrict a length-`m'` sequence to its first `m` entries
   via `Fin.castLE`, get a zero-sum subset in `Fin m`, re-embed into `Fin m'` along
   `Fin.castLEEmb` with `Finset.sum_map` preserving the sum.

Combining: if the least Davenport length `d ≤ a+b−2`, monotonicity puts `a+b−2` in the
Davenport set, contradicting the witness. Hence `a+b−1 ≤ d`.

`davenport_rank2_diag_lower` specializes to `D(ℤ/nℤ ⊕ ℤ/nℤ) ≥ 2n − 1`.

## Lean gotchas encountered (Mathlib v4.26.0)

- **Binder-type ambiguity.** Writing the filter predicate as `fun i => (i : ℕ) < a − 1`
  lets Lean infer `i : ℕ` (taking `↑i = i`), making `s.filter` expect `Finset ℕ` and
  producing "Application type mismatch ... expected Finset ℕ". Fix: annotate every
  filter binder explicitly, `fun i : Fin (a − 1 + (b − 1)) => …`.
- **`set L := a−1+(b−1)` backfires.** Folding the length into an abbreviation broke
  `rw [hsum]` (syntactic pattern no longer found) and made `omega` lose the
  `i.isLt : ↑i < a−1+(b−1)` bound. Keep the literal expression instead.
- **`card_le_card_of_injOn` is `Set`-valued.** Its `MapsTo`/`InjOn` hypotheses range
  over `↑s` (the coe to `Set`), so `Finset.mem_filter` makes no progress on the intro'd
  membership; use `simp only [Finset.coe_filter, Set.mem_setOf_eq, not_lt]` and
  `simp only [Finset.coe_range, Set.mem_Iio]` on the goal.
- **`omega` needs a beta-reduced hypothesis.** In the `InjOn` goal the equality
  `hxy : (fun i => ↑i − (a−1)) x = (fun i => ↑i − (a−1)) y` stays as an opaque lambda
  application, invisible to `omega`. `replace hxy : (↑x:ℕ) − (a−1) = (↑y:ℕ) − (a−1) := hxy`
  (defeq beta) exposes it; nat-subtraction injectivity then needs the `a−1 ≤ ↑x`,
  `a−1 ≤ ↑y` bounds from the filter membership.

## Open questions (see meta.json)

1. **(high)** The matching Olson upper bound `D(ℤ/aℤ ⊕ ℤ/bℤ) ≤ a + b − 1` — is there an
   elementary axiom-free Lean proof, or does it require the group-algebra polynomial method?
2. **(medium)** General-rank lower bound `D(⨁ᵢ ℤ/nᵢ) ≥ 1 + Σ(nᵢ − 1)` by concatenating
   `k` coordinate blocks — cleanest Lean encoding of the indexed direct sum?

## Relationship to other entries

- **Extends** `erdos-131-oq-01-oq-01-oq-01-oq-03` (exact cyclic constant `D(ℤ/nℤ) = n`):
  answers its open question `…-oq-03-oq-01` for the rank-2 lower bound.
- Self-contained (`import Mathlib` only); does not import the cyclic companion, so it is
  independently verifiable and axiom-free.
