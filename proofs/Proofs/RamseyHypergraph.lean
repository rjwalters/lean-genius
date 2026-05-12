import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic

/-
# Ramsey Numbers for k-Uniform Hypergraphs (OQ-03 of erdos-szekeres)

## What This Establishes

Erdős–Szekeres (Wiedijk #73, formalized in `Proofs/ErdosSzekeres.lean`) is the
*sequence* refinement of graph Ramsey (`k = 2`). OQ-03 of `erdos-szekeres` asks
for the generalization to `k`-uniform hypergraphs: for `k ≥ 2`, define the
diagonal hypergraph Ramsey number `R_k(s,t)` as the least `n` such that every
2-coloring of `[n]^{(k)}` (the `k`-subsets of `{0,...,n-1}`) contains a
monochromatic `s`-clique of one color or a monochromatic `t`-clique of the
other.

This file is the **S2 scaffold** — it sets up the API and states the main
existence theorem (`ramsey_existence`, OQ-03a) as a `sorry`. The two-layer
neighborhood induction (Ramsey 1930) and the Erdős–Rado tower upper bound
(OQ-03b) are deferred to later sessions per
`research/problems/erdos-szekeres-oq-03/state.md`.

## Status

- [x] Definitions: `kColoring`, `IsMonochromatic`, `IsRamsey`, `ramseyNumber`.
- [x] `IsMonochromatic_of_card_lt_k`: any subset smaller than `k` is trivially
  monochromatic of every color (the `powersetCard` is empty).
- [x] `is_ramsey_zero_clique`: the degenerate `s = 0` case (every coloring has
  a `0`-clique).
- [ ] `ramsey_existence` (OQ-03a): the main result, stated as `sorry`. Proof
  strategy in `state.md`.
- [ ] `ramseyNumber_one` (k=1 pigeonhole sanity check): stated as `sorry` and
  scheduled for S3 alongside the existence theorem.

## Approach

- We model `k`-subsets of `{0,...,n-1}` as elements of
  `(Finset.univ : Finset (Fin n)).powersetCard k`, and a 2-coloring as
  `Finset (Fin n) → Bool` (only the values on `k`-subsets matter for
  `IsMonochromatic`).
- `ramseyNumber k s t` is defined as `sInf {n | IsRamsey n k s t}`; for
  parameter values where the set is empty (e.g. degenerate inputs), this
  returns `0`. Once `ramsey_existence` is proved, the value is the true
  Ramsey number for all `k ≥ 2`, `s, t ≥ k`.

## References

- F. P. Ramsey, *On a problem of formal logic*, Proc. London Math. Soc. (2)
  30 (1930), 264–286 — original proof of OQ-03a.
- P. Erdős, R. Rado, *A partition calculus in set theory*, Bull. AMS 62
  (1956), 427–489 — the tower upper bound (OQ-03b).
- P. Erdős, A. Hajnal, *On Ramsey like theorems*, Combinatorics (Oxford 1972),
  123–140 — stepping-up lower bound (OQ-03c).
-/

namespace RamseyK

open Finset

/-- A 2-coloring of the `k`-subsets of `{0,...,n-1}`. We model it as a
function on all of `Finset (Fin n)`; only the values on subsets of cardinality
`k` are inspected by `IsMonochromatic`. -/
abbrev kColoring (n : ℕ) := Finset (Fin n) → Bool

/-- A subset `S ⊆ {0,...,n-1}` is **monochromatic of color `c`** for a coloring
`χ` at uniformity `k` if every `k`-subset of `S` is colored `c`. -/
def IsMonochromatic {n : ℕ} (χ : kColoring n) (k : ℕ)
    (S : Finset (Fin n)) (c : Bool) : Prop :=
  ∀ T ∈ S.powersetCard k, χ T = c

/-- The **Ramsey condition** `IsRamsey n k s t`: every 2-coloring of the
`k`-subsets of `{0,...,n-1}` contains either a monochromatic `false` `s`-clique
or a monochromatic `true` `t`-clique. -/
def IsRamsey (n k s t : ℕ) : Prop :=
  ∀ χ : kColoring n,
    (∃ S : Finset (Fin n), S.card = s ∧ IsMonochromatic χ k S false) ∨
    (∃ S : Finset (Fin n), S.card = t ∧ IsMonochromatic χ k S true)

/-- The **k-uniform hypergraph Ramsey number**: the least `n` such that
`IsRamsey n k s t` holds. By `sInf` convention on `ℕ`, this is `0` if no
such `n` exists; once `ramsey_existence` is proved for `k ≥ 2`, `s, t ≥ k`,
this returns the true Ramsey number. -/
noncomputable def ramseyNumber (k s t : ℕ) : ℕ :=
  sInf {n | IsRamsey n k s t}

/-- A subset smaller than the uniformity `k` has no `k`-subsets and is
trivially monochromatic of every color. -/
lemma isMonochromatic_of_card_lt {n k : ℕ} (χ : kColoring n)
    (S : Finset (Fin n)) (c : Bool) (h : S.card < k) :
    IsMonochromatic χ k S c := by
  intro T hT
  rw [Finset.mem_powersetCard] at hT
  obtain ⟨hTsub, hTcard⟩ := hT
  have hTle : T.card ≤ S.card := Finset.card_le_card hTsub
  exfalso
  omega

/-- (OQ-03a) **Ramsey's hypergraph theorem.** For every uniformity `k ≥ 2`
and every pair of target sizes `s, t ≥ k`, there is a finite `n` such that
every 2-coloring of `[n]^{(k)}` contains a monochromatic `s`- or `t`-clique.

This is the main result of the OQ-03 entry. The proof (Ramsey 1930) is by
two-layer induction on `k` and `s + t`; see `state.md` for the strategy.
Deferred to S3. -/
theorem ramsey_existence (k s t : ℕ) (hk : 2 ≤ k) (hs : k ≤ s) (ht : k ≤ t) :
    ∃ n, IsRamsey n k s t := by
  sorry

/-- The empty set is a `0`-clique, monochromatic of every color. -/
lemma isMonochromatic_empty_zero {n k : ℕ} (χ : kColoring n) (c : Bool)
    (hk : 1 ≤ k) :
    IsMonochromatic χ k (∅ : Finset (Fin n)) c := by
  apply isMonochromatic_of_card_lt
  rw [Finset.card_empty]
  exact hk

/-- Degenerate base case: when the `false`-target size is `0`, every coloring
trivially has a `0`-monochromatic `false` "clique" — the empty set. Hence
`IsRamsey n k 0 t` holds for all `n, k, t` with `k ≥ 1`. -/
lemma is_ramsey_zero_false (n k t : ℕ) (hk : 1 ≤ k) : IsRamsey n k 0 t := by
  intro χ
  refine Or.inl ⟨∅, ?_, ?_⟩
  · exact Finset.card_empty
  · exact isMonochromatic_empty_zero χ false hk

/-- Symmetric degenerate base case for the `true`-target. -/
lemma is_ramsey_zero_true (n k s : ℕ) (hk : 1 ≤ k) : IsRamsey n k s 0 := by
  intro χ
  refine Or.inr ⟨∅, ?_, ?_⟩
  · exact Finset.card_empty
  · exact isMonochromatic_empty_zero χ true hk

/-- (k=1 sanity check, scheduled for S3.) The `k = 1` Ramsey number is the
pigeonhole bound `s + t - 1`. Stated here for the API; proof deferred to S3
(it needs both the pigeonhole-forward direction and an explicit bad coloring
for the lower bound).

The forward direction (showing `IsRamsey (s+t-1) 1 s t` via `Finset.filter`
counting) is straightforward; the reverse `¬ IsRamsey (s+t-2) 1 s t` requires
constructing the coloring with `s-1` `false`-singletons and `t-1`
`true`-singletons. -/
theorem ramseyNumber_one (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    ramseyNumber 1 s t = s + t - 1 := by
  sorry

end RamseyK
