/-
  Erdős Problem #131 — Non-Dividing Sets
  Follow-up (oq-01-oq-01-oq-01-oq-04): the rank-2 Davenport LOWER bound

      D(ℤ/aℤ ⊕ ℤ/bℤ) ≥ a + b − 1.

  Source: https://erdosproblems.com/131
  Companion to: `Proofs.Erdos131DavenportConstant` (the EXACT cyclic Davenport
  constant `D(ℤ/nℤ) = n`, proved as an `IsLeast` statement in the genuine
  sequence setting over `ZMod n`).

  NOTE.  This file is deliberately SELF-CONTAINED (only `import Mathlib`); it does
  not import the companions, which keeps it independently verifiable and axiom-free.

  ## Why this is the interesting regime

  For CYCLIC groups the Davenport constant is elementary: `D(ℤ/nℤ) = n` (companion
  file).  The non-trivial theory of the Davenport constant lives in higher RANK.
  The famous result of Olson is

      D(ℤ/aℤ ⊕ ℤ/bℤ) = a + b − 1            (for a ∣ b),

  whose *upper* bound is a substantial combinatorial theorem (NOT in Mathlib).  The
  matching **lower** bound, however, is completely elementary and unconditional, and
  is what we formalize here.

  ## What this file adds

  * `HasZeroSumSubseq` / `DavenportSet` — the same sequence-level definitions as the
    cyclic companion, but for an arbitrary additive group `G`.
  * `davenport_set_mono` — the Davenport set is upward closed: if every length-`m`
    sequence has a nonempty zero-sum subsequence, so does every longer one
    (restrict to a prefix via `Fin.castLE`, then re-embed the witness subset).
  * `witness` — the standard extremal sequence: `e₁ = (1,0)` repeated `a−1` times
    followed by `e₂ = (0,1)` repeated `b−1` times, of length `(a−1)+(b−1) = a+b−2`.
  * `davenport_rank2_witness` — that sequence has NO nonempty zero-sum subsequence.
    Reason: a nonempty subset `s` sums to `(k₁, k₂)` with `k₁ = |s ∩ block₁|` (mod a)
    and `k₂ = |s ∩ block₂|` (mod b); zero forces `a ∣ k₁` with `0 ≤ k₁ ≤ a−1` and
    `b ∣ k₂` with `0 ≤ k₂ ≤ b−1`, hence `k₁ = k₂ = 0`, i.e. `s` is empty.
  * `davenport_rank2_lower` — therefore `a + b − 2 ∉ DavenportSet`, and by upward
    closure the least Davenport length `d` satisfies `a + b − 1 ≤ d`.
  * `davenport_rank2_diag_lower` — the diagonal special case
    `D(ℤ/nℤ ⊕ ℤ/nℤ) ≥ 2n − 1` (sharp, by Olson; the upper half is not formalized).

  All results are unconditional and axiom-free.
-/

import Mathlib

namespace Erdos131DavenportRank2

open Finset

/-- A sequence `f : Fin m → G` *has a nonempty zero-sum subsequence* if some nonempty
index set `s` has `∑ i ∈ s, f i = 0`. -/
def HasZeroSumSubseq {G : Type*} [AddCommMonoid G] {m : ℕ} (f : Fin m → G) : Prop :=
  ∃ s : Finset (Fin m), s.Nonempty ∧ ∑ i ∈ s, f i = 0

/-- The **Davenport set** of `G`: the set of lengths `m` such that *every* length-`m`
sequence over `G` has a nonempty zero-sum subsequence.  The Davenport constant `D(G)`
is the least element of this set. -/
def DavenportSet (G : Type*) [AddCommMonoid G] : Set ℕ :=
  {m | ∀ f : Fin m → G, HasZeroSumSubseq f}

/-- **The Davenport set is upward closed.**  If every length-`m` sequence has a nonempty
zero-sum subsequence, then so does every length-`m'` sequence for `m ≤ m'`.

Proof: restrict `f : Fin m' → G` to its first `m` entries via `Fin.castLE`, obtain a
zero-sum subset `s : Finset (Fin m)`, and re-embed it into `Fin m'` with the order
embedding `Fin.castLEEmb`; `Finset.sum_map` keeps the sum unchanged. -/
theorem davenport_set_mono {G : Type*} [AddCommMonoid G] {m m' : ℕ} (h : m ≤ m')
    (hm : m ∈ DavenportSet G) : m' ∈ DavenportSet G := by
  intro f
  obtain ⟨s, hne, hsum⟩ := hm (fun i => f (Fin.castLE h i))
  refine ⟨s.map (Fin.castLEEmb h), Finset.map_nonempty.mpr hne, ?_⟩
  rw [Finset.sum_map]
  simpa [Fin.coe_castLEEmb] using hsum

/-- The **rank-2 extremal sequence**: `e₁ = (1,0)` repeated `a−1` times, then
`e₂ = (0,1)` repeated `b−1` times.  Length `(a−1)+(b−1) = a+b−2`. -/
def witness (a b : ℕ) : Fin (a - 1 + (b - 1)) → ZMod a × ZMod b :=
  fun i => if (i : ℕ) < a - 1 then (1, 0) else (0, 1)

/-- **No nonempty zero-sum subsequence of the rank-2 witness.**

For `a, b ≥ 1`, the sequence `witness a b` over `ℤ/aℤ ⊕ ℤ/bℤ` has no nonempty
zero-sum subsequence.  A nonempty `s` splits as `s₁ = s ∩ block₁`, `s₂ = s ∩ block₂`;
the two coordinates of `∑_{i∈s} witness a b i` are `(|s₁| : ZMod a)` and
`(|s₂| : ZMod b)`.  Vanishing forces `a ∣ |s₁|` with `|s₁| ≤ a−1` and `b ∣ |s₂|` with
`|s₂| ≤ b−1`, so `|s₁| = |s₂| = 0` and `s = ∅`. -/
theorem davenport_rank2_witness {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ¬ HasZeroSumSubseq (witness a b) := by
  rintro ⟨s, hne, hsum⟩
  -- Coordinatewise description of each term.
  have hfst : ∀ i, (witness a b i).1 = if (i : ℕ) < a - 1 then (1 : ZMod a) else 0 := by
    intro i; unfold witness; by_cases h : (i : ℕ) < a - 1 <;> simp [h]
  have hsnd : ∀ i, (witness a b i).2 = if ¬ ((i : ℕ) < a - 1) then (1 : ZMod b) else 0 := by
    intro i; unfold witness; by_cases h : (i : ℕ) < a - 1 <;> simp [h]
  -- The two coordinates of the (zero) total are the two block-cardinalities, mod a / mod b.
  have hz1 : (∑ i ∈ s, witness a b i).1 = 0 := by rw [hsum]; rfl
  have hz2 : (∑ i ∈ s, witness a b i).2 = 0 := by rw [hsum]; rfl
  have h1 : ((s.filter (fun i : Fin (a - 1 + (b - 1)) => (i : ℕ) < a - 1)).card : ZMod a) = 0 := by
    rw [Prod.fst_sum] at hz1
    simp only [hfst] at hz1
    rwa [Finset.sum_boole] at hz1
  have h2 : ((s.filter (fun i : Fin (a - 1 + (b - 1)) => ¬ ((i : ℕ) < a - 1))).card : ZMod b) = 0 := by
    rw [Prod.snd_sum] at hz2
    simp only [hsnd] at hz2
    rwa [Finset.sum_boole] at hz2
  -- Each block-cardinality is bounded by the block size, so divisibility forces it to 0.
  have hb1 : (s.filter (fun i : Fin (a - 1 + (b - 1)) => (i : ℕ) < a - 1)).card ≤ a - 1 := by
    have key : (s.filter (fun i : Fin (a - 1 + (b - 1)) => (i : ℕ) < a - 1)).card
        ≤ (Finset.range (a - 1)).card := by
      apply Finset.card_le_card_of_injOn (fun i : Fin (a - 1 + (b - 1)) => (i : ℕ))
      · intro i hi
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hi
        simp only [Finset.coe_range, Set.mem_Iio]
        exact hi.2
      · intro x _ y _ hxy; exact Fin.val_injective hxy
    simpa using key
  have hb2 : (s.filter (fun i : Fin (a - 1 + (b - 1)) => ¬ ((i : ℕ) < a - 1))).card ≤ b - 1 := by
    have key : (s.filter (fun i : Fin (a - 1 + (b - 1)) => ¬ ((i : ℕ) < a - 1))).card
        ≤ (Finset.range (b - 1)).card := by
      apply Finset.card_le_card_of_injOn (fun i : Fin (a - 1 + (b - 1)) => (i : ℕ) - (a - 1))
      · intro i hi
        simp only [Finset.coe_filter, Set.mem_setOf_eq, not_lt] at hi
        simp only [Finset.coe_range, Set.mem_Iio]
        have := i.isLt
        omega
      · intro x hx y hy hxy
        simp only [Finset.coe_filter, Set.mem_setOf_eq, not_lt] at hx hy
        replace hxy : (↑x : ℕ) - (a - 1) = (↑y : ℕ) - (a - 1) := hxy
        apply Fin.val_injective
        omega
    simpa using key
  have hc1 : (s.filter (fun i : Fin (a - 1 + (b - 1)) => (i : ℕ) < a - 1)).card = 0 := by
    rcases Nat.eq_zero_or_pos
        (s.filter (fun i : Fin (a - 1 + (b - 1)) => (i : ℕ) < a - 1)).card with h0 | hpos
    · exact h0
    · exact absurd ((ZMod.natCast_eq_zero_iff _ _).mp h1)
        (Nat.not_dvd_of_pos_of_lt hpos (by omega))
  have hc2 : (s.filter (fun i : Fin (a - 1 + (b - 1)) => ¬ ((i : ℕ) < a - 1))).card = 0 := by
    rcases Nat.eq_zero_or_pos
        (s.filter (fun i : Fin (a - 1 + (b - 1)) => ¬ ((i : ℕ) < a - 1))).card with h0 | hpos
    · exact h0
    · exact absurd ((ZMod.natCast_eq_zero_iff _ _).mp h2)
        (Nat.not_dvd_of_pos_of_lt hpos (by omega))
  -- The two blocks partition `s`, so `s` is empty — contradicting nonemptiness.
  have hsplit : (s.filter (fun i : Fin (a - 1 + (b - 1)) => (i : ℕ) < a - 1)).card
      + (s.filter (fun i : Fin (a - 1 + (b - 1)) => ¬ ((i : ℕ) < a - 1))).card = s.card :=
    Finset.filter_card_add_filter_neg_card_eq_card _
  have hcard0 : s.card = 0 := by omega
  exact absurd (Finset.card_pos.mpr hne) (by omega)

/-- **Rank-2 Davenport lower bound: `D(ℤ/aℤ ⊕ ℤ/bℤ) ≥ a + b − 1`.**

If `d` is the least Davenport length for `ℤ/aℤ ⊕ ℤ/bℤ`, then `a + b − 1 ≤ d`.  Were
`d ≤ a + b − 2`, upward closure (`davenport_set_mono`) would put `a + b − 2` in the
Davenport set, contradicting `davenport_rank2_witness`. -/
theorem davenport_rank2_lower {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    {d : ℕ} (hd : IsLeast (DavenportSet (ZMod a × ZMod b)) d) :
    a + b - 1 ≤ d := by
  by_contra hlt
  push_neg at hlt
  have hdle : d ≤ a - 1 + (b - 1) := by omega
  have hmem : (a - 1 + (b - 1)) ∈ DavenportSet (ZMod a × ZMod b) :=
    davenport_set_mono hdle hd.1
  exact davenport_rank2_witness ha hb (hmem (witness a b))

/-- **Diagonal special case: `D(ℤ/nℤ ⊕ ℤ/nℤ) ≥ 2n − 1`.**

This bound is sharp — Olson's theorem gives `D(ℤ/nℤ ⊕ ℤ/nℤ) = 2n − 1` — but the
matching upper bound is a substantial result not formalized here (and not in Mathlib). -/
theorem davenport_rank2_diag_lower {n : ℕ} (hn : 1 ≤ n)
    {d : ℕ} (hd : IsLeast (DavenportSet (ZMod n × ZMod n)) d) :
    2 * n - 1 ≤ d := by
  have := davenport_rank2_lower hn hn hd
  omega

end Erdos131DavenportRank2
