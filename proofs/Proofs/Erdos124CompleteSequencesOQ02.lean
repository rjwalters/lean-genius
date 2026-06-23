import Mathlib

/-
# Erdős Problem 124 — Follow-up OQ-02: A Counting Necessity (Density Obstruction)

## Context

The parent file `Erdos124CompleteSequences.lean` proves the **sufficiency** half of
Erdős Problem 124 (the "weak version", solved by Harmonic's Aristotle in 2025):

> If `d₁, …, dₖ ≥ 2` and `∑ᵢ 1/(dᵢ − 1) ≥ 1`, then **every** natural number `n` can be
> written as `n = ∑ᵢ aᵢ` where each `aᵢ` has only the digits `0` and `1` in base `dᵢ`.

This file proves a **necessity** counterpart: a hard *counting* (density) obstruction
that explains why a hypothesis on the bases is unavoidable.

## The characterization used

A natural number `a` "has only digits `0` and `1` in base `d`" **iff** `a` is a sum of
*distinct* powers of `d`, i.e. `a = ∑_{j ∈ S} dʲ` for some finite set `S` of exponents.
(The bijection sends the set `S` of positions carrying digit `1` to the value.)  We take
this subset-sum form, `RepBase`, as the definition; it is the same set of numbers as the
`(Nat.digits d a).toFinset ⊆ {0,1}` formulation used in the parent file.

## The result

Let `Lᵢ(N) = #{ j : dᵢʲ < N }` be the number of powers of `dᵢ` strictly below `N`.
Each base-`dᵢ` summand below `N` is a subset-sum of those `Lᵢ(N)` powers, so there are at
most `2^{Lᵢ(N)}` possible values for it. Since a representation `n = ∑ᵢ aᵢ` *determines*
`n`, the map `n ↦ (a₁, …, aₖ)` is injective. Therefore:

  **(counting_necessity)**  If every `n < N` is representable, then
        `N ≤ ∏ᵢ 2^{Lᵢ(N)}`.

This is a genuine obstruction, distinct from (and complementary to) the parent's
sufficiency theorem: representing an entire initial segment `[0, N)` forces the bases to
be "dense enough" in a counting sense. As a concrete instance, a single base `3` cannot
represent all of `[0, 8)` (the bound gives `8 ≤ 2² = 4`, impossible), whereas base `2`
saturates the bound (`8 ≤ 2³ = 8`), matching ordinary binary representation.

## Status
- Self-contained, imports only Mathlib. No `sorry`, no extra axioms.
-/

namespace Erdos124OQ02

open Finset

/-- `RepBase d a`: the number `a` is a sum of *distinct* powers of `d`; equivalently,
`a` has only the digits `0` and `1` when written in base `d`. -/
def RepBase (d a : ℕ) : Prop := ∃ S : Finset ℕ, a = ∑ j ∈ S, d ^ j

/-- `Rep d a`: `a = ∑ᵢ fᵢ` with each summand `fᵢ` having `0/1` digits in base `d i`.
This is exactly the conclusion shape of Erdős 124. -/
def Rep {k : ℕ} (d : Fin k → ℕ) (a : ℕ) : Prop :=
  ∃ f : Fin k → ℕ, (∀ i, RepBase (d i) (f i)) ∧ a = ∑ i, f i

/-- `powExps d N`: the exponents `j` whose power `dʲ` is still `< N`. -/
def powExps (d N : ℕ) : Finset ℕ := (range N).filter (fun j => d ^ j < N)

/-- The set of values `< N` of the form "sum of distinct powers of `d`", described
explicitly as the image of the powerset of `powExps d N`. -/
def valSet (d N : ℕ) : Finset ℕ :=
  (powExps d N).powerset.image (fun S => ∑ j ∈ S, d ^ j)

@[simp] lemma repBase_zero (d : ℕ) : RepBase d 0 := ⟨∅, by simp⟩

/-- `0` is always representable (empty representation). -/
lemma rep_zero {k : ℕ} (d : Fin k → ℕ) : Rep d 0 := ⟨fun _ => 0, fun _ => repBase_zero _, by simp⟩

/-- **Key counting lemma.** If `a` is a sum of distinct powers of `d` (base `d ≥ 2`)
and `a < N`, then `a` lies in the explicitly bounded set `valSet d N`. -/
lemma mem_valSet_of_repBase {d a N : ℕ} (hd : 2 ≤ d) (ha : RepBase d a) (haN : a < N) :
    a ∈ valSet d N := by
  obtain ⟨S, hS⟩ := ha
  -- Every exponent actually used lies in `powExps d N`.
  have hsub : S ⊆ powExps d N := by
    intro j hj
    have hpow_le : d ^ j ≤ a := by
      rw [hS]; exact Finset.single_le_sum (by intro i _; positivity) hj
    have hpow_lt : d ^ j < N := lt_of_le_of_lt hpow_le haN
    have hj_lt : j < N := by
      have h2 : 2 ^ j ≤ d ^ j := Nat.pow_le_pow_left hd j
      have h3 : j < 2 ^ j := Nat.lt_two_pow_self
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj_lt, hpow_lt⟩
  exact Finset.mem_image.mpr ⟨S, Finset.mem_powerset.mpr hsub, hS.symm⟩

/-- `valSet d N` has at most `2^{|powExps d N|}` elements. -/
lemma card_valSet_le (d N : ℕ) : (valSet d N).card ≤ 2 ^ (powExps d N).card := by
  calc (valSet d N).card ≤ (powExps d N).powerset.card := Finset.card_image_le
    _ = 2 ^ (powExps d N).card := Finset.card_powerset _

/-- **Counting necessity for Erdős 124 (density obstruction).**

If `d₁,…,dₖ ≥ 2` and every `n < N` is representable as a sum `∑ᵢ aᵢ` with each `aᵢ` a sum
of distinct powers of `dᵢ`, then
  `N ≤ ∏ᵢ 2^{Lᵢ(N)}`,  where  `Lᵢ(N) = #{ j : dᵢʲ < N }`.
Equivalently `N ≤ 2^{∑ᵢ Lᵢ(N)}`. This bounds how long an initial segment the bases can
cover, and hence shows the parent's reciprocal-sum hypothesis cannot be dropped. -/
theorem counting_necessity {k : ℕ} (d : Fin k → ℕ) (N : ℕ)
    (hd : ∀ i, 2 ≤ d i) (hrep : ∀ n < N, Rep d n) :
    N ≤ ∏ i, 2 ^ (powExps (d i) N).card := by
  -- Choose a representation for every `n < N`.
  have hrep' : ∀ n : ℕ, n < N → ∃ f : Fin k → ℕ,
      (∀ i, RepBase (d i) (f i)) ∧ n = ∑ i, f i := hrep
  choose! F hFrep hFsum using hrep'
  -- The product of the bounding finsets.
  set V : Fin k → Finset ℕ := fun i => valSet (d i) N with hV
  -- The injective coordinate map `n ↦ (Fᵢ n)`.
  let φ : ℕ → (Fin k → ℕ) := fun n => if n < N then F n else (fun _ => 0 : Fin k → ℕ)
  have hmaps : ∀ n ∈ range N, φ n ∈ Fintype.piFinset V := by
    intro n hn
    have hnN : n < N := Finset.mem_range.mp hn
    rw [Fintype.mem_piFinset]
    intro i
    have hφ : φ n = F n := if_pos hnN
    rw [hφ]
    -- `F n i` is base-`dᵢ` representable and `< N`, so it is in `valSet (d i) N`.
    have hlt : F n i < N := by
      have hle : F n i ≤ ∑ j, F n j :=
        Finset.single_le_sum (by intro j _; positivity) (Finset.mem_univ i)
      have := hFsum n hnN
      omega
    exact mem_valSet_of_repBase (hd i) (hFrep n hnN i) hlt
  have hinj : Set.InjOn φ (range N) := by
    intro m hm n hn hmn
    have hmN : m < N := Finset.mem_range.mp hm
    have hnN : n < N := Finset.mem_range.mp hn
    have hφm : φ m = F m := if_pos hmN
    have hφn : φ n = F n := if_pos hnN
    have hsumm := hFsum m hmN
    have hsumn := hFsum n hnN
    rw [hsumm, hsumn]
    rw [hφm, hφn] at hmn
    rw [hmn]
  -- Cardinality chain.
  have hcard : (range N).card ≤ (Fintype.piFinset V).card :=
    Finset.card_le_card_of_injOn φ hmaps hinj
  rw [Finset.card_range, Fintype.card_piFinset] at hcard
  refine le_trans hcard ?_
  apply Finset.prod_le_prod'
  intro i _
  exact card_valSet_le (d i) N

/-- **Single-base specialization.** For a single base `d ≥ 2`, if every `n < N` is a sum
of distinct powers of `d`, then `N ≤ 2^{L}` with `L = #{ j : dʲ < N }`. -/
theorem counting_necessity_single {d N : ℕ} (hd : 2 ≤ d)
    (hrep : ∀ n < N, RepBase d n) :
    N ≤ 2 ^ (powExps d N).card := by
  have hsub : (range N) ⊆ valSet d N := by
    intro n hn
    have hnN : n < N := Finset.mem_range.mp hn
    exact mem_valSet_of_repBase hd (hrep n hnN) hnN
  calc N = (range N).card := (Finset.card_range N).symm
    _ ≤ (valSet d N).card := Finset.card_le_card hsub
    _ ≤ 2 ^ (powExps d N).card := card_valSet_le d N

/-! ### Concrete instances of the obstruction -/

/-- For base `3` below `8`, only `3⁰ = 1` and `3¹ = 3` are powers `< 8`. -/
lemma powExps_three_eight : (powExps 3 8).card = 2 := by decide

/-- For base `2` below `8`, the powers `< 8` are `1, 2, 4`. -/
lemma powExps_two_eight : (powExps 2 8).card = 3 := by decide

/-- **Concrete density obstruction.** A *single* base `3` cannot represent every number
in `[0, 8)` as a sum of distinct powers of `3`: the counting bound forces `8 ≤ 2² = 4`,
which is false. (Indeed `2`, `5`, `6`, `7` are missing.) -/
theorem base_three_cannot_cover_eight : ¬ (∀ n < 8, RepBase 3 n) := by
  intro h
  have hbound := counting_necessity_single (d := 3) (N := 8) (by norm_num) h
  rw [powExps_three_eight] at hbound
  norm_num at hbound

/-- **Tightness at base `2`.** The bound `N ≤ 2^{L}` is sharp: at `N = 8`, base `2` gives
`L = 3` and `2³ = 8 = N`, matching ordinary binary representation. -/
theorem base_two_bound_tight : (8 : ℕ) ≤ 2 ^ (powExps 2 8).card := by
  rw [powExps_two_eight]; norm_num

end Erdos124OQ02
