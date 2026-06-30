import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ENNReal.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Proofs.BinomialTheoremOQ02OQ01OQ01OQ01

/-
# Multinomial PMF Integration with Mathlib's PMF Framework

## Open Question
"Can the full PMF.multinomial be integrated into Mathlib's PMF framework?"

## Answer
**Yes.** We construct a `PMF` instance for the multinomial distribution by:
1. Defining the support type as the set of compositions of n into k parts
2. Constructing the PMF via `PMF.ofFinset` using the multinomial probabilities
3. Proving the normalization condition from the multinomial theorem
4. Deriving the marginal distributions as binomial PMFs

Mathlib's `PMF` type requires:
- A function `α → ℝ≥0∞` (probability mass function)
- A proof that `∑' a, f a = 1` (normalization)

The multinomial theorem provides the normalization proof directly.

## Dependencies
- BinomialTheoremOQ02OQ01: multinomialProb, multinomialProb_sum_eq_one
- Mathlib: PMF, Nat.multinomial, ENNReal, piAntidiag
-/

namespace BinomialTheoremOQ02OQ01OQ01

open Finset BigOperators MeasureTheory
open scoped ENNReal Nat

-- ============================================================
-- PART 1: The Composition Type (Support of Multinomial)
-- ============================================================

/-- A composition of n into parts indexed by s: a function k : α → ℕ
    with ∑ k(i) = n for i ∈ s. This is the support of the multinomial. -/
structure Composition (α : Type*) [DecidableEq α] (s : Finset α) (n : ℕ) where
  /-- The count function: how many of each outcome -/
  counts : α → ℕ
  /-- The counts sum to n -/
  sum_eq : ∑ i ∈ s, counts i = n
  /-- Counts outside s are zero -/
  counts_outside : ∀ a, a ∉ s → counts a = 0

/-- Helper: two Compositions with equal count functions are equal. -/
private theorem Composition.ext_counts {α : Type*} [DecidableEq α] {s : Finset α} {n : ℕ}
    {a b : Composition α s n} (h : a.counts = b.counts) : a = b := by
  obtain ⟨ca, ha1, ha2⟩ := a
  obtain ⟨cb, hb1, hb2⟩ := b
  subst h; rfl

/-- The set of all compositions of n into parts indexed by s is finite,
    via bijection with the `piAntidiag s n` finset. -/
instance (α : Type*) [DecidableEq α] (s : Finset α) (n : ℕ) :
    Fintype (Composition α s n) :=
  Fintype.ofEquiv ↥(s.piAntidiag n) {
    toFun := fun fh =>
      let h := Finset.mem_piAntidiag.mp fh.2
      { counts := fh.1, sum_eq := h.1,
        counts_outside := fun a ha => by_contra fun hne => ha (h.2 a hne) }
    invFun := fun c =>
      ⟨c.counts, Finset.mem_piAntidiag.mpr
        ⟨c.sum_eq, fun i hi => by_contra fun h => hi (c.counts_outside i h)⟩⟩
    left_inv := fun fh => Subtype.ext rfl
    right_inv := fun c => Composition.ext_counts rfl }

-- ============================================================
-- PART 2: Multinomial PMF as ENNReal Function
-- ============================================================

/-- The multinomial PMF as a function to ℝ≥0∞ (extended nonneg reals).
    This is the type required by Mathlib's PMF framework.

    For a probability vector p on alphabet s and n trials:
    f(k) = multinomial(s, k.counts) · ∏ p(i) ^ k.counts(i) -/
noncomputable def multinomialPMFVal {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ≥0∞) (n : ℕ)
    (k : Composition α s n) : ℝ≥0∞ :=
  (Nat.multinomial s k.counts : ℝ≥0∞) * ∏ i ∈ s, p i ^ k.counts i

-- ============================================================
-- PART 3: Normalization (The Key Step)
-- ============================================================

/-- **Normalization of Multinomial PMF in ENNReal**

    The sum of multinomial probabilities over all compositions equals 1,
    provided ∑ p(i) = 1.

    This is the multinomial theorem expressed in ENNReal:
    (∑ p(i))^n = ∑_{k:comp(n)} multinomial(s,k) · ∏ p(i)^k(i) = 1

    This is the critical step for constructing a PMF instance. -/
theorem multinomialPMF_sum_eq_one {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ≥0∞) (n : ℕ)
    (hp : ∑ i ∈ s, p i = 1) :
    ∑ k : Composition α s n, multinomialPMFVal s p n k = 1 := by
  -- Anonymous record-wise equivalence to the sibling file's Composition type.
  -- Both Composition structures have identical fields (counts, sum_eq,
  -- counts_outside); the only reason for the bridge is namespace separation.
  let e : Composition α s n ≃ CompositionFintype.Composition α s n :=
    { toFun := fun c => ⟨c.counts, c.sum_eq, c.counts_outside⟩
      invFun := fun c => ⟨c.counts, c.sum_eq, c.counts_outside⟩
      left_inv := fun c => by cases c; rfl
      right_inv := fun c => by cases c; rfl }
  -- Step 1: transfer the Composition-indexed sum via the equivalence; the
  -- summand is preserved pointwise because the bridge is the identity on
  -- the underlying `counts` field, and `multinomialPMFVal` only reads `counts`.
  rw [Fintype.sum_equiv e
        (fun c => multinomialPMFVal s p n c)
        (fun c => (Nat.multinomial s c.counts : ℝ≥0∞)
                    * ∏ i ∈ s, p i ^ c.counts i)
        (fun _ => rfl)]
  -- Step 2: use the sibling's bridge to land on a piAntidiag sum.
  rw [CompositionFintype.sum_composition_eq_piAntidiag_sum (M := ℝ≥0∞) s n
        (fun k => (Nat.multinomial s k : ℝ≥0∞) * ∏ i ∈ s, p i ^ k i)]
  -- Step 3: fold the piAntidiag sum into a power via Mathlib's multinomial theorem.
  rw [← Finset.sum_pow_eq_sum_piAntidiag s p n]
  -- Step 4: substitute ∑ p = 1 and 1^n = 1.
  rw [hp, one_pow]

-- ============================================================
-- PART 4: The PMF Instance
-- ============================================================

/-- **Multinomial Distribution as Mathlib PMF**

    This is the main construction: we wrap the multinomial probability function
    into Mathlib's PMF type. The key ingredient is the normalization proof. -/
noncomputable def multinomialPMF {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ≥0∞) (n : ℕ)
    (hp : ∑ i ∈ s, p i = 1) : PMF (Composition α s n) :=
  ⟨fun k => multinomialPMFVal s p n k, by
    -- Convert the Finset.sum normalization into a HasSum statement.
    -- For Fintype α, HasSum f c ↔ ∑ a, f a = c via hasSum_fintype.
    have h := hasSum_fintype (fun k : Composition α s n => multinomialPMFVal s p n k)
    rwa [multinomialPMF_sum_eq_one s p n hp] at h⟩

-- ============================================================
-- PART 5: Properties of the PMF
-- ============================================================

/-- The PMF value at a composition k is the multinomial probability -/
theorem multinomialPMF_apply {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ≥0∞) (n : ℕ) (hp : ∑ i ∈ s, p i = 1)
    (k : Composition α s n) :
    (multinomialPMF s p n hp) k = multinomialPMFVal s p n k := by
  rfl

/-- The support of the multinomial PMF consists of compositions where
    all probabilities are nonzero for the counted outcomes -/
theorem multinomialPMF_support {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ≥0∞) (n : ℕ) (hp : ∑ i ∈ s, p i = 1)
    (k : Composition α s n) :
    (multinomialPMF s p n hp) k ≠ 0 ↔
    ∀ i ∈ s, k.counts i ≠ 0 → p i ≠ 0 := by
  -- The PMF value is `multinomial · ∏ p i ^ counts i`. The multinomial coefficient
  -- is a positive natural, hence a nonzero ENNReal, so the value is nonzero iff the
  -- product is. In ℝ≥0∞ (no zero divisors) a product is nonzero iff every factor is,
  -- and `p i ^ counts i ≠ 0` iff `counts i = 0` (giving `1`) or `p i ≠ 0`.
  rw [multinomialPMF_apply]
  unfold multinomialPMFVal
  rw [mul_ne_zero_iff, Finset.prod_ne_zero_iff]
  have hmul : (Nat.multinomial s k.counts : ℝ≥0∞) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact (Nat.multinomial_pos s k.counts).ne'
  constructor
  · rintro ⟨_, hprod⟩ i hi hcount
    exact (pow_ne_zero_iff hcount).mp (hprod i hi)
  · intro h
    refine ⟨hmul, fun i hi => ?_⟩
    rcases eq_or_ne (k.counts i) 0 with hc | hc
    · rw [hc, pow_zero]; exact one_ne_zero
    · rw [pow_ne_zero_iff hc]; exact h i hi hc

-- ============================================================
-- PART 6: Marginal Distribution (Binomial)
-- ============================================================

/-- **Marginal Distribution is Binomial**

    The marginal distribution of Xᵢ (count of outcome i) in a multinomial
    distribution is Binomial(n, pᵢ).

    Proof sketch: Sum over all compositions with kᵢ fixed.
    By the multinomial theorem applied to the remaining k-1 categories,
    the marginal probability is C(n, kᵢ) · pᵢ^kᵢ · (1-pᵢ)^(n-kᵢ). -/
theorem multinomial_marginal_binomial {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ)
    (hp_sum : ∑ i ∈ s, p i = 1) (hp_nonneg : ∀ i ∈ s, 0 ≤ p i)
    (i : α) (hi : i ∈ s) (m : ℕ) (hm : m ≤ n) :
    ∑ k ∈ s.piAntidiag n |>.filter (fun k => k i = m),
      (Nat.multinomial s k : ℝ) * ∏ j ∈ s, p j ^ k j =
    (Nat.choose n m : ℝ) * p i ^ m * (1 - p i) ^ (n - m) := by
  -- Reindex compositions of `n` with `kᵢ = m` to compositions of `n-m` on `s \ {i}`
  -- by zeroing the `i`-th coordinate; the inverse re-inserts the value `m` at `i`.
  rw [Finset.sum_nbij'
        (i := fun k => Function.update k i 0)
        (j := fun g => Function.update g i m)
        (t := (s.erase i).piAntidiag (n - m))
        (g := fun g => (n.choose m : ℝ) * p i ^ m *
          ((Nat.multinomial (s.erase i) g : ℝ) * ∏ l ∈ s.erase i, p l ^ g l))]
  · -- the reduced sum is `C(n,m)·pᵢᵐ·(1-pᵢ)ⁿ⁻ᵐ` by the multinomial theorem on `s \ {i}`
    have hfactor : ∑ g ∈ (s.erase i).piAntidiag (n - m),
          (n.choose m : ℝ) * p i ^ m *
            ((Nat.multinomial (s.erase i) g : ℝ) * ∏ l ∈ s.erase i, p l ^ g l)
        = (n.choose m : ℝ) * p i ^ m * ∑ g ∈ (s.erase i).piAntidiag (n - m),
            ((Nat.multinomial (s.erase i) g : ℝ) * ∏ l ∈ s.erase i, p l ^ g l) := by
      rw [Finset.mul_sum]
    have hrest : ∑ l ∈ s.erase i, p l = 1 - p i := by
      have h2 : p i + ∑ l ∈ s.erase i, p l = 1 := by
        rw [Finset.add_sum_erase s p hi]; exact hp_sum
      linarith
    rw [hfactor, ← Finset.sum_pow_eq_sum_piAntidiag (s.erase i) p (n - m), hrest]
  · -- forward map lands in piAntidiag (s.erase i) (n-m)
    intro k hk
    rw [Finset.mem_filter, Finset.mem_piAntidiag] at hk
    obtain ⟨⟨hksum, hksupp⟩, hkim⟩ := hk
    rw [Finset.mem_piAntidiag]
    refine ⟨?_, ?_⟩
    · have hcong : ∑ l ∈ s.erase i, (Function.update k i 0) l = ∑ l ∈ s.erase i, k l :=
        Finset.sum_congr rfl
          (fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)])
      rw [hcong]
      have he : k i + ∑ l ∈ s.erase i, k l = n := by
        rw [Finset.add_sum_erase s k hi]; exact hksum
      rw [hkim] at he; omega
    · intro l hl
      by_cases hli : l = i
      · subst hli; rw [Function.update_self] at hl; exact absurd rfl hl
      · rw [Function.update_of_ne hli] at hl
        exact Finset.mem_erase.mpr ⟨hli, hksupp l hl⟩
  · -- inverse map lands in the filtered set
    intro g hg
    rw [Finset.mem_piAntidiag] at hg
    obtain ⟨hgsum, hgsupp⟩ := hg
    rw [Finset.mem_filter, Finset.mem_piAntidiag]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have hcong : ∑ l ∈ s.erase i, (Function.update g i m) l = ∑ l ∈ s.erase i, g l :=
        Finset.sum_congr rfl
          (fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)])
      rw [← Finset.add_sum_erase s (Function.update g i m) hi, Function.update_self, hcong, hgsum]
      omega
    · intro l hl
      by_cases hli : l = i
      · subst hli; exact hi
      · rw [Function.update_of_ne hli] at hl
        exact Finset.mem_of_mem_erase (hgsupp l hl)
    · rw [Function.update_self]
  · -- left inverse
    intro k hk
    have hkim : k i = m := (Finset.mem_filter.mp hk).2
    funext l
    by_cases hli : l = i
    · subst hli; rw [Function.update_self]; exact hkim.symm
    · rw [Function.update_of_ne hli, Function.update_of_ne hli]
  · -- right inverse
    intro g hg
    rw [Finset.mem_piAntidiag] at hg
    have hgi : g i = 0 := by
      by_contra h
      exact (Finset.notMem_erase i s) (hg.2 i h)
    funext l
    by_cases hli : l = i
    · subst hli; rw [Function.update_self]; exact hgi.symm
    · rw [Function.update_of_ne hli, Function.update_of_ne hli]
  · -- summand correspondence
    intro k hk
    rw [Finset.mem_filter, Finset.mem_piAntidiag] at hk
    obtain ⟨⟨hksum, hksupp⟩, hkim⟩ := hk
    have herasesum : ∑ l ∈ s.erase i, k l = n - m := by
      have he : k i + ∑ l ∈ s.erase i, k l = n := by
        rw [Finset.add_sum_erase s k hi]; exact hksum
      rw [hkim] at he; omega
    have hmult : Nat.multinomial s k = n.choose m * Nat.multinomial (s.erase i) k := by
      conv_lhs => rw [← Finset.insert_erase hi]
      rw [Nat.multinomial_insert (Finset.notMem_erase i s) k, herasesum, hkim,
          show m + (n - m) = n from by omega]
    have hmultR : (Nat.multinomial s k : ℝ)
        = (n.choose m : ℝ) * (Nat.multinomial (s.erase i) k : ℝ) := by exact_mod_cast hmult
    have hprods : (∏ l ∈ s, p l ^ k l) = p i ^ m * ∏ l ∈ s.erase i, p l ^ k l := by
      rw [← Finset.mul_prod_erase s (fun l => p l ^ k l) hi, hkim]
    have hmcongr : Nat.multinomial (s.erase i) (Function.update k i 0)
        = Nat.multinomial (s.erase i) k :=
      Nat.multinomial_congr
        (fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)])
    have hpcongr : (∏ l ∈ s.erase i, p l ^ (Function.update k i 0) l)
        = ∏ l ∈ s.erase i, p l ^ k l :=
      Finset.prod_congr rfl
        (fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)])
    rw [hmcongr, hpcongr, hprods, hmultR]; ring

-- ============================================================
-- PART 7: Mean and Variance
-- ============================================================

/-- **Absorption identity.** For a composition `k` of `n` (i.e. `∑ k = n`) with
    `kᵢ ≥ 1`, lowering the `i`-th count by one turns the multinomial coefficient
    into the `(n-1)`-multinomial, absorbing the factor `kᵢ` into `n`:
    `kᵢ · multinomial(s,k) = n · multinomial(s, update k i (kᵢ-1))`.
    This is the combinatorial engine behind `E[Xᵢ] = n·pᵢ`. -/
private theorem multinomial_absorb {α : Type*} [DecidableEq α] (s : Finset α)
    (k : α → ℕ) (n : ℕ) (i : α) (hi : i ∈ s) (hsum : ∑ j ∈ s, k j = n) (hki : k i ≠ 0) :
    k i * Nat.multinomial s k =
    n * Nat.multinomial s (Function.update k i (k i - 1)) := by
  have hn : n ≠ 0 := by
    have hle : k i ≤ ∑ j ∈ s, k j := Finset.single_le_sum (fun j _ => Nat.zero_le _) hi
    omega
  set P := ∏ j ∈ s.erase i, (k j)! with hP
  -- factor the factorial products at `i`
  have hk_prod : (∏ j ∈ s, (k j)!) = (k i)! * P :=
    (Finset.mul_prod_erase s (fun j => (k j)!) hi).symm
  have hk'_prod : (∏ j ∈ s, ((Function.update k i (k i - 1)) j)!) = (k i - 1)! * P := by
    rw [← Finset.mul_prod_erase s (fun j => ((Function.update k i (k i - 1)) j)!) hi,
        Function.update_self]
    congr 1
    exact Finset.prod_congr rfl
      (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  -- the lowered composition sums to `n - 1`
  have hsum' : (∑ j ∈ s, (Function.update k i (k i - 1)) j) = n - 1 := by
    rw [← Finset.add_sum_erase s (Function.update k i (k i - 1)) hi, Function.update_self]
    have hcong : (∑ j ∈ s.erase i, (Function.update k i (k i - 1)) j) = ∑ j ∈ s.erase i, k j :=
      Finset.sum_congr rfl
        (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
    rw [hcong]
    have he : k i + ∑ j ∈ s.erase i, k j = n := by
      rw [Finset.add_sum_erase s k hi]; exact hsum
    omega
  have spec_k : (∏ j ∈ s, (k j)!) * Nat.multinomial s k = n ! := by
    rw [Nat.multinomial_spec s k, hsum]
  have spec_k' : (∏ j ∈ s, ((Function.update k i (k i - 1)) j)!) *
      Nat.multinomial s (Function.update k i (k i - 1)) = (n - 1)! := by
    rw [Nat.multinomial_spec s (Function.update k i (k i - 1)), hsum']
  have hpos : 0 < (k i - 1)! * P := by
    refine Nat.mul_pos (Nat.factorial_pos _) ?_
    rw [hP]; exact Finset.prod_pos (fun j _ => Nat.factorial_pos _)
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc (k i - 1)! * P * (k i * Nat.multinomial s k)
      = (k i * (k i - 1)!) * P * Nat.multinomial s k := by ring
    _ = (k i)! * P * Nat.multinomial s k := by rw [Nat.mul_factorial_pred hki]
    _ = (∏ j ∈ s, (k j)!) * Nat.multinomial s k := by rw [hk_prod]
    _ = n ! := spec_k
    _ = n * (n - 1)! := (Nat.mul_factorial_pred hn).symm
    _ = n * ((∏ j ∈ s, ((Function.update k i (k i - 1)) j)!) *
            Nat.multinomial s (Function.update k i (k i - 1))) := by rw [spec_k']
    _ = n * ((k i - 1)! * P * Nat.multinomial s (Function.update k i (k i - 1))) := by
          rw [hk'_prod]
    _ = (k i - 1)! * P * (n * Nat.multinomial s (Function.update k i (k i - 1))) := by ring

/-- The expected value of the i-th component is E[Xᵢ] = n · pᵢ.

    Proof: each composition `k` of `n` with `kᵢ ≥ 1` corresponds bijectively to a
    composition of `n-1` by lowering `kᵢ`; the absorption identity converts the
    weight `kᵢ·multinomial(s,k)·∏pⱼ^kⱼ` into `n·pᵢ·multinomial(s,k')·∏pⱼ^k'ⱼ`, and
    summing the latter over all compositions of `n-1` gives `n·pᵢ·(∑p)ⁿ⁻¹ = n·pᵢ`. -/
theorem multinomial_mean {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ)
    (hp_sum : ∑ i ∈ s, p i = 1) (hp_nonneg : ∀ i ∈ s, 0 ≤ p i)
    (i : α) (hi : i ∈ s) :
    ∑ k ∈ s.piAntidiag n,
      (k i : ℝ) * ((Nat.multinomial s k : ℝ) * ∏ j ∈ s, p j ^ k j) =
    n * p i := by
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simp
  -- total mass of the (n-1)-multinomial is 1 (multinomial theorem with ∑ p = 1)
  have hmass : ∑ k ∈ s.piAntidiag (n - 1),
      (Nat.multinomial s k : ℝ) * ∏ j ∈ s, p j ^ k j = 1 := by
    rw [← Finset.sum_pow_eq_sum_piAntidiag s p (n - 1), hp_sum, one_pow]
  -- drop the kᵢ = 0 terms (they carry a vanishing factor kᵢ)
  rw [← Finset.sum_filter_of_ne (p := fun k => k i ≠ 0)
        (fun k _ hfk hzero => hfk (by rw [hzero]; simp))]
  -- reindex onto compositions of n-1 via k ↦ update k i (kᵢ-1)
  rw [Finset.sum_nbij'
        (i := fun k => Function.update k i (k i - 1))
        (j := fun k' => Function.update k' i (k' i + 1))
        (t := s.piAntidiag (n - 1))
        (g := fun k' => (n : ℝ) * p i *
          ((Nat.multinomial s k' : ℝ) * ∏ j ∈ s, p j ^ k' j))]
  · rw [← Finset.mul_sum, hmass, mul_one]
  · -- hi : forward map lands in piAntidiag (n-1)
    intro k hk
    rw [Finset.mem_filter, Finset.mem_piAntidiag] at hk
    obtain ⟨⟨hksum, hksupp⟩, hki⟩ := hk
    rw [Finset.mem_piAntidiag]
    refine ⟨?_, ?_⟩
    · have hcong : (∑ j ∈ s.erase i, (Function.update k i (k i - 1)) j) = ∑ j ∈ s.erase i, k j :=
        Finset.sum_congr rfl
          (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
      rw [← Finset.add_sum_erase s (Function.update k i (k i - 1)) hi, Function.update_self, hcong]
      have he : k i + ∑ j ∈ s.erase i, k j = n := by
        rw [Finset.add_sum_erase s k hi]; exact hksum
      omega
    · intro j hj
      by_cases hji : j = i
      · subst hji; exact hi
      · rw [Function.update_of_ne hji] at hj; exact hksupp j hj
  · -- hj : inverse map lands in the filtered set
    intro k' hk'
    rw [Finset.mem_piAntidiag] at hk'
    obtain ⟨hk'sum, hk'supp⟩ := hk'
    rw [Finset.mem_filter, Finset.mem_piAntidiag]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have hcong : (∑ j ∈ s.erase i, (Function.update k' i (k' i + 1)) j) = ∑ j ∈ s.erase i, k' j :=
        Finset.sum_congr rfl
          (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
      rw [← Finset.add_sum_erase s (Function.update k' i (k' i + 1)) hi, Function.update_self, hcong]
      have he : k' i + ∑ j ∈ s.erase i, k' j = n - 1 := by
        rw [Finset.add_sum_erase s k' hi]; exact hk'sum
      omega
    · intro j hj
      by_cases hji : j = i
      · subst hji; exact hi
      · rw [Function.update_of_ne hji] at hj; exact hk'supp j hj
    · rw [Function.update_self]; exact Nat.succ_ne_zero _
  · -- left inverse
    intro k hk
    have hki : k i ≠ 0 := (Finset.mem_filter.mp hk).2
    funext j
    by_cases hji : j = i
    · subst hji; rw [Function.update_self, Function.update_self]; omega
    · rw [Function.update_of_ne hji, Function.update_of_ne hji]
  · -- right inverse
    intro k' hk'
    funext j
    by_cases hji : j = i
    · subst hji; rw [Function.update_self, Function.update_self]; omega
    · rw [Function.update_of_ne hji, Function.update_of_ne hji]
  · -- summand correspondence
    intro k hk
    rw [Finset.mem_filter, Finset.mem_piAntidiag] at hk
    obtain ⟨⟨hksum, _⟩, hki⟩ := hk
    have habs : (k i : ℝ) * (Nat.multinomial s k : ℝ)
        = (n : ℝ) * (Nat.multinomial s (Function.update k i (k i - 1)) : ℝ) := by
      exact_mod_cast multinomial_absorb s k n i hi hksum hki
    have hprod : (∏ j ∈ s, p j ^ k j)
        = p i * ∏ j ∈ s, p j ^ (Function.update k i (k i - 1)) j := by
      have hL : (∏ j ∈ s, p j ^ k j) = p i ^ k i * ∏ j ∈ s.erase i, p j ^ k j :=
        (Finset.mul_prod_erase s (fun j => p j ^ k j) hi).symm
      have hR : (∏ j ∈ s, p j ^ (Function.update k i (k i - 1)) j)
          = p i ^ (k i - 1) * ∏ j ∈ s.erase i, p j ^ k j := by
        rw [← Finset.mul_prod_erase s (fun j => p j ^ (Function.update k i (k i - 1)) j) hi]
        congr 1
        · rw [Function.update_self]
        · exact Finset.prod_congr rfl
            (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
      rw [hL, hR, ← mul_assoc]
      congr 1
      rw [← pow_succ']
      congr 1
      omega
    calc (k i : ℝ) * ((Nat.multinomial s k : ℝ) * ∏ j ∈ s, p j ^ k j)
        = ((k i : ℝ) * (Nat.multinomial s k : ℝ)) * (∏ j ∈ s, p j ^ k j) := by ring
      _ = ((n : ℝ) * (Nat.multinomial s (Function.update k i (k i - 1)) : ℝ))
            * (p i * ∏ j ∈ s, p j ^ (Function.update k i (k i - 1)) j) := by rw [habs, hprod]
      _ = (n : ℝ) * p i *
            ((Nat.multinomial s (Function.update k i (k i - 1)) : ℝ)
              * ∏ j ∈ s, p j ^ (Function.update k i (k i - 1)) j) := by ring

/-- **Weighted absorption.** The real-valued form of `multinomial_absorb`, carrying
    the probability weight: lowering the `i`-th count by one converts the weighted
    summand `kᵢ · multinomial(s,k) · ∏pⱼ^kⱼ` into `n·pᵢ · multinomial(s,k') · ∏pⱼ^k'ⱼ`. -/
private theorem multinomial_absorb_weighted {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (k : α → ℕ) (n : ℕ) (i : α)
    (hi : i ∈ s) (hsum : ∑ l ∈ s, k l = n) (hki : k i ≠ 0) :
    (k i : ℝ) * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)
    = (n : ℝ) * p i * ((Nat.multinomial s (Function.update k i (k i - 1)) : ℝ)
        * ∏ l ∈ s, p l ^ (Function.update k i (k i - 1)) l) := by
  have habs : (k i : ℝ) * (Nat.multinomial s k : ℝ)
      = (n : ℝ) * (Nat.multinomial s (Function.update k i (k i - 1)) : ℝ) := by
    exact_mod_cast multinomial_absorb s k n i hi hsum hki
  have hprod : (∏ l ∈ s, p l ^ k l)
      = p i * ∏ l ∈ s, p l ^ (Function.update k i (k i - 1)) l := by
    have hL : (∏ l ∈ s, p l ^ k l) = p i ^ k i * ∏ l ∈ s.erase i, p l ^ k l :=
      (Finset.mul_prod_erase s (fun l => p l ^ k l) hi).symm
    have hR : (∏ l ∈ s, p l ^ (Function.update k i (k i - 1)) l)
        = p i ^ (k i - 1) * ∏ l ∈ s.erase i, p l ^ k l := by
      rw [← Finset.mul_prod_erase s (fun l => p l ^ (Function.update k i (k i - 1)) l) hi]
      congr 1
      · rw [Function.update_self]
      · exact Finset.prod_congr rfl
          (fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)])
    rw [hL, hR, ← mul_assoc]
    congr 1
    rw [← pow_succ']
    congr 1
    omega
  calc (k i : ℝ) * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)
      = ((k i : ℝ) * (Nat.multinomial s k : ℝ)) * (∏ l ∈ s, p l ^ k l) := by ring
    _ = ((n : ℝ) * (Nat.multinomial s (Function.update k i (k i - 1)) : ℝ))
          * (p i * ∏ l ∈ s, p l ^ (Function.update k i (k i - 1)) l) := by rw [habs, hprod]
    _ = (n : ℝ) * p i * ((Nat.multinomial s (Function.update k i (k i - 1)) : ℝ)
          * ∏ l ∈ s, p l ^ (Function.update k i (k i - 1)) l) := by ring

/-- **Cross moment** `E[Xᵢ·Xⱼ] = n·(n-1)·pᵢ·pⱼ` for `i ≠ j`.

    Proof: lower `Xᵢ` by the absorption bijection (the surviving `kⱼ` factor rides
    along unchanged since `j ≠ i`), reducing the sum to `n·pᵢ` times the *mean of
    `Xⱼ` in an `(n-1)`-trial multinomial*, which is `(n-1)·pⱼ` by `multinomial_mean`. -/
private theorem multinomial_cross_moment {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ)
    (hp_sum : ∑ i ∈ s, p i = 1) (hp_nonneg : ∀ i ∈ s, 0 ≤ p i)
    (i j : α) (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    ∑ k ∈ s.piAntidiag n,
      (k i : ℝ) * (k j : ℝ) * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)
    = (n : ℝ) * ((n - 1 : ℕ) : ℝ) * p i * p j := by
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simp
  rw [← Finset.sum_filter_of_ne (p := fun k => k i ≠ 0)
        (fun k _ hfk hzero => hfk (by rw [hzero]; simp))]
  rw [Finset.sum_nbij'
        (i := fun k => Function.update k i (k i - 1))
        (j := fun k' => Function.update k' i (k' i + 1))
        (t := s.piAntidiag (n - 1))
        (g := fun k' => (n : ℝ) * p i * (k' j : ℝ) *
          ((Nat.multinomial s k' : ℝ) * ∏ l ∈ s, p l ^ k' l))]
  · -- ∑ g = n·pᵢ · (mean of Xⱼ over n-1 trials) = n·pᵢ·(n-1)·pⱼ
    have hfac : ∑ k' ∈ s.piAntidiag (n - 1),
          (n : ℝ) * p i * (k' j : ℝ) * ((Nat.multinomial s k' : ℝ) * ∏ l ∈ s, p l ^ k' l)
        = (n : ℝ) * p i * ∑ k' ∈ s.piAntidiag (n - 1),
            (k' j : ℝ) * ((Nat.multinomial s k' : ℝ) * ∏ l ∈ s, p l ^ k' l) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k' _ => by ring)
    rw [hfac, multinomial_mean s p (n - 1) hp_sum hp_nonneg j hj]; ring
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_piAntidiag] at hk
    obtain ⟨⟨hksum, hksupp⟩, hki⟩ := hk
    rw [Finset.mem_piAntidiag]
    refine ⟨?_, ?_⟩
    · have hcong : (∑ l ∈ s.erase i, (Function.update k i (k i - 1)) l) = ∑ l ∈ s.erase i, k l :=
        Finset.sum_congr rfl
          (fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)])
      rw [← Finset.add_sum_erase s (Function.update k i (k i - 1)) hi, Function.update_self, hcong]
      have he : k i + ∑ l ∈ s.erase i, k l = n := by
        rw [Finset.add_sum_erase s k hi]; exact hksum
      omega
    · intro l hl
      by_cases hli : l = i
      · subst hli; exact hi
      · rw [Function.update_of_ne hli] at hl; exact hksupp l hl
  · intro k' hk'
    rw [Finset.mem_piAntidiag] at hk'
    obtain ⟨hk'sum, hk'supp⟩ := hk'
    rw [Finset.mem_filter, Finset.mem_piAntidiag]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have hcong : (∑ l ∈ s.erase i, (Function.update k' i (k' i + 1)) l) = ∑ l ∈ s.erase i, k' l :=
        Finset.sum_congr rfl
          (fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)])
      rw [← Finset.add_sum_erase s (Function.update k' i (k' i + 1)) hi, Function.update_self, hcong]
      have he : k' i + ∑ l ∈ s.erase i, k' l = n - 1 := by
        rw [Finset.add_sum_erase s k' hi]; exact hk'sum
      omega
    · intro l hl
      by_cases hli : l = i
      · subst hli; exact hi
      · rw [Function.update_of_ne hli] at hl; exact hk'supp l hl
    · rw [Function.update_self]; exact Nat.succ_ne_zero _
  · intro k hk
    have hki : k i ≠ 0 := (Finset.mem_filter.mp hk).2
    funext l
    by_cases hli : l = i
    · subst hli; rw [Function.update_self, Function.update_self]; omega
    · rw [Function.update_of_ne hli, Function.update_of_ne hli]
  · intro k' hk'
    funext l
    by_cases hli : l = i
    · subst hli; rw [Function.update_self, Function.update_self]; omega
    · rw [Function.update_of_ne hli, Function.update_of_ne hli]
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_piAntidiag] at hk
    obtain ⟨⟨hksum, _⟩, hki⟩ := hk
    have hweighted := multinomial_absorb_weighted s p k n i hi hksum hki
    have hkj' : (Function.update k i (k i - 1)) j = k j :=
      Function.update_of_ne (Ne.symm hij) _ _
    calc (k i : ℝ) * (k j : ℝ) * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)
        = (k j : ℝ) * ((k i : ℝ) * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)) := by ring
      _ = (k j : ℝ) * ((n : ℝ) * p i *
            ((Nat.multinomial s (Function.update k i (k i - 1)) : ℝ)
              * ∏ l ∈ s, p l ^ (Function.update k i (k i - 1)) l)) := by rw [hweighted]
      _ = (n : ℝ) * p i * ((Function.update k i (k i - 1)) j : ℝ) *
            ((Nat.multinomial s (Function.update k i (k i - 1)) : ℝ)
              * ∏ l ∈ s, p l ^ (Function.update k i (k i - 1)) l) := by rw [← hkj']; ring

/-- The covariance of components: Cov(Xᵢ, Xⱼ) = -n · pᵢ · pⱼ for i ≠ j.
    This negative correlation is a fundamental property of the multinomial:
    more of one outcome means less of another.

    Proof: expand `Cov = E[XᵢXⱼ] − E[Xᵢ]E[Xⱼ]`. The cross moment is `n(n-1)pᵢpⱼ`
    (`multinomial_cross_moment`) and the total mass is `1` (multinomial theorem),
    so the sum equals `n(n-1)pᵢpⱼ − n²pᵢpⱼ = −n·pᵢ·pⱼ`. -/
theorem multinomial_covariance {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ)
    (hp_sum : ∑ i ∈ s, p i = 1) (hp_nonneg : ∀ i ∈ s, 0 ≤ p i)
    (i j : α) (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    ∑ k ∈ s.piAntidiag n,
      ((k i : ℝ) * (k j : ℝ) - n * p i * (n * p j)) *
      ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l) =
    -(n : ℝ) * p i * p j := by
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simp
  have hmass : ∑ k ∈ s.piAntidiag n, (Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l = 1 := by
    rw [← Finset.sum_pow_eq_sum_piAntidiag s p n, hp_sum, one_pow]
  have hcross := multinomial_cross_moment s p n hp_sum hp_nonneg i j hi hj hij
  have hdist : ∀ k : α → ℕ,
      ((k i : ℝ) * (k j : ℝ) - n * p i * (n * p j)) *
        ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)
      = (k i : ℝ) * (k j : ℝ) * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)
        - (n * p i * (n * p j)) * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l) :=
    fun k => by ring
  rw [Finset.sum_congr rfl (fun k _ => hdist k), Finset.sum_sub_distrib, hcross,
      ← Finset.mul_sum, hmass, mul_one]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  push_cast
  ring

-- ============================================================
-- PART 8: Feasibility Analysis
-- ============================================================

/-
## Can the Multinomial PMF Be Integrated into Mathlib?

**YES, with the following steps:**

### What's Available in Mathlib:
1. ✅ `PMF` type with `tsum` normalization
2. ✅ `Nat.multinomial` coefficients
3. ✅ `Finset.sum_pow_eq_sum_piAntidiag` (multinomial theorem)
4. ✅ `ENNReal` arithmetic
5. ✅ `PMF.bind`, `PMF.map` for constructing derived distributions

### What Needs to Be Built:
1. **Composition type**: The set of compositions of n into k parts as a `Fintype`
   (~50 lines, using `piAntidiag` as the underlying finset)
2. **ENNReal multinomial theorem**: Lifting the ℝ theorem to ℝ≥0∞
   (~30 lines, careful with infinite values)
3. **PMF construction**: Wrapping multinomialPMFVal with normalization proof
   (~20 lines, using the ENNReal multinomial theorem)
4. **Marginal extraction**: Proving the marginal is binomial
   (~100 lines, main technical content)

### Estimated Effort: ~200-300 lines for a complete Mathlib contribution

### Conclusion
The integration IS feasible. The main obstacle is the composition type
(Fintype instance) and lifting the multinomial theorem to ENNReal.
The PMF construction itself is straightforward once these are in place.
-/

-- ============================================================
-- PART 9: Concrete Example — Dice Roll
-- ============================================================

/-- Example: Rolling a fair die n times.
    The multinomial distribution with k = 6 outcomes each with probability 1/6.
    P(seeing each face exactly once in 6 rolls) = 6!/(1!·...·1!) · (1/6)^6 = 720/46656 -/
theorem dice_six_rolls_all_different :
    Nat.multinomial {0, 1, 2, 3, 4, 5} (fun _ => 1) *
    (1 : ℕ) = Nat.factorial 6 := by
  decide

-- ============================================================
-- PART 10: Summary
-- ============================================================

/-
## Summary of Results (0 axioms, 0 sorries — fully verified)

### Construction
1. `Composition` type + `Fintype` instance (support of the multinomial)
2. `multinomialPMF_sum_eq_one`: normalization in ℝ≥0∞ via the multinomial theorem
3. `multinomialPMF`: the multinomial distribution as a Mathlib `PMF`
4. `multinomialPMF_apply`, `multinomialPMF_support`: basic PMF properties

### Distributional properties (the combinatorial core)
5. `multinomial_absorb`: the absorption identity kᵢ·M(s,k) = n·M(s,k⁻ⁱ)
6. `multinomial_marginal_binomial`: the marginal of Xᵢ is Binomial(n, pᵢ)
7. `multinomial_mean`: E[Xᵢ] = n·pᵢ
8. `multinomial_covariance`: Cov(Xᵢ,Xⱼ) = -n·pᵢ·pⱼ (negative correlation)
9. `dice_six_rolls_all_different`: concrete example (kernel `decide`, no `ofReduceBool`)

### Key Contribution
Demonstrates that the multinomial distribution can be integrated into Mathlib's
PMF framework, and proves its principal distributional properties (marginals,
mean, covariance) from a single combinatorial engine — the absorption identity
`kᵢ·multinomial(s,k) = n·multinomial(s, k with kᵢ−1)` — together with the
`piAntidiag`-based multinomial theorem. The mean, cross moment and covariance all
reduce, via one reindexing bijection, to the multinomial theorem on `n−1` (resp.
`n−m`) trials. Axiom-free (`decide`, not `native_decide`).
-/

#check @multinomialPMF
#check @multinomial_marginal_binomial
#check @multinomial_mean
#check @multinomial_covariance

-- Axiom audit: should list only propext / Classical.choice / Quot.sound
#print axioms multinomial_marginal_binomial
#print axioms multinomial_mean
#print axioms multinomial_covariance
#print axioms dice_six_rolls_all_different

end BinomialTheoremOQ02OQ01OQ01
