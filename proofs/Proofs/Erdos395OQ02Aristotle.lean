/-
  Aristotle targets for Erdős Problem #395 — Open Question oq-02
  Dimension-one reverse Littlewood–Offord (the lower boundary case).

  See Erdos395OQ02.lean for the main formalization (the orthogonality
  obstruction and the sharp dichotomy, both verified, 0 axioms).

  ## Why these targets

  The main file records the fixed-dimension question

      ReverseLO_fixedDim d :  ∃ C c > 0, ∀ m > 0, ∀ unit z : Fin m → ℝ^d,
                                P(‖Σ εᵢ zᵢ‖ ≤ C) ≥ c/m

  as an *unproven* Prop.  Its two boundary dimensions are in fact settled:
  `d = 2` is the parent theorem (HJNS 2024, unit complex vectors), and `d = 1`
  is the classical one-dimensional reverse Littlewood–Offord, which is
  elementary.  These targets formalize the `d = 1` case so that, once proved,
  the genuinely open question is pinned to `d ≥ 3`.

  ## The d = 1 argument

  In `EuclideanSpace ℝ (Fin 1)` a unit vector has its single coordinate equal to
  `±1`, so `‖Σ εᵢ zᵢ‖ = |Σ εᵢ (zᵢ)₀|` is the absolute value of an ordinary `±1`
  walk of length `m`.  The favourable event `|Σ ±1| ≤ 1` is realized by at least
  the central-binomial number `C(m, ⌊m/2⌋)` of the `2ᵐ` sign patterns:
  the map sending a `⌊m/2⌋`-subset `S ⊆ Fin m` to the pattern whose `i`-th signed
  term is `+1` for `i ∈ S` and `-1` otherwise is injective and lands in the
  favourable set (its signed sum is `2⌊m/2⌋ - m ∈ {0,-1}`, of absolute value
  `≤ 1`).  Since `C(m, ⌊m/2⌋)` is the largest of the `m+1` binomial coefficients
  summing to `2ᵐ`, we get `C(m, ⌊m/2⌋) ≥ 2ᵐ/(m+1)`, hence

      P(‖Σ εᵢ zᵢ‖ ≤ 1) ≥ C(m, ⌊m/2⌋)/2ᵐ ≥ 1/(m+1) ≥ (1/2)/m,

  so `ReverseLO_fixedDim 1` holds with threshold `C = 1` and constant `c = 1/2`.

  Criteria for inclusion (per research/SORRY-CLASSIFICATION.md):
  - NOT the main open conjecture (that is `ReverseLO_fixedDim d` for `d ≥ 3`).
  - Known / classical results, each a clean theorem with no definition sorries.
  - No axioms.
-/
import Mathlib

namespace Erdos395OQ02Aristotle

/-- Boolean encoding of a sign (`true ↦ +1`, `false ↦ -1`). -/
def toSign (b : Bool) : ℝ := if b then 1 else -1

/-- The signed sum `Σ εᵢ zᵢ` for a Boolean sign pattern, in dimension one. -/
noncomputable def signedSum {m : ℕ} (z : Fin m → EuclideanSpace ℝ (Fin 1))
    (s : Fin m → Bool) : EuclideanSpace ℝ (Fin 1) :=
  ∑ i, toSign (s i) • z i

/-- Number of sign patterns whose signed sum has norm `≤ C`. -/
noncomputable def smallSumCount {m : ℕ} (z : Fin m → EuclideanSpace ℝ (Fin 1))
    (C : ℝ) : ℕ :=
  (Finset.univ.filter (fun s : Fin m → Bool => ‖signedSum z s‖ ≤ C)).card

/-- **Target 1 (routine).** Central-binomial bound: the middle coefficient is the
largest of the `m+1` terms summing to `2ᵐ`, so `2ᵐ ≤ (m+1)·C(m, ⌊m/2⌋)`.
Provable from `Nat.sum_range_choose` and `Nat.choose_le_middle`. -/
theorem two_pow_le_succ_mul_choose_half (m : ℕ) :
    2 ^ m ≤ (m + 1) * Nat.choose m (m / 2) := by
  calc 2 ^ m = ∑ i ∈ Finset.range (m + 1), Nat.choose m i := (Nat.sum_range_choose m).symm
    _ ≤ ∑ _i ∈ Finset.range (m + 1), Nat.choose m (m / 2) :=
        Finset.sum_le_sum (fun i _ => Nat.choose_le_middle i m)
    _ = (m + 1) * Nat.choose m (m / 2) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **Target 2 (routine).** In dimension one, a unit vector's single coordinate
is `±1`.  Provable from `EuclideanSpace.norm_eq` / `Real.sqrt_sq_eq_abs` and
`abs_eq`. -/
theorem coord_eq_one_or {m : ℕ} (z : Fin m → EuclideanSpace ℝ (Fin 1)) (i : Fin m)
    (h : ‖z i‖ = 1) : z i 0 = 1 ∨ z i 0 = -1 := by
  have hnorm : ‖z i‖ = |z i 0| := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, Real.sqrt_sq_eq_abs,
      abs_abs]
  rw [hnorm] at h
  rwa [abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at h

/-- **Target 3 (routine).** In dimension one, the norm of a signed sum is the
absolute value of the ordinary scalar signed sum of the coordinates.  Provable
from `EuclideanSpace.norm_eq`, `Fin.sum_univ_one`, and `Finset.sum_apply`. -/
theorem norm_signedSum_dim_one {m : ℕ} (z : Fin m → EuclideanSpace ℝ (Fin 1))
    (s : Fin m → Bool) :
    ‖signedSum z s‖ = |∑ i, toSign (s i) * z i 0| := by
  have happ : signedSum z s 0 = ∑ i, toSign (s i) * z i 0 := by
    simp only [signedSum, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
      Pi.smul_apply, smul_eq_mul]
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, happ, Real.norm_eq_abs, Real.sqrt_sq_eq_abs,
    abs_abs]

/-- **Target 4 (the combinatorial core).** At least `C(m, ⌊m/2⌋)` of the `2ᵐ`
sign patterns give a signed sum of norm `≤ 1`.  Proof: the injection sending a
`⌊m/2⌋`-subset `S` to the pattern making the `i`-th signed term `+1` on `S` and
`-1` off `S` lands in the favourable set (signed sum `2⌊m/2⌋ - m ∈ {0,-1}`), so
`Finset.card_le_card_of_injOn` with `Finset.card_powersetCard` gives the bound. -/
theorem choose_le_smallSumCount_dim_one {m : ℕ}
    (z : Fin m → EuclideanSpace ℝ (Fin 1)) (hz : ∀ i, ‖z i‖ = 1) :
    Nat.choose m (m / 2) ≤ smallSumCount z 1 := by
  classical
  -- Per-coordinate sign bit: `toSign (sgn i) = z i 0` (a unit vector's single
  -- coordinate is `±1`, so such a Boolean exists).  Routing the sign through this
  -- honest `Bool` avoids `decide` on (non-computable) real equality.
  have hsign : ∀ i, ∃ b : Bool, toSign b = z i 0 := by
    intro i
    rcases coord_eq_one_or z i (hz i) with h1 | h1
    · exact ⟨true, by simp [toSign, h1]⟩
    · exact ⟨false, by simp [toSign, h1]⟩
  choose sgn hsgn using hsign
  -- The injection sending a `⌊m/2⌋`-subset `S` to the sign pattern that matches
  -- `sgn` exactly on `S`, so the `i`-th signed term is `+1` on `S` and `-1` off it.
  let φ : Finset (Fin m) → (Fin m → Bool) := fun S i => decide (i ∈ S) == sgn i
  -- For each `S` and `i`, the signed term equals `+1` on `S`, `-1` off `S`.
  have hterm : ∀ (S : Finset (Fin m)) (i : Fin m),
      toSign (φ S i) * z i 0 = if i ∈ S then (1 : ℝ) else -1 := by
    intro S i
    rw [← hsgn i]
    by_cases hmem : i ∈ S <;> cases hb : sgn i <;>
      norm_num [φ, toSign, hmem, hb]
  have hcard : (Finset.powersetCard (m / 2) (Finset.univ : Finset (Fin m))).card
      = m.choose (m / 2) := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [smallSumCount, ← hcard]
  refine Finset.card_le_card_of_injOn φ ?_ ?_
  · -- `φ S` lands in the favourable set.
    intro S hS
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hS
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [norm_signedSum_dim_one]
    have hsum : (∑ i, toSign (φ S i) * z i 0) = 2 * (S.card : ℝ) - m := by
      rw [Finset.sum_congr rfl (fun i _ => hterm S i)]
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
        mul_one, mul_neg_one]
      have hf : (Finset.univ.filter (fun i => i ∈ S)) = S := by
        ext i; simp
      have hg : (Finset.univ.filter (fun i => i ∉ S)).card = m - S.card := by
        rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), hf,
          Finset.card_univ, Fintype.card_fin]
      rw [hf, hg]
      have hSle : S.card ≤ m := by
        calc S.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card hS.1
          _ = m := by simp
      push_cast [Nat.cast_sub hSle]
      ring
    rw [hsum, hS.2]
    -- `|2 * (m/2) - m| ≤ 1`
    have hbound : 2 * ((m / 2 : ℕ) : ℝ) - (m : ℝ) ≤ 1 ∧
        -(1 : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) - (m : ℝ) := by
      have h1 : 2 * (m / 2) ≤ m := by omega
      have h2 : m ≤ 2 * (m / 2) + 1 := by omega
      have ha : ((2 * (m / 2) : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
      have hb : ((m : ℕ) : ℝ) ≤ ((2 * (m / 2) + 1 : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at ha hb
      constructor <;> linarith
    rw [abs_le]
    exact ⟨hbound.2, hbound.1⟩
  · -- `φ` is injective on `(m/2)`-subsets.
    intro S₁ _ S₂ _ heq
    ext i
    have hi : (decide (i ∈ S₁) == sgn i) = (decide (i ∈ S₂) == sgn i) := congrFun heq i
    have cancel : ∀ a b c : Bool, (a == c) = (b == c) → a = b := by decide
    have hd : decide (i ∈ S₁) = decide (i ∈ S₂) := cancel _ _ _ hi
    rwa [decide_eq_decide] at hd

/-- **Target 5 (assembly).** The fixed-dimension reverse Littlewood–Offord
question is TRUE for `d = 1`: with threshold `C = 1` and constant `c = 1/2`,
every one-dimensional unit configuration satisfies `P(‖Σ εᵢ zᵢ‖ ≤ 1) ≥ (1/2)/m`.
Assembled from Targets 1 and 4 by real arithmetic. -/
theorem reverseLO_dim_one :
    ∃ C c : ℝ, 0 < c ∧
      ∀ m : ℕ, 0 < m → ∀ z : Fin m → EuclideanSpace ℝ (Fin 1),
        (∀ i, ‖z i‖ = 1) → c / (m : ℝ) ≤ (smallSumCount z C : ℝ) / (2 : ℝ) ^ m := by
  refine ⟨1, 1 / 2, by norm_num, ?_⟩
  intro m hm z hz
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  -- `C(m,⌊m/2⌋) ≤ smallSumCount z 1` and `2^m ≤ (m+1)·C(m,⌊m/2⌋)`.
  have hsc : ((m.choose (m / 2) : ℕ) : ℝ) ≤ (smallSumCount z 1 : ℝ) := by
    exact_mod_cast choose_le_smallSumCount_dim_one z hz
  have h1r : (2 : ℝ) ^ m ≤ ((m : ℝ) + 1) * (m.choose (m / 2) : ℝ) := by
    have := two_pow_le_succ_mul_choose_half m
    have : ((2 ^ m : ℕ) : ℝ) ≤ (((m + 1) * Nat.choose m (m / 2) : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at this; linarith
  rw [le_div_iff₀ h2pos, div_mul_eq_mul_div, div_le_iff₀ hmr]
  -- Reduce to `(1/2) * 2^m ≤ smallSumCount * m`.
  have hchoose_nonneg : (0 : ℝ) ≤ (m.choose (m / 2) : ℝ) := by positivity
  nlinarith [hsc, h1r, hmr, hm1, mul_le_mul_of_nonneg_right hsc hmr.le,
    mul_nonneg hchoose_nonneg hmr.le, hchoose_nonneg,
    mul_nonneg hchoose_nonneg (by linarith : (0:ℝ) ≤ (m:ℝ) - 1)]

end Erdos395OQ02Aristotle
