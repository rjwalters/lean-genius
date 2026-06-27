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
def signedSum {m : ℕ} (z : Fin m → EuclideanSpace ℝ (Fin 1)) (s : Fin m → Bool) :
    EuclideanSpace ℝ (Fin 1) :=
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
  sorry

/-- **Target 2 (routine).** In dimension one, a unit vector's single coordinate
is `±1`.  Provable from `EuclideanSpace.norm_eq` / `Real.sqrt_sq_eq_abs` and
`abs_eq`. -/
theorem coord_eq_one_or {m : ℕ} (z : Fin m → EuclideanSpace ℝ (Fin 1)) (i : Fin m)
    (h : ‖z i‖ = 1) : z i 0 = 1 ∨ z i 0 = -1 := by
  sorry

/-- **Target 3 (routine).** In dimension one, the norm of a signed sum is the
absolute value of the ordinary scalar signed sum of the coordinates.  Provable
from `EuclideanSpace.norm_eq`, `Fin.sum_univ_one`, and `Finset.sum_apply`. -/
theorem norm_signedSum_dim_one {m : ℕ} (z : Fin m → EuclideanSpace ℝ (Fin 1))
    (s : Fin m → Bool) :
    ‖signedSum z s‖ = |∑ i, toSign (s i) * z i 0| := by
  sorry

/-- **Target 4 (the combinatorial core).** At least `C(m, ⌊m/2⌋)` of the `2ᵐ`
sign patterns give a signed sum of norm `≤ 1`.  Proof: the injection sending a
`⌊m/2⌋`-subset `S` to the pattern making the `i`-th signed term `+1` on `S` and
`-1` off `S` lands in the favourable set (signed sum `2⌊m/2⌋ - m ∈ {0,-1}`), so
`Finset.card_le_card_of_injOn` with `Finset.card_powersetCard` gives the bound. -/
theorem choose_le_smallSumCount_dim_one {m : ℕ}
    (z : Fin m → EuclideanSpace ℝ (Fin 1)) (hz : ∀ i, ‖z i‖ = 1) :
    Nat.choose m (m / 2) ≤ smallSumCount z 1 := by
  sorry

/-- **Target 5 (assembly).** The fixed-dimension reverse Littlewood–Offord
question is TRUE for `d = 1`: with threshold `C = 1` and constant `c = 1/2`,
every one-dimensional unit configuration satisfies `P(‖Σ εᵢ zᵢ‖ ≤ 1) ≥ (1/2)/m`.
Assembled from Targets 1 and 4 by real arithmetic. -/
theorem reverseLO_dim_one :
    ∃ C c : ℝ, 0 < c ∧
      ∀ m : ℕ, 0 < m → ∀ z : Fin m → EuclideanSpace ℝ (Fin 1),
        (∀ i, ‖z i‖ = 1) → c / (m : ℝ) ≤ (smallSumCount z C : ℝ) / (2 : ℝ) ^ m := by
  sorry

end Erdos395OQ02Aristotle
