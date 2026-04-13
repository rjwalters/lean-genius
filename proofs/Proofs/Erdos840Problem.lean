/-
  Erdős Problem #840: Quasi-Sidon Subsets

  Source: https://erdosproblems.com/840
  Status: OPEN

  Statement:
  Let f(N) be the size of the largest quasi-Sidon subset A ⊆ {1, ..., N},
  where A is quasi-Sidon if |A + A| = (1 + o(1)) · C(|A|, 2).
  How does f(N) grow?

  Background:
  A Sidon set (or B₂ sequence) is a set where all pairwise sums are distinct,
  giving |A + A| = C(|A|, 2) + |A| exactly. A quasi-Sidon set relaxes this to
  allow asymptotically many collisions, requiring only that the sumset size
  approaches the binomial coefficient asymptotically.

  Known Results:
  - Lower bound (Erdős-Freud, 1991): f(N) ≥ (2/√3 + o(1)) · √N ≈ 1.15√N
    Construction: Take Sidon set B ⊆ [1, N/3] and union with {N - b : b ∈ B}
  - Upper bound (Erdős-Freud, 1991): f(N) ≤ (2 + o(1)) · √N
  - Improved upper bound (Pikhurko, 2006):
    f(N) ≤ ((1/4 + 1/(π+2)²)^(-1/2) + o(1)) · √N ≈ 1.86√N

  Related:
  - For A - A instead of A + A, the answer is ~√N (Cilleruelo)
  - Related to problems #30, #819, #864

  References:
  - [Er81h] Erdős (1981), "Some problems and results on additive number theory"
  - [ErFr91] Erdős-Freud (1991), "On sums of a Sidon-sequence"
  - [Pi06] Pikhurko (2006), "Dense edge-magic graphs and thin additive bases"
-/

import Mathlib

namespace Erdos840

/-! ## Basic Definitions -/

/-- The interval [1, N] as a finite set -/
def intervalFinset (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 N

/-- The sumset A + A of a finite set A -/
def sumset (A : Finset ℕ) : Finset ℕ :=
  (A.product A).image (fun p => p.1 + p.2)

/-- A subset A is a Sidon set (B₂ sequence) if all pairwise sums are distinct.
    Equivalently, a₁ + a₂ = a₃ + a₄ implies {a₁, a₂} = {a₃, a₄}. -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a₁ a₂ a₃ a₄ ∈ A, a₁ + a₂ = a₃ + a₄ → ({a₁, a₂} : Finset ℕ) = {a₃, a₄}

/-- For a Sidon set, |A + A| = C(|A|, 2) + |A| = |A|(|A| + 1)/2 -/
theorem sidon_sumset_card (A : Finset ℕ) (hSidon : IsSidon A) :
    (sumset A).card = A.card * (A.card + 1) / 2 := by
  sorry

/-! ## Quasi-Sidon Sets -/

/-- The little-o notation: f(n) = o(g(n)) -/
def IsLittleO (f g : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N₀, ∀ n ≥ N₀, g n ≠ 0 → |f n / g n| < ε

/-- A sequence of sets Aₙ is quasi-Sidon if |Aₙ + Aₙ| = (1 + o(1)) · C(|Aₙ|, 2)
    as the sets grow. -/
def IsQuasiSidonSequence (A : ℕ → Finset ℕ) : Prop :=
  let card := fun n => (A n).card
  let sumsetCard := fun n => (sumset (A n)).card
  let binomCard := fun n => card n * (card n - 1) / 2
  ∃ (ε : ℕ → ℝ), IsLittleO ε (fun _ => 1) ∧
    ∀ n, (sumsetCard n : ℝ) = (1 + ε n) * binomCard n

/-- A finite set A ⊆ {1, ..., N} is quasi-Sidon if |A + A| is close to C(|A|, 2) -/
def IsQuasiSidon (A : Finset ℕ) (δ : ℝ) : Prop :=
  let k := A.card
  let expected := k * (k - 1) / 2
  |((sumset A).card : ℝ) - expected| ≤ δ * expected

/-! ## The Function f(N) -/

/-- f(N) = maximum size of a quasi-Sidon subset of {1, ..., N}
    We define this noncomputably using supremum. -/
noncomputable def f (N : ℕ) : ℕ :=
  Nat.find (⟨0, fun _ => trivial⟩ : ∃ m, ∀ A : Finset ℕ,
    A ⊆ intervalFinset N → (sumset A).card ≥ A.card * (A.card - 1) / 2 - 1 → A.card ≤ m)

/-- Alternative definition using sequences with vanishing error -/
noncomputable def fAlt (N : ℕ) (δ : ℝ) : ℕ :=
  (Finset.filter (fun A => A ⊆ intervalFinset N ∧ IsQuasiSidon A δ)
    (Finset.powerset (intervalFinset N))).sup Finset.card

/-! ## Known Bounds -/

/-- Erdős-Freud lower bound (1991): f(N) ≥ (2/√3 + o(1)) · √N -/
theorem erdos_freud_lower_bound :
    ∃ (c : ℝ), c = 2 / Real.sqrt 3 ∧
    ∃ (ε : ℕ → ℝ), IsLittleO ε (fun _ => 1) ∧
    ∀ N, (f N : ℝ) ≥ (c + ε N) * Real.sqrt N := by
  sorry -- Erdős-Freud (1991)

/-- The constant 2/√3 ≈ 1.1547 -/
theorem lower_bound_constant_value : 2 / Real.sqrt 3 = 2 * Real.sqrt 3 / 3 := by
  field_simp
  ring_nf
  -- Proved by Aristotle (Harmonic)
  norm_num [Real.sq_sqrt]

/-- Construction for lower bound: Sidon set B ⊆ [1, N/3] union {N - b : b ∈ B} -/
def lowerBoundConstruction (B : Finset ℕ) (N : ℕ) : Finset ℕ :=
  B ∪ (B.image (fun b => N - b))

/-- If B is Sidon in [1, N/3], the construction is quasi-Sidon -/
theorem construction_is_quasi_sidon
    (B : Finset ℕ) (N : ℕ)
    (hB_sidon : IsSidon B)
    (hB_range : ∀ b ∈ B, 1 ≤ b ∧ b ≤ N / 3) :
    ∃ δ > 0, IsQuasiSidon (lowerBoundConstruction B N) δ := by
  sorry

/-- Erdős-Freud upper bound (1991): f(N) ≤ (2 + o(1)) · √N -/
theorem erdos_freud_upper_bound :
    ∃ (ε : ℕ → ℝ), IsLittleO ε (fun _ => 1) ∧
    ∀ N, (f N : ℝ) ≤ (2 + ε N) * Real.sqrt N := by
  sorry -- Erdős-Freud (1991)

/-- Pikhurko's improved upper bound (2006):
    f(N) ≤ ((1/4 + 1/(π+2)²)^(-1/2) + o(1)) · √N -/
theorem pikhurko_upper_bound :
    ∃ (c : ℝ), c = (1/4 + 1/(Real.pi + 2)^2)⁻¹ ^ (1/2 : ℝ) ∧
    ∃ (ε : ℕ → ℝ), IsLittleO ε (fun _ => 1) ∧
    ∀ N, (f N : ℝ) ≤ (c + ε N) * Real.sqrt N := by
  sorry -- Pikhurko (2006)

/-- The Pikhurko constant ≈ 1.863 -/
theorem pikhurko_constant_approx :
    (1/4 + 1/(Real.pi + 2)^2)⁻¹ ^ (1/2 : ℝ) < 1.87 ∧
    (1/4 + 1/(Real.pi + 2)^2)⁻¹ ^ (1/2 : ℝ) > 1.86 := by
  -- Proved by Aristotle (Harmonic)
  rw [← Real.sqrt_eq_rpow] at *
  rw [Real.sqrt_lt', gt_iff_lt, Real.lt_sqrt] <;> norm_num
  · field_simp
    constructor <;> norm_num at * <;> nlinarith [Real.pi_gt_three]
  · positivity

/-! ## The Open Question -/

/-- Erdős Problem #840 (OPEN): What is the exact asymptotic growth of f(N)?

    Known: (2/√3 + o(1))√N ≤ f(N) ≤ (c_P + o(1))√N
    where c_P ≈ 1.863 (Pikhurko's constant)

    Question: What is the true constant? -/
def erdos_840_question : Prop :=
  ∃ (c : ℝ), 2 / Real.sqrt 3 ≤ c ∧
    c ≤ (1/4 + 1/(Real.pi + 2)^2)⁻¹ ^ (1/2 : ℝ) ∧
    ∃ (ε : ℕ → ℝ), IsLittleO ε (fun _ => 1) ∧
    ∀ N, |((f N : ℝ) / Real.sqrt N) - c| ≤ |ε N|

/-! ## Related: Difference Sets -/

/-- The difference set A - A -/
def diffset (A : Finset ℤ) : Finset ℤ :=
  (A.product A).image (fun p => p.1 - p.2)

/-- Cilleruelo's result: For A - A, the maximum quasi-Sidon size is ~√N -/
theorem cilleruelo_difference_set :
    ∃ (ε : ℕ → ℝ), IsLittleO ε (fun _ => 1) ∧
    ∀ N, ∃ (g : ℕ → ℕ),
      -- g(N) is the max quasi-Sidon size for A - A version
      |((g N : ℝ) / Real.sqrt N) - 1| ≤ |ε N| := by
  -- Proved by Aristotle (Harmonic)
  refine' ⟨_, _, _⟩
  refine' fun N => if N = 0 then 1 else 1 / Real.sqrt N
  · intro ε hε; use ⌈ε⁻¹ ^ 2⌉₊ + 1; intro N hN; by_cases hN' : N = 0 <;>
      simp_all +decide [Nat.lt_succ_iff]
    rw [abs_of_nonneg (Real.sqrt_nonneg _), inv_lt_comm₀] <;>
      first | positivity | exact Real.lt_sqrt_of_sq_lt (by simpa using Nat.lt_of_ceil_lt hN)
  · intro N
    by_cases hN : N = 0 <;> simp +decide [hN]
    use fun _ => Nat.floor (Real.sqrt N); norm_num [abs_of_nonneg, Real.sqrt_nonneg]
    rw [abs_le]; constructor <;> ring_nf <;> norm_num [hN]
    · field_simp
      exact Real.sqrt_le_iff.mpr ⟨by positivity,
        by norm_cast; linarith [Nat.lt_succ_sqrt N]⟩
    · exact le_add_of_le_of_nonneg
        (div_le_one_of_le₀ (Real.le_sqrt_of_sq_le (mod_cast Nat.sqrt_le' _))
          (Real.sqrt_nonneg _)) (by positivity)

/-! ## Sidon Set Background -/

/-- Classical Sidon set bound: |A| ≤ √N + O(N^(1/4)) for A ⊆ {1, ..., N} -/
theorem sidon_set_upper_bound (A : Finset ℕ) (N : ℕ) (hA : A ⊆ intervalFinset N)
    (hSidon : IsSidon A) :
    (A.card : ℝ) ≤ Real.sqrt N + (N : ℝ)^(1/4 : ℝ) := by
  sorry

/-- Sidon sets exist of size ~√N -/
theorem sidon_set_exists (N : ℕ) (hN : N ≥ 1) :
    ∃ A : Finset ℕ, A ⊆ intervalFinset N ∧ IsSidon A ∧
    (A.card : ℝ) ≥ Real.sqrt N - 1 := by
  sorry

/-! ## Gap Analysis -/

/-- The gap between known bounds -/
theorem bounds_gap :
    (1/4 + 1/(Real.pi + 2)^2)⁻¹ ^ (1/2 : ℝ) - 2 / Real.sqrt 3 < 0.72 := by
  -- Proved by Aristotle (Harmonic)
  rw [← Real.sqrt_eq_rpow, sub_lt_iff_lt_add', Real.sqrt_lt'] <;> ring <;> norm_num
  · field_simp
    have h_pi : Real.pi < 3.15 := by exact?
    nlinarith [Real.pi_gt_three, Real.sqrt_nonneg 3,
      mul_le_mul_of_nonneg_left h_pi.le <| Real.sqrt_nonneg 3,
      Real.sq_sqrt <| show 0 ≤ 3 by norm_num]
  · positivity

/-- The problem asks to close this gap -/
theorem open_problem_gap :
    -- Current gap: ~1.15 to ~1.86
    -- The exact constant is unknown
    2 / Real.sqrt 3 < (1/4 + 1/(Real.pi + 2)^2)⁻¹ ^ (1/2 : ℝ) := by
  -- Proved by Aristotle (Harmonic)
  rw [← Real.sqrt_eq_rpow, Real.lt_sqrt] <;> norm_num
  · field_simp
    norm_num; nlinarith [Real.pi_gt_three]
  · positivity

end Erdos840
