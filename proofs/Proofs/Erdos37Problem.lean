/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 43de7d32-d24a-4a49-8723-3e384c5843fa

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem schnirelmannDensity_mem_Icc (A : Set ℕ) :
    schnirelmannDensity A ∈ Set.Icc 0 1

- theorem lacunary_counting_bound (A : Set ℕ) (hA : IsLacunarySet A) :
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ N in atTop,
      (countingFunction A N : ℝ) ≤ C * Real.log N
-/

/-
  Erdős Problem #37: Essential Components and Lacunary Sets

  Source: https://erdosproblems.com/37
  Status: DISPROVED (Ruzsa 1987)

  Statement:
  Can a lacunary set A ⊂ ℕ be an essential component?

  **Definition**: A set A is an **essential component** if d_s(A + B) > d_s(B)
  for every B ⊂ ℕ with 0 < d_s(B) < 1, where d_s is Schnirelmann density.

  **Definition**: A set is **lacunary** if its elements grow exponentially,
  e.g., A = {2^n : n ∈ ℕ} or A = {a_n} where a_{n+1}/a_n ≥ λ > 1.

  **Answer**: NO - lacunary sets cannot be essential components.

  **Ruzsa's Theorem (1987)**:
  If A is an essential component, then there exists c > 0 such that
  |A ∩ {1,...,N}| ≥ (log N)^{1+c} for all sufficiently large N.

  Lacunary sets have |A ∩ {1,...,N}| = O(log N), which is much smaller than
  (log N)^{1+c}, so they cannot be essential components.

  **Optimality**: For any c > 0, there exists an essential component A with
  |A ∩ {1,...,N}| ≤ (log N)^{1+c} for large N.

  **Open Question** (Ruzsa 1999): Is {2^m · 3^n : m,n ∈ ℕ} an essential component?
  This set grows faster than lacunary but slower than (log N)^{1+c}.

  References:
  - [Er56], [Er61], [Er73], [ErGr80]
  - Ruzsa (1987, 1999) [Ru87], [Ru99]
-/

import Mathlib


open Set Finset BigOperators Filter

namespace Erdos37

/-!
## Schnirelmann Density

The Schnirelmann density is a fundamental concept in additive number theory.
Unlike natural density (which uses limits), Schnirelmann density uses an infimum,
making it well-suited for studying sumsets.
-/

/-- The counting function: number of elements of A in {1, ..., n}. -/
noncomputable def countingFunction (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard (A ∩ Set.Icc 1 n)

/-- **Schnirelmann density** of a set A ⊆ ℕ.
    d_s(A) = inf_{n ≥ 1} |A ∩ {1,...,n}| / n

    This is always in [0, 1]. Key property: d_s(A) = 1 iff 1 ∈ A and
    the density stays at 1 for all initial segments. -/
noncomputable def schnirelmannDensity (A : Set ℕ) : ℝ :=
  iInf fun n : {m : ℕ // m ≥ 1} => (countingFunction A n.val : ℝ) / n.val

/-- Schnirelmann density is always in [0, 1]. -/
theorem schnirelmannDensity_mem_Icc (A : Set ℕ) :
    schnirelmannDensity A ∈ Set.Icc 0 1 := by
  constructor;
  · exact Real.iInf_nonneg fun n => div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ );
  · -- Since the counting function is at most n for any n, dividing by n gives a value that's at most 1. Therefore, the infimum of these values must also be at most 1.
    have h_le_one : ∀ n : {m : ℕ // m ≥ 1}, (countingFunction A n.val : ℝ) / n.val ≤ 1 := by
      intro n;
      refine' div_le_one_of_le₀ _ _ <;> norm_cast;
      · exact le_trans ( Set.ncard_le_ncard ( Set.inter_subset_right ) ) ( by simpa [ Set.ncard_eq_toFinset_card' ] );
      · bound;
    exact ciInf_le_of_le ⟨ 0, Set.forall_mem_range.2 fun _ => div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ⟩ ⟨ 1, by norm_num ⟩ ( h_le_one _ )

/-!
## Sumsets

The sumset A + B consists of all sums a + b where a ∈ A and b ∈ B.
-/

/-- The sumset A + B = {a + b : a ∈ A, b ∈ B}. -/
def sumset (A B : Set ℕ) : Set ℕ :=
  {n | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

notation:65 A " +ₛ " B => sumset A B

/-!
## Essential Components

A set A is an essential component if adding it to any set B with
positive Schnirelmann density strictly increases the density.
-/

/-- A set A is an **essential component** if d_s(A + B) > d_s(B)
    for every B with 0 < d_s(B) < 1.

    Essential components are "additively helpful" - they always
    increase the Schnirelmann density when added to a set. -/
def IsEssentialComponent (A : Set ℕ) : Prop :=
  ∀ B : Set ℕ, 0 < schnirelmannDensity B → schnirelmannDensity B < 1 →
    schnirelmannDensity (A +ₛ B) > schnirelmannDensity B

/-!
## Lacunary Sets

A lacunary set has elements that grow exponentially fast.
The canonical example is {2^n : n ∈ ℕ}.
-/

/-- A sequence is **lacunary** with ratio r > 1 if a_{n+1} ≥ r · a_n. -/
def IsLacunarySeq (a : ℕ → ℕ) (r : ℝ) : Prop :=
  r > 1 ∧ ∀ n : ℕ, (a (n + 1) : ℝ) ≥ r * a n

/-- A set A is **lacunary** if it can be enumerated as a lacunary sequence. -/
def IsLacunarySet (A : Set ℕ) : Prop :=
  ∃ (a : ℕ → ℕ) (r : ℝ), StrictMono a ∧ IsLacunarySeq a r ∧
    A = Set.range a

/-- The powers of 2 form a lacunary set. -/
def powersOfTwo : Set ℕ := {n | ∃ k : ℕ, n = 2^k}

theorem powersOfTwo_lacunary : IsLacunarySet powersOfTwo := by
  use fun k => 2^k, 2
  refine ⟨?_, ?_, ?_⟩
  · intro m n hmn
    exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) hmn
  · constructor
    · norm_num
    · intro n
      simp only [pow_succ]
      ring_nf
      norm_cast
  · ext n
    simp only [Set.mem_range, powersOfTwo, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩
    · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩

/-!
## Growth Bounds

Essential components must grow at least as fast as (log N)^{1+c}.
Lacunary sets grow only as fast as log N.
-/

/- Lacunary sets have counting function O(log N). -/
noncomputable section AristotleLemmas

/-
If a sequence is lacunary with ratio r, then a_n >= a_0 * r^n.
-/
lemma lacunary_sequence_growth {a : ℕ → ℕ} {r : ℝ} (h : IsLacunarySeq a r) (n : ℕ) :
    (a n : ℝ) ≥ a 0 * r ^ n := by
      induction' n with n ih;
      · norm_num;
      · rw [ pow_succ', mul_left_comm ] ; nlinarith [ h.2 n, show ( 1 : ℝ ) ≤ r by linarith [ h.1 ] ] ;

/-
If a sequence is lacunary, the index n grows at most logarithmically with the value a_n.
-/
lemma lacunary_index_upper_bound {a : ℕ → ℕ} {r : ℝ} (h_lac : IsLacunarySeq a r) (h_mono : StrictMono a) :
    ∃ C, ∀ᶠ N in atTop, ∀ n, a n ≤ N → (n : ℝ) ≤ C * Real.log N := by
      rcases eq_or_ne ( a 0 ) 0 with ha|ha <;> simp_all +decide [ Erdos37.IsLacunarySeq ];
      · -- For $n \geq 1$, we have $a_n \geq r^{n-1}$.
        have h_an_ge_r_pow : ∀ n ≥ 1, (a n : ℝ) ≥ r ^ (n - 1) := by
          intros n hn_ge_1
          induction' n, hn_ge_1 using Nat.le_induction with n hn ih;
          · have := h_mono zero_lt_one; aesop;
          · exact le_trans ( by cases n <;> simp_all +decide [ pow_succ' ] ; nlinarith ) ( h_lac.2 n );
        -- Taking logarithms gives $n - 1 \leq \log_r(N)$.
        have h_n_minus_1_le_log : ∀ n ≥ 1, ∀ N, a n ≤ N → (n - 1 : ℝ) ≤ Real.log N / Real.log r := by
          intros n hn N hN
          have h_log : Real.log (a n) ≥ (n - 1 : ℝ) * Real.log r := by
            simpa [ Nat.cast_sub hn ] using Real.log_le_log ( pow_pos ( by linarith ) _ ) ( h_an_ge_r_pow n hn );
          rw [ le_div_iff₀ ( Real.log_pos h_lac.1 ) ];
          exact h_log.trans ( Real.log_le_log ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by linarith [ h_mono hn ] ) <| Nat.cast_le.mpr hN );
        -- For large $N$, this implies $n \leq \frac{\log N}{\log r} + 1$.
        have h_n_le_log_plus_one : ∀ᶠ N in Filter.atTop, ∀ n, a n ≤ N → (n : ℝ) ≤ (Real.log N / Real.log r) + 1 := by
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN using fun n hn => if hn' : n ≥ 1 then by linarith [ h_n_minus_1_le_log n hn' N hn ] else by interval_cases n ; norm_num at * ; linarith [ show ( 0 :ℝ ) ≤ Real.log N / Real.log r by exact div_nonneg ( Real.log_natCast_nonneg _ ) ( Real.log_nonneg h_lac.1.le ) ] ;
        -- Choose $C = \frac{1}{\log r} + 1$.
        use (1 / Real.log r) + 1;
        obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp h_n_le_log_plus_one;
        refine' ⟨ N + ⌈Real.exp 1⌉₊ + 1, fun b hb n hn => le_trans ( hN b ( by linarith ) n hn ) _ ⟩ ; ring_nf
        -- Goal: 1 + log b * (log r)⁻¹ ≤ log b + log b * (log r)⁻¹, i.e., 1 ≤ log b
        have hb_ge_e : (b : ℝ) ≥ Real.exp 1 := calc (b : ℝ) ≥ N + ⌈Real.exp 1⌉₊ + 1 := by exact_mod_cast hb
            _ ≥ ⌈Real.exp 1⌉₊ := by linarith
            _ ≥ Real.exp 1 := Nat.ceil_le.mp (le_refl _)
        have hlogb_ge_1 : Real.log b ≥ 1 := by rw [ge_iff_le, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hb_ge_e
        linarith
      · use 1 / Real.log r, a 0;
        -- By definition of $a$, we know that $a n \geq a 0 * r^n$ for all $n$.
        have h_an_ge : ∀ n, (a n : ℝ) ≥ a 0 * r ^ n := fun n => lacunary_sequence_growth h_lac n
        intro b hb n hn; rw [ div_mul_eq_mul_div, le_div_iff₀ ( Real.log_pos h_lac.1 ) ] ; have := h_an_ge n; norm_num at *;
        rw [ ← Real.log_pow ] ; gcongr ; norm_cast at * ; nlinarith [ pow_pos ( zero_lt_one.trans h_lac.1 ) n ];
        nlinarith [ show ( a 0 : ℝ ) ≥ 1 by exact_mod_cast Nat.pos_of_ne_zero ha, show ( a n : ℝ ) ≤ b by exact_mod_cast hn ]

end AristotleLemmas

theorem lacunary_counting_bound (A : Set ℕ) (hA : IsLacunarySet A) :
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ N in atTop,
      (countingFunction A N : ℝ) ≤ C * Real.log N := by
  obtain ⟨ a, r, ha_mono, ha_lac, rfl ⟩ := hA;
  -- By lacunary_index_upper_bound, there exists C' such that for large N, if a n ≤ N, then n ≤ C' * log N.
  obtain ⟨C', hC'⟩ : ∃ C' > 0, ∀ᶠ N in Filter.atTop, ∀ n, a n ≤ N → (n : ℝ) ≤ C' * Real.log N := by
    obtain ⟨ C', hC' ⟩ := lacunary_index_upper_bound ha_lac ha_mono;
    exact ⟨ Max.max C' 1, by positivity, by filter_upwards [ hC', Filter.eventually_gt_atTop 1 ] with N hN hN' n hn; exact le_trans ( hN n hn ) ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( Real.log_nonneg ( mod_cast hN'.le ) ) ) ⟩;
  -- The counting function K(N) is the number of elements of A in [1, N].
  -- Since A = range a and a is strictly monotone, the elements of A are a_0, a_1, ...
  -- If K(N) = k, then there are k indices n such that 1 ≤ a n ≤ N.
  -- Let m be the largest such index. Then a m ≤ N.
  -- By the bound, m ≤ C' * log N.
  -- The number of such indices is at most m + 1 (indices 0 to m).
  -- So K(N) ≤ m + 1 ≤ C' * log N + 1.
  have h_counting_function : ∀ᶠ N in Filter.atTop, Erdos37.countingFunction (Set.range a) N ≤ C' * Real.log N + 1 := by
    filter_upwards [ hC'.2, Filter.eventually_ge_atTop 1 ] with N hN₁ hN₂;
    -- The set {a n | n ≤ m} has cardinality m + 1.
    have h_card : Set.ncard (Set.range a ∩ Set.Icc 1 N) ≤ Nat.card (Finset.filter (fun n => a n ≤ N) (Finset.range (Nat.succ (Nat.floor (C' * Real.log N))))) := by
      have h_card : Set.range a ∩ Set.Icc 1 N ⊆ Set.image a (Finset.filter (fun n => a n ≤ N) (Finset.range (Nat.succ (Nat.floor (C' * Real.log N))))) := by
        rintro x ⟨ ⟨ n, rfl ⟩, hn₁, hn₂ ⟩ ; exact ⟨ n, Finset.mem_coe.mpr <| Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Nat.le_floor <| hN₁ n hn₂, hn₂ ⟩, rfl ⟩ ;
      refine' le_trans ( Set.ncard_le_ncard h_card ) _;
      rw [ Set.ncard_image_of_injective _ ha_mono.injective ] ; aesop;
    refine' le_trans ( Nat.cast_le.mpr h_card ) _;
    rw [ Nat.card_eq_fintype_card, Fintype.card_coe ];
    refine' le_trans ( Nat.cast_le.mpr <| Finset.card_filter_le _ _ ) _ ; norm_num;
    exact Nat.floor_le ( mul_nonneg hC'.1.le ( Real.log_nonneg ( Nat.one_le_cast.mpr hN₂ ) ) );
  refine' ⟨ C' + 1, by linarith, _ ⟩;
  filter_upwards [ h_counting_function, Filter.eventually_gt_atTop 2 ] with N hN₁ hN₂ using le_trans hN₁ <| by nlinarith [ show 1 ≤ Real.log N from by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( N :ℝ ) ≥ 3 by exact_mod_cast hN₂ ] ] ;

/-!
## Main Results
-/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry253387', 'Erdos37.ruzsa_essential_component_lower_bound']-/
/--
**Ruzsa's Lower Bound (1987)**:
If A is an essential component, then there exists c > 0 such that
|A ∩ {1,...,N}| ≥ (log N)^{1+c} for all sufficiently large N.

This is the key result that shows lacunary sets cannot be essential components.
-/
axiom ruzsa_essential_component_lower_bound :
    ∀ A : Set ℕ, IsEssentialComponent A →
      ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in atTop,
        (countingFunction A N : ℝ) ≥ (Real.log N)^(1 + c)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['Erdos37.ruzsa_essential_component_construction', 'harmonicSorry747414']-/
/--
**Ruzsa's Upper Bound (1987)**:
For any c > 0, there exists an essential component A with
|A ∩ {1,...,N}| ≤ (log N)^{1+c} for large N.

This shows the lower bound is optimal.
-/
axiom ruzsa_essential_component_construction :
    ∀ c : ℝ, c > 0 →
      ∃ A : Set ℕ, IsEssentialComponent A ∧
        ∀ᶠ N in atTop, (countingFunction A N : ℝ) ≤ (Real.log N)^(1 + c)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['Erdos37.erdos_37_disproved', 'harmonicSorry419681']-/
/--
**Erdős Problem #37 (DISPROVED)**:
No lacunary set can be an essential component.

Proof sketch: Lacunary sets have |A ∩ {1,...,N}| = O(log N), but
Ruzsa proved essential components need |A ∩ {1,...,N}| ≥ (log N)^{1+c}
for some c > 0. Since log N < (log N)^{1+c} for large N, lacunary sets
fail the growth requirement.
-/
axiom erdos_37_disproved :
    ∀ A : Set ℕ, IsLacunarySet A → ¬IsEssentialComponent A

/-- Alternative statement: The main question is answered negatively. -/
def Erdos37Question : Prop :=
  ∃ A : Set ℕ, IsLacunarySet A ∧ IsEssentialComponent A

theorem erdos_37_answer : ¬Erdos37Question := by
  intro ⟨A, hLac, hEss⟩
  exact erdos_37_disproved A hLac hEss

/-!
## The 2^m · 3^n Question (OPEN)

Ruzsa (1999) asked whether the set {2^m · 3^n : m, n ∈ ℕ} is an
essential component. This is NOT lacunary (it has growth
|A ∩ {1,...,N}| ~ (log N)^2 / (2 log 2 · log 3)).
-/

/-- The set of numbers of the form 2^m · 3^n. -/
def smoothNumbers23 : Set ℕ := {n | ∃ m k : ℕ, n = 2^m * 3^k}

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry175979', 'Erdos37.smooth23_counting']-/
/-- Counting function for 2^m · 3^n is asymptotic to (log N)^2 / constant. -/
axiom smooth23_counting :
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ N in atTop,
      |(countingFunction smoothNumbers23 N : ℝ) - C * (Real.log N)^2| ≤ Real.log N

/-- Ruzsa's open question: Is {2^m · 3^n} an essential component?
    This remains OPEN as of the latest update. -/
def RuzsaOpenQuestion : Prop := IsEssentialComponent smoothNumbers23

/-!
## Classical Results on Schnirelmann Density
-/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry257958', 'Erdos37.schnirelmann_theorem']-/
/-- **Schnirelmann's Theorem**: If d_s(A) + d_s(B) ≥ 1, then A + B = ℕ
    (contains all positive integers). -/
axiom schnirelmann_theorem :
    ∀ A B : Set ℕ, schnirelmannDensity A + schnirelmannDensity B ≥ 1 →
      ∀ n : ℕ, n ≥ 1 → n ∈ A +ₛ B

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry52923', 'Erdos37.mann_theorem']-/
/-- **Mann's Theorem**: d_s(A + B) ≥ min(1, d_s(A) + d_s(B)).
    This is stronger than Schnirelmann's original bound. -/
axiom mann_theorem :
    ∀ A B : Set ℕ,
      schnirelmannDensity (A +ₛ B) ≥ min 1 (schnirelmannDensity A + schnirelmannDensity B)

/-!
## Summary

**Erdős Problem #37** asked whether lacunary sets can be essential components.

**Answer**: NO (Ruzsa 1987)

**Key insight**: Essential components must grow at least as (log N)^{1+c},
but lacunary sets grow only as log N.

**Optimality**: The (log N)^{1+c} bound is tight - essential components
can grow arbitrarily close to this rate.

**Open question**: Is {2^m · 3^n} an essential component? (Growth ~ (log N)^2)
-/

end Erdos37