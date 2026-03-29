/-
  Aristotle targets for Erdős Problem #956
  Routine supporting lemmas for automated proof search.
  See Erdos956Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (h(n) > n^(1+c))
  - Known results from Mathlib: set distance properties, convexity/compactness
    preservation under translation, basic analysis inequalities
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos956Aristotle

open Set Metric Finset

/-- The distance between two sets in a metric space. -/
noncomputable def setDistance {X : Type*} [PseudoMetricSpace X] (C D : Set X) : ℝ :=
  sInf { dist c d | (c : X) (d : X) (_ : c ∈ C) (_ : d ∈ D) }

/-- A translate C + x of a set. -/
def translate (C : Set (EuclideanSpace ℝ (Fin 2))) (x : EuclideanSpace ℝ (Fin 2)) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  { c + x | c ∈ C }

-- Routine: Symmetry of set distance (follows from dist_comm)
theorem setDistance_symm {X : Type*} [PseudoMetricSpace X] (C D : Set X) :
    setDistance C D = setDistance D C := by
  unfold setDistance
  congr 1
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, d, hc, hd, rfl⟩
    exact ⟨d, c, hd, hc, (dist_comm c d).symm⟩
  · rintro ⟨d, c, hd, hc, rfl⟩
    exact ⟨c, d, hc, hd, (dist_comm c d)⟩

/-
PROBLEM
Routine: Non-negativity of set distance (dist is non-negative, so is its infimum)

PROVIDED SOLUTION
Unfold setDistance. If the set of distances is empty, sInf of empty set is 0 >= 0. Otherwise, use le_csInf with the fact that dist is nonneg. Note that the set representation may use exists with equality flipped (dist c d = x vs x = dist c d), so be careful with the exact form.
-/
theorem setDistance_nonneg {X : Type*} [PseudoMetricSpace X] (C D : Set X) :
    setDistance C D ≥ 0 := by
  -- Apply the fact that the infimum of a set of nonnegative numbers is nonnegative.
  apply Real.sInf_nonneg; intro x hx
  aesop

-- Routine: Translates preserve convexity
theorem translate_convex (C : Set (EuclideanSpace ℝ (Fin 2))) (x : EuclideanSpace ℝ (Fin 2))
    (hC : Convex ℝ C) : Convex ℝ (translate C x) := by
  intro a ha b hb t₁ t₂ ht₁ ht₂ ht
  obtain ⟨ca, hca, rfl⟩ := ha
  obtain ⟨cb, hcb, rfl⟩ := hb
  refine ⟨t₁ • ca + t₂ • cb, hC hca hcb ht₁ ht₂ ht, ?_⟩
  simp only [smul_add]
  have : t₁ • ca + t₁ • x + (t₂ • cb + t₂ • x) =
      (t₁ • ca + t₂ • cb) + (t₁ • x + t₂ • x) := by abel
  rw [this, ← add_smul, ht, one_smul]

/-
PROBLEM
Routine: Translates preserve compactness

PROVIDED SOLUTION
Show translate C x = (· + x) '' C, then use IsCompact.image with continuity of addition.
-/
theorem translate_compact (C : Set (EuclideanSpace ℝ (Fin 2))) (x : EuclideanSpace ℝ (Fin 2))
    (hC : IsCompact C) : IsCompact (translate C x) := by
  convert hC.image _ using 1;
  continuity

-- Routine: Translation preserves nonemptiness
theorem translate_nonempty (C : Set (EuclideanSpace ℝ (Fin 2))) (x : EuclideanSpace ℝ (Fin 2))
    (hC : C.Nonempty) : (translate C x).Nonempty := by
  obtain ⟨c, hc⟩ := hC
  exact ⟨c + x, ⟨c, hc, rfl⟩⟩

/-
PROBLEM
Routine: Distance between singletons equals point distance

PROVIDED SOLUTION
Unfold setDistance. Show the set { dist c d | c ∈ {a}, d ∈ {b} } = {dist a b}, then csInf of a singleton is the element itself.
-/
theorem setDistance_singletons {X : Type*} [PseudoMetricSpace X] (a b : X) :
    setDistance {a} {b} = dist a b := by
  exact le_antisymm ( csInf_le ⟨ 0, by rintro x ⟨ c, d, hc, hd, rfl ⟩ ; positivity ⟩ ⟨ _, _, rfl, rfl, rfl ⟩ ) ( le_csInf ⟨ _, ⟨ _, _, rfl, rfl, rfl ⟩ ⟩ fun x hx => by aesop )

-- Routine: The general convex set exponent 7/5 exceeds the translate exponent 4/3
theorem general_exponent_larger : (7 : ℝ) / 5 > 4 / 3 := by norm_num

/-
PROBLEM
Routine: For large n, n^(4/3) > n * log n / log log n

PROVIDED SOLUTION
For n ≥ 100, we need n^(4/3) > n * log n / log(log n). This is equivalent to n^(1/3) > log n / log(log n). For n = 100, n^(1/3) ≈ 4.64, log 100 ≈ 4.6, log(log 100) ≈ 1.53, so log n / log(log n) ≈ 3.0. And n^(1/3) grows polynomially while log n / log(log n) grows much slower. One approach: use native_decide or norm_num for the base case and monotonicity. Alternatively, bound log n ≤ n^(1/6) and log(log n) ≥ 1 for large n, giving the ratio ≤ n^(1/6) which is less than n^(1/3).
-/
theorem power_dominates_log_ratio (n : ℕ) (hn : n ≥ 100) :
    (n : ℝ) ^ ((4 : ℝ) / 3) > n * Real.log n / Real.log (Real.log n) := by
  -- We'll use that $n \geq 100$ to show that $n^{1/3} > \log n / \log(\log n)$ for $n \geq 100$.
  have h_ratio : ∀ n : ℕ, 100 ≤ n → (n : ℝ) ^ (1 / 3 : ℝ) > Real.log n / Real.log (Real.log n) := by
    intro n hn; refine' lt_of_le_of_lt ( div_le_self ( Real.log_nonneg <| Nat.one_le_cast.2 <| by linarith ) _ ) _;
    · rw [ Real.le_log_iff_exp_le ( Real.log_pos <| by norm_cast; linarith ) ];
      -- We'll use that $Real.log n \geq 4$ for $n \geq 100$.
      have h_log_ge_4 : Real.log n ≥ 4 := by
        rw [ ge_iff_le, Real.le_log_iff_exp_le ( by positivity ) ];
        exact le_trans ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show Real.exp 4 = ( Real.exp 1 ) ^ 4 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this 4 ) ( by norm_num ) ) ( Nat.cast_le.mpr hn );
      exact le_trans ( Real.exp_one_lt_d9.le ) ( by norm_num; linarith );
    · -- Let $y = \sqrt[3]{n}$, then we have $n = y^3$.
      set y : ℝ := (n : ℝ) ^ (1 / 3 : ℝ)
      have hn_eq_y3 : (n : ℝ) = y ^ 3 := by
        rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num;
      -- We'll use that $y \geq 4.64$ for $n \geq 100$.
      have hy_ge_4_64 : y ≥ 4.64 := by
        -- We'll use that $y \geq 4.64$ for $n \geq 100$. Since $n \geq 100$, we have $y^3 \geq 100$.
        have hy_ge_4_64 : y ^ 3 ≥ 100 := by
          exact hn_eq_y3 ▸ mod_cast hn;
        norm_num; nlinarith [ sq_nonneg ( y^2 ) ] ;
      -- We'll use that $Real.log y < y / 3$ for $y \geq 4.64$.
      have h_log_y_lt_y_div_3 : Real.log y < y / 3 := by
        have := Real.log_lt_sub_one_of_pos ( show 0 < y / 4 by positivity );
        rw [ Real.log_div ] at this <;> norm_num at * <;> try linarith;
        have := this ( by linarith ) ; have := Real.log_two_lt_d9; norm_num1 at *; rw [ show ( 4 : ℝ ) = 2 ^ 2 by norm_num, Real.log_pow ] at *; norm_num at *; linarith;
      rw [ hn_eq_y3, Real.log_pow ] ; norm_num at * ; linarith;
  rw [ show ( 4 / 3 : ℝ ) = 1 + 1 / 3 by norm_num, Real.rpow_add' ] <;> norm_num ; ring_nf at * ; nlinarith [ h_ratio n hn, show ( n :ℝ ) ≥ 100 by exact_mod_cast hn ]

end Erdos956Aristotle