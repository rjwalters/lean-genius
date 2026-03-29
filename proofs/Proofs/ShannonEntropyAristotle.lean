/-
  Aristotle targets for Shannon Entropy
  Routine supporting lemmas for automated proof search.
  See ShannonEntropy.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely in Mathlib (Jensen, convexity, etc.)
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)

  Status: 2 targets remaining (log_sum_inequality, conditioning_reduces_entropy)
  Already proved in main file: kl_divergence_nonneg, gibbs_inequality,
  entropy_le_log_card, mutual_info_nonneg
-/
import Mathlib

namespace InformationTheory.Aristotle

/-
PROBLEM
============================================================
Log-Sum Inequality
============================================================

Log-sum inequality: Σ aᵢ log(aᵢ/bᵢ) ≥ (Σ aᵢ) log(Σ aᵢ / Σ bᵢ)
This follows from Jensen's inequality applied to the convex function t ↦ t * log t.

PROVIDED SOLUTION
Use Jensen's inequality for the convex function f(t) = t * log(t) on (0,∞). Write each aᵢ * log(aᵢ/bᵢ) = bᵢ * f(aᵢ/bᵢ). Then by Jensen: Σ bᵢ * f(aᵢ/bᵢ) ≥ (Σ bᵢ) * f(Σ bᵢ * (aᵢ/bᵢ) / Σ bᵢ) = (Σ bᵢ) * f((Σ aᵢ) / (Σ bᵢ)). The last expression equals (Σ aᵢ) * log((Σ aᵢ)/(Σ bᵢ)). If this approach is hard to formalize directly via Jensen, an alternative is to use the fact that KL divergence is nonneg (log_sum_inequality is essentially a restatement). Or prove directly: for each i, aᵢ * log(aᵢ/bᵢ) ≥ aᵢ - bᵢ (by log x ≤ x - 1 applied to bᵢ/aᵢ when aᵢ > 0), then use a more refined argument. Actually the simplest approach may be: note that x*log(x) is convex for x > 0, use weights wᵢ = bᵢ/(Σ bᵢ) and points xᵢ = aᵢ/bᵢ in Jensen's inequality.
-/
theorem log_sum_inequality {n : ℕ} {a b : Fin n → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 < b i) :
    ∑ i, a i * Real.log (a i / b i) ≥
    (∑ i, a i) * Real.log ((∑ i, a i) / ∑ i, b i) := by
      by_contra! h_contra;
      -- Apply Jensen's inequality to the convex function $f(x) = x \log(x)$ with weights $b_i$.
      have h_jensen : ∑ i, b i * (a i / b i) * Real.log (a i / b i) ≥ (∑ i, b i) * ((∑ i, a i) / (∑ i, b i)) * Real.log ((∑ i, a i) / (∑ i, b i)) := by
        -- We'll use that $f(x) = x \log x$ is convex to apply Jensen's inequality.
        have h_convex : ConvexOn ℝ (Set.Ici 0) (fun x => x * Real.log x) := by
          exact ( Real.convexOn_mul_log )
        generalize_proofs at *; (
        -- Apply Jensen's inequality with the weights $b_i$ and the values $a_i / b_i$.
        have h_jensen : (∑ i, b i * (a i / b i) * Real.log (a i / b i)) / (∑ i, b i) ≥ ((∑ i, b i * (a i / b i)) / (∑ i, b i)) * Real.log ((∑ i, b i * (a i / b i)) / (∑ i, b i)) := by
          have h_jensen : (∑ i, (b i / ∑ i, b i) * (a i / b i * Real.log (a i / b i))) ≥ ((∑ i, (b i / ∑ i, b i) * (a i / b i))) * Real.log ((∑ i, (b i / ∑ i, b i) * (a i / b i))) := by
            apply ConvexOn.map_sum_le h_convex
            generalize_proofs at *; (
            exact fun i _ => div_nonneg ( le_of_lt ( hb i ) ) ( Finset.sum_nonneg fun _ _ => le_of_lt ( hb _ ) ));
            · rw [ ← Finset.sum_div, div_self <| ne_of_gt <| Finset.sum_pos ( fun _ _ => hb _ ) ⟨ ⟨ 0, Nat.pos_of_ne_zero <| by rintro rfl; norm_num at * ⟩, Finset.mem_univ _ ⟩ ];
            · exact fun i _ => div_nonneg ( ha i ) ( le_of_lt ( hb i ) )
          generalize_proofs at *; (
          simp_all +decide [ div_eq_inv_mul, mul_assoc, Finset.mul_sum _ _ _, Finset.sum_mul ])
        generalize_proofs at *; (
        simp_all +decide [ mul_div_cancel₀ _ ( ne_of_gt ( hb _ ) ) ];
        rw [ le_div_iff₀ ] at h_jensen <;> linarith [ Finset.sum_pos ( fun i _ => hb i ) ⟨ ⟨ 0, Nat.pos_of_ne_zero ( by rintro rfl; norm_num at h_contra ) ⟩, Finset.mem_univ _ ⟩ ] ;));
      simp_all +decide [ mul_div_cancel₀ _ ( ne_of_gt ( hb _ ) ) ];
      rw [ mul_div_cancel₀ _ ( ne_of_gt <| Finset.sum_pos ( fun _ _ => hb _ ) ⟨ ⟨ 0, Nat.pos_of_ne_zero <| by rintro rfl; norm_num at * ⟩, Finset.mem_univ _ ⟩ ) ] at h_jensen ; linarith

-- ============================================================
-- Conditioning Reduces Entropy
-- ============================================================

-- Shannon entropy for finite distributions (reproduced for self-containment)
noncomputable def shannonEntropy {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) : ℝ :=
  -∑ x : α, if p x = 0 then 0 else p x * Real.log (p x)

-- Conditional entropy H(X|Y) = -Σ_x Σ_y p(x,y) log(p(x,y)/p(y))
noncomputable def conditionalEntropy {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (pXY : α × β → ℝ) : ℝ :=
  -(∑ x : α, ∑ y : β,
    if pXY (x, y) = 0 then 0
    else pXY (x, y) * Real.log (pXY (x, y) / (∑ x' : α, pXY (x', y))))

/-
PROBLEM
Conditioning reduces entropy: H(X|Y) ≤ H(X)
Follows from I(X;Y) = H(X) - H(X|Y) ≥ 0.
Proof strategy: decompose MI as sum of H(X) term and H(X|Y) term,
use mutual_info_nonneg (already proved) to conclude.

PROVIDED SOLUTION
Use Gibbs' inequality / log-sum inequality. The key idea: H(X) - H(X|Y) = I(X;Y) ≥ 0 by non-negativity of mutual information (which follows from KL divergence non-negativity / log-sum inequality). Expand: H(X) = -Σ_x p(x) log p(x) where p(x) = Σ_y p(x,y), and H(X|Y) = -Σ_x Σ_y p(x,y) log(p(x,y)/p(y)) where p(y) = Σ_x p(x,y). Then H(X) - H(X|Y) = Σ_x Σ_y p(x,y) log(p(x,y)/(p(x)*p(y))) = I(X;Y). This is a KL divergence D(p(x,y) || p(x)p(y)) ≥ 0 by log-sum inequality. Alternatively, use the log-sum inequality directly on appropriate sums, or use Jensen's inequality on the concavity of log.
-/
theorem conditioning_reduces_entropy {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {pXY : α × β → ℝ} (hp : ∀ xy, 0 ≤ pXY xy)
    (hsum : ∑ xy : α × β, pXY xy = 1) :
    conditionalEntropy pXY ≤
    shannonEntropy (fun x => ∑ y : β, pXY (x, y)) := by
      -- By the definition of mutual information, we have $I(X; Y) = H(X) - H(X|Y)$.
      set I : ℝ := ∑ x : α, ∑ y : β, pXY (x, y) * Real.log (pXY (x, y) / (∑ x', pXY (x', y)) / (∑ y', pXY (x, y'))) with hI_def
      have hI_eq : I = shannonEntropy (fun x => ∑ y, pXY (x, y)) - conditionalEntropy pXY := by
        unfold shannonEntropy conditionalEntropy I; simp +decide [ Finset.sum_mul _ _ _, Finset.mul_sum ] ; ring;
        rw [ ← Finset.sum_neg_distrib ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext x ; by_cases hx : ∑ y, pXY ( x, y ) = 0 <;> simp +decide [ hx, Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ] ; ring;
        · rw [ Finset.sum_eq_zero_iff_of_nonneg ] at hx <;> aesop;
        · rw [ Finset.sum_filter ] ; rw [ ← Finset.sum_neg_distrib ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext y ; by_cases hy : pXY ( x, y ) = 0 <;> simp +decide [ hy, Real.log_mul, hx, Finset.sum_eq_zero_iff_of_nonneg, hp ] ; ring;
          rw [ Real.log_mul, Real.log_mul ] <;> ring <;> simp +decide [ *, ne_of_gt ];
          · ring;
          · exact ne_of_gt ( lt_of_lt_of_le ( lt_of_le_of_ne ( hp _ ) ( Ne.symm hy ) ) ( Finset.single_le_sum ( fun x' _ => hp ( x', y ) ) ( Finset.mem_univ x ) ) );
          · exact ne_of_gt ( lt_of_lt_of_le ( lt_of_le_of_ne ( hp _ ) ( Ne.symm hy ) ) ( Finset.single_le_sum ( fun x' _ => hp ( x', y ) ) ( Finset.mem_univ x ) ) );
      -- By the properties of the logarithm and the fact that $p(x,y) \geq 0$, we have $p(x,y) \log \frac{p(x,y)}{p(x)p(y)} \geq p(x,y) - p(x)p(y)$.
      have h_ineq : ∀ x y, pXY (x, y) * Real.log (pXY (x, y) / (∑ x', pXY (x', y)) / (∑ y', pXY (x, y'))) ≥ pXY (x, y) - (∑ x', pXY (x', y)) * (∑ y', pXY (x, y')) := by
        intro x y
        by_cases hxy : pXY (x, y) = 0;
        · simp [hxy];
          exact mul_nonneg ( Finset.sum_nonneg fun _ _ => hp _ ) ( Finset.sum_nonneg fun _ _ => hp _ );
        · have h_ineq : Real.log ((pXY (x, y) / (∑ x', pXY (x', y)) / (∑ y', pXY (x, y')))) ≥ 1 - (∑ x', pXY (x', y)) * (∑ y', pXY (x, y')) / pXY (x, y) := by
            have h_ineq : ∀ z : ℝ, 0 < z → Real.log z ≥ 1 - 1 / z := by
              exact fun z hz => by have := Real.log_le_sub_one_of_pos ( inv_pos.mpr hz ) ; norm_num at * ; linarith;
            convert h_ineq _ _ using 1;
            · grind +revert;
            · refine' div_pos ( div_pos ( lt_of_le_of_ne ( hp _ ) ( Ne.symm hxy ) ) ( lt_of_lt_of_le ( lt_of_le_of_ne ( hp _ ) ( Ne.symm hxy ) ) ( Finset.single_le_sum ( fun a _ => hp ( a, y ) ) ( Finset.mem_univ x ) ) ) ) ( lt_of_lt_of_le ( lt_of_le_of_ne ( hp _ ) ( Ne.symm hxy ) ) ( Finset.single_le_sum ( fun a _ => hp ( x, a ) ) ( Finset.mem_univ y ) ) );
          nlinarith [ hp ( x, y ), mul_div_cancel₀ ( ( ∑ x', pXY ( x', y ) ) * ∑ y', pXY ( x, y' ) ) hxy ];
      have h_sum_ineq : ∑ x : α, ∑ y : β, pXY (x, y) - ∑ x : α, ∑ y : β, (∑ x', pXY (x', y)) * (∑ y', pXY (x, y')) ≥ 0 := by
        have h_sum_ineq : ∑ x : α, ∑ y : β, (∑ x', pXY (x', y)) * (∑ y', pXY (x, y')) = (∑ x : α, ∑ y : β, pXY (x, y)) * (∑ x : α, ∑ y : β, pXY (x, y)) := by
          simp +decide only [← Finset.sum_mul, ← Finset.mul_sum _ _ _];
          rw [ Finset.sum_comm ];
        rw [ h_sum_ineq, show ∑ x : α, ∑ y : β, pXY ( x, y ) = 1 by simpa only [ ← Finset.sum_product' ] using hsum ] ; norm_num;
      linarith [ show I ≥ ∑ x, ∑ y, pXY ( x, y ) - ∑ x, ∑ y, ( ∑ x', pXY ( x', y ) ) * ∑ y', pXY ( x, y' ) by exact le_trans ( by simp +decide [ Finset.sum_sub_distrib ] ) ( Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => h_ineq x y ) ]

end InformationTheory.Aristotle