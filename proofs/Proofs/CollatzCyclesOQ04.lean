/-
# Collatz Cycles OQ-04: The Algebraic Cycle Equation

## Research Question

For a Collatz cycle with j odd steps and M total halvings, the odd elements
n₀, n₁, ..., n_{j-1} and halving counts m₀, m₁, ..., m_{j-1} must satisfy:

    ∏ᵢ (3·nᵢ + 1) = 2^M · ∏ᵢ nᵢ

where M = m₀ + m₁ + ... + m_{j-1}. This follows from the step relations
2^{mᵢ} · n_{(i+1) mod j} = 3nᵢ + 1 by taking the product over all i and using
that the cyclic shift permutes the index set. It implies:

1. **General halving constraint**: 2^M > 3^j (strict, for all j ≥ 1)
2. **No power equality**: 2^M ≠ 3^j for positive M, j (by parity)
3. **Cycle length lower bound**: Any cycle has M ≥ j + 1 total halvings

This generalizes the specific cases j=1,2,3,4 proved in CollatzCycles.lean
to a single algebraic argument valid for all j.

## References

- Lagarias, J.C. (1985). "The 3x+1 problem and its generalizations."
  American Mathematical Monthly 92(1), pp. 3–23.
- Eliahou, S. (1993). "The 3x+1 problem: new lower bounds on nontrivial cycle lengths."
  Discrete Mathematics 118(1–3), pp. 45–56.
-/

import Mathlib

namespace CollatzCyclesOQ04

open BigOperators Finset

/-! ## Part I: Collatz Cycle Configurations -/

/-- A valid Collatz cycle configuration with j odd steps.
    Encodes the cyclic step relation 2^{mᵢ} · n_{(i+1) mod j} = 3nᵢ + 1. -/
structure CycleConfig (j : ℕ) (hj : 0 < j) where
  odds     : Fin j → ℕ
  halvings : Fin j → ℕ
  all_pos  : ∀ i, 0 < odds i
  all_odd  : ∀ i, odds i % 2 = 1
  cycle_prop : ∀ i : Fin j,
    2 ^ halvings i * odds ⟨(i.val + 1) % j, Nat.mod_lt _ hj⟩ = 3 * odds i + 1

/-- Total halvings M = Σᵢ mᵢ -/
def CycleConfig.M {j : ℕ} {hj : 0 < j} (c : CycleConfig j hj) : ℕ :=
  ∑ i : Fin j, c.halvings i

/-! ## Part II: The Cyclic Successor Bijection -/

/-- The cyclic successor i ↦ (i+1) mod j as a permutation of Fin j. -/
def cyclicSucc (j : ℕ) (hj : 0 < j) : Equiv.Perm (Fin j) where
  toFun   i := ⟨(i.val + 1) % j, Nat.mod_lt _ hj⟩
  invFun  i := ⟨(i.val + j - 1) % j, Nat.mod_lt _ hj⟩
  left_inv  := by intro ⟨i, hi⟩; ext; simp only; omega
  right_inv := by intro ⟨i, hi⟩; ext; simp only; omega

/-! ## Part III: Key Product Identities -/

/-- Products over a permuted Fin j index equal the original product.
    This uses the fact that cyclic shift is a bijection on Fin j. -/
theorem prod_perm_eq {j : ℕ} (σ : Equiv.Perm (Fin j)) (f : Fin j → ℕ) :
    ∏ i, f (σ i) = ∏ i, f i :=
  Equiv.prod_comp σ f

/-- ∏ᵢ 2^{mᵢ} = 2^{∑ᵢ mᵢ}: product of powers equals power of sum. -/
theorem prod_two_pow (j : ℕ) (m : Fin j → ℕ) :
    ∏ i : Fin j, 2 ^ m i = 2 ^ ∑ i : Fin j, m i :=
  Finset.prod_pow_eq_pow_sum Finset.univ m 2

/-! ## Part IV: The Product Equation -/

/-- **Main Theorem**: For any valid Collatz cycle, ∏ᵢ (3nᵢ + 1) = 2^M · ∏ᵢ nᵢ.

    Proof: Each step gives 3nᵢ + 1 = 2^{mᵢ} · n_{σ(i)} where σ is the cyclic shift.
    Taking the product: ∏(3nᵢ+1) = ∏(2^{mᵢ} · n_{σ(i)})
                      = (∏ 2^{mᵢ}) · (∏ n_{σ(i)})    [by multiplicativity]
                      = 2^M · ∏ nᵢ                    [since σ is a bijection] -/
theorem cycle_product_equation {j : ℕ} (hj : 0 < j) (c : CycleConfig j hj) :
    ∏ i : Fin j, (3 * c.odds i + 1) = 2 ^ c.M * ∏ i : Fin j, c.odds i := by
  have step_eq : ∀ i : Fin j,
      3 * c.odds i + 1 = 2 ^ c.halvings i * c.odds ((cyclicSucc j hj) i) :=
    fun i => (c.cycle_prop i).symm
  calc ∏ i : Fin j, (3 * c.odds i + 1)
      = ∏ i : Fin j, (2 ^ c.halvings i * c.odds ((cyclicSucc j hj) i)) :=
          Finset.prod_congr rfl (fun i _ => step_eq i)
    _ = (∏ i : Fin j, 2 ^ c.halvings i) *
        (∏ i : Fin j, c.odds ((cyclicSucc j hj) i)) :=
          Finset.prod_mul_distrib
    _ = 2 ^ c.M * ∏ i : Fin j, c.odds i := by
          rw [prod_two_pow, prod_perm_eq (cyclicSucc j hj) c.odds]

/-! ## Part V: The Halving Constraint -/

/-- ∏ᵢ (3nᵢ + 1) > 3^j · ∏ᵢ nᵢ when all nᵢ ≥ 1.

    Proof by induction on j. The inductive step uses:
    (3*n₀+1) * ∏_tail_steps > (3*n₀+1) * 3^j' * ∏_tail  [by IH]
                             > (3*n₀) * 3^j' * ∏_tail      [since 3*n₀+1 > 3*n₀]
                             = 3^(j'+1) * (n₀ * ∏_tail)    ✓  -/
theorem prod_step_gt {j : ℕ} (hj : 0 < j) (n : Fin j → ℕ) (hpos : ∀ i, 0 < n i) :
    3 ^ j * ∏ i : Fin j, n i < ∏ i : Fin j, (3 * n i + 1) := by
  revert hj n hpos
  induction j with
  | zero => intro hj; exact absurd hj (Nat.lt_irrefl 0)
  | succ j' ih =>
    intro hj n hpos
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, pow_succ]
    have hpos0 : 0 < n 0 := hpos 0
    have hposR : ∀ i : Fin j', 0 < n i.succ := fun i => hpos i.succ
    rcases Nat.eq_zero_or_pos j' with rfl | hj'p
    · -- Base case: j' = 0, so Fin 0 products are 1
      simp [Fin.prod_univ_zero]; omega
    · -- Inductive step: apply IH to the tail
      have ih' := ih hj'p (fun i => n i.succ) hposR
      -- Let P = ∏_tail, Q = ∏_tail_steps, r = 3^j'
      -- ih': r * P < Q
      -- Goal: r * 3 * (n 0 * P) < (3 * n 0 + 1) * Q
      have hP  : 0 < ∏ i : Fin j', n i.succ :=
        Finset.prod_pos (fun i _ => hposR i)
      have hQ  : 0 < ∏ i : Fin j', (3 * n i.succ + 1) :=
        Finset.prod_pos (fun i _ => by linarith [hposR i])
      -- Clean calc proof:
      --   r*3*(n0*P) = 3*n0*(r*P) < 3*n0*Q ≤ (3*n0+1)*Q
      calc 3 ^ j' * 3 * (n 0 * ∏ i : Fin j', n i.succ)
          = 3 * n 0 * (3 ^ j' * ∏ i : Fin j', n i.succ) := by ring
        _ < 3 * n 0 * ∏ i : Fin j', (3 * n i.succ + 1) :=
              mul_lt_mul_of_pos_left ih' (by linarith)
        _ ≤ (3 * n 0 + 1) * ∏ i : Fin j', (3 * n i.succ + 1) :=
              Nat.mul_le_mul_right _ (by omega)

/-- **General Halving Constraint**: For any Collatz cycle, 3^j < 2^M.

    Proof: From ∏(3nᵢ+1) > 3^j·∏nᵢ and ∏(3nᵢ+1) = 2^M·∏nᵢ,
    we get 2^M·∏nᵢ > 3^j·∏nᵢ; cancelling ∏nᵢ > 0 gives 2^M > 3^j. -/
theorem halving_constraint {j : ℕ} (hj : 0 < j) (c : CycleConfig j hj) :
    3 ^ j < 2 ^ c.M := by
  have hprod_eq   := cycle_product_equation hj c
  have hprod_ineq := prod_step_gt hj c.odds c.all_pos
  rw [hprod_eq] at hprod_ineq
  exact lt_of_mul_lt_mul_right hprod_ineq (Nat.zero_le _)

/-! ## Part VI: No Power Equality -/

/-- 3^j is always odd: 3^j ≡ 1 (mod 2). -/
theorem odd_three_pow (j : ℕ) : 3 ^ j % 2 = 1 := by
  induction j with
  | zero => simp
  | succ j' ih => simp [pow_succ, Nat.mul_mod, ih]

/-- **No Power Equality**: 2^M ≠ 3^j for M ≥ 1.
    Proof: 2^M ≡ 0 (mod 2) but 3^j ≡ 1 (mod 2). -/
theorem no_power_eq {M j : ℕ} (hM : 0 < M) : 2 ^ M ≠ 3 ^ j := by
  intro h
  have heven : 2 ^ M % 2 = 0 := by
    have : 2 ∣ 2 ^ M := dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hM)
    omega
  have hodd := odd_three_pow j
  omega

/-! ## Part VII: Minimum Cycle Length -/

/-- For j ≥ 1: 2^j < 3^j. -/
theorem two_pow_lt_three_pow {j : ℕ} (hj : 0 < j) : 2 ^ j < 3 ^ j :=
  Nat.pow_lt_pow_left (by norm_num) hj

/-- For any Collatz cycle with j odd steps and M halvings, M ≥ j + 1.
    Proof: 2^M > 3^j > 2^j (for j ≥ 1), so M > j by monotonicity of 2^·. -/
theorem cycle_M_gt_j {j : ℕ} (hj : 0 < j) (c : CycleConfig j hj) : c.M ≥ j + 1 := by
  have hconstr := halving_constraint hj c
  have h2j     := two_pow_lt_three_pow hj
  -- 2^M > 3^j > 2^j, so M > j
  have hM_gt   : 2 ^ c.M > 2 ^ j := by linarith
  -- Contrapositive: if M ≤ j then 2^M ≤ 2^j
  by_contra hlt; push_neg at hlt
  exact absurd hM_gt (not_lt.mpr (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-! ## Part VIII: Connection to CollatzCycles.lean (OQ-02)

The general `halving_constraint` subsumes the j=1,2,3,4 cases from CollatzCycles.lean. -/

/-- For j=1: any Collatz cycle needs M ≥ 2 halvings. -/
theorem min_halvings_j1 {j : ℕ} (hj : 0 < j) (c : CycleConfig j hj)
    (hj1 : j = 1) : c.M ≥ 2 := by
  subst hj1; have h := halving_constraint hj c; simp at h
  by_contra hlt; push_neg at hlt; interval_cases c.M <;> omega

/-- For j=2: any Collatz cycle needs M ≥ 4 halvings. -/
theorem min_halvings_j2 {j : ℕ} (hj : 0 < j) (c : CycleConfig j hj)
    (hj2 : j = 2) : c.M ≥ 4 := by
  subst hj2; have h := halving_constraint hj c; norm_num at h
  by_contra hlt; push_neg at hlt; interval_cases c.M <;> omega

/-- For j=3: any Collatz cycle needs M ≥ 5 halvings. -/
theorem min_halvings_j3 {j : ℕ} (hj : 0 < j) (c : CycleConfig j hj)
    (hj3 : j = 3) : c.M ≥ 5 := by
  subst hj3; have h := halving_constraint hj c; norm_num at h
  by_contra hlt; push_neg at hlt; interval_cases c.M <;> omega

/-- For j=4: any Collatz cycle needs M ≥ 7 halvings. -/
theorem min_halvings_j4 {j : ℕ} (hj : 0 < j) (c : CycleConfig j hj)
    (hj4 : j = 4) : c.M ≥ 7 := by
  subst hj4; have h := halving_constraint hj c; norm_num at h
  by_contra hlt; push_neg at hlt; interval_cases c.M <;> omega

end CollatzCyclesOQ04
