import Mathlib

/-
# Integer-series squares are detected modulo four

Lean core of `research/problems/erdos-85-wip-01/NONBACKTRACKING_INTEGRALITY_MOD4.md`
(codex-sol-1, 2026-09-08, review #1477).  For `P ∈ ℤ⟦X⟧` with constant
coefficient `1` put `R := ∑_j (p_{2j} mod 2) X^j` (`evenReduction`).  Then

  `P` is a square in `ℤ⟦X⟧`   ⟺   `P ≡ R² (mod 4)` coefficientwise.

This is the equivalence (2) ⟺ (3) of the note.  The reduction (1) ⟺ (2)
— all-length primitive-cycle integrality via the Euler expansion and the
Ihara substitution `u ↦ u/(1+su²)` — is NOT formalised here.  For a
polynomial `P` the right-hand side is a finite test on the coefficients
`0, …, deg P` (`sq_iff_modEq_four_of_polynomial`).

Scope: pure formal power-series algebra over `ℤ`.  No graph, no spectrum,
no A-REG claim.

Proof.  (⇒) If `P = H²` then modulo two `p_{2j} ≡ h_j² ≡ h_j` (only the
pair `(j,j)` of the Cauchy product survives, by the swap involution in
`ZMod 2`), hence `H = R + 2K` and `H² = R² + 4(RK + K²)`.
(⇐) Write `P = R² + 4J`.  `R` is a unit and `J(0) = 0`, so `Z := J·R⁻²`
has zero constant term, and the coefficient recursion
`w_n = z_n − ∑_{a+b=n} w_a w_b` produces an integer series `W` with
`W(0) = 0` and `W + W² = Z`.  Then `H := R(1 + 2W)` has
`H² = R²(1 + 4Z) = P`.  No Catalan numbers are needed.
-/

namespace Erdos85

open PowerSeries Finset

/-! ### The coefficient recursion `W + W² = Z` -/

/-- Coefficients of the unique `W ∈ ℤ⟦X⟧` with `W(0) = 0` and `W + W² = Z`,
where `z n` is the `n`-th coefficient of `Z` (and `z 0 = 0`). -/
def sqrtAux (z : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => z (n + 1) - ∑ p ∈ (antidiagonal (n + 1)).attach,
      if p.1.1 = 0 ∨ p.1.2 = 0 then 0 else sqrtAux z p.1.1 * sqrtAux z p.1.2
termination_by n => n
decreasing_by
  all_goals
    have := mem_antidiagonal.mp p.2
    omega

theorem sqrtAux_zero (z : ℕ → ℤ) : sqrtAux z 0 = 0 := by
  rw [sqrtAux]

theorem sqrtAux_succ (z : ℕ → ℤ) (n : ℕ) :
    sqrtAux z (n + 1) =
      z (n + 1) - ∑ p ∈ antidiagonal (n + 1), sqrtAux z p.1 * sqrtAux z p.2 := by
  rw [sqrtAux, sum_attach (antidiagonal (n + 1))
    (fun q : ℕ × ℕ => if q.1 = 0 ∨ q.2 = 0 then (0 : ℤ) else sqrtAux z q.1 * sqrtAux z q.2)]
  congr 1
  refine sum_congr rfl fun p _ => ?_
  split_ifs with h
  · rcases h with h | h <;> simp [h, sqrtAux_zero]
  · rfl

/-- `W + W² = Z` for `W := mk (sqrtAux z)`, provided `z 0 = 0`. -/
theorem mk_sqrtAux_add_sq (z : ℕ → ℤ) (hz : z 0 = 0) :
    mk (sqrtAux z) + mk (sqrtAux z) ^ 2 = mk z := by
  ext n
  rcases n with _ | n
  · simp [sq, sqrtAux_zero, hz]
  · simp only [map_add, sq, coeff_mul, coeff_mk]
    rw [sqrtAux_succ]
    ring

/-- `1 + 4Z` is the square of an integer unit series `1 + 2W` whenever `Z(0) = 0`. -/
theorem exists_one_add_two_mul_sq (Z : ℤ⟦X⟧) (hZ : constantCoeff Z = 0) :
    ∃ W : ℤ⟦X⟧, constantCoeff W = 0 ∧ (1 + 2 * W) ^ 2 = 1 + 4 * Z := by
  set W : ℤ⟦X⟧ := mk (sqrtAux fun n => coeff n Z) with hWdef
  refine ⟨W, ?_, ?_⟩
  · show sqrtAux _ 0 = 0
    exact sqrtAux_zero _
  · have h : W + W ^ 2 = Z := by
      have h := mk_sqrtAux_add_sq (fun n => coeff n Z)
        (by rw [coeff_zero_eq_constantCoeff_apply]; exact hZ)
      have hZ' : mk (fun n => coeff n Z) = Z := PowerSeries.ext fun n => coeff_mk n _
      rwa [hZ'] at h
    linear_combination 4 * h

/-! ### The even reduction `R` and the Frobenius step modulo two -/

/-- `R := ∑_j (p_{2j} mod 2) X^j`. -/
noncomputable def evenReduction (P : ℤ⟦X⟧) : ℤ⟦X⟧ := mk fun j => coeff (2 * j) P % 2

theorem coeff_evenReduction (P : ℤ⟦X⟧) (j : ℕ) :
    coeff j (evenReduction P) = coeff (2 * j) P % 2 :=
  coeff_mk _ _

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> rfl

theorem zmod2_mul_self (x : ZMod 2) : x * x = x := by
  fin_cases x <;> rfl

/-- Over `ZMod 2` the even coefficients of a square are the coefficients of
the series: `coeff (2j) (B²) = coeff j B`. -/
theorem coeff_two_mul_sq_zmod2 (B : (ZMod 2)⟦X⟧) (j : ℕ) :
    coeff (2 * j) (B ^ 2) = coeff j B := by
  rw [sq, coeff_mul]
  have hmem : ((j, j) : ℕ × ℕ) ∈ antidiagonal (2 * j) := by
    rw [mem_antidiagonal]; ring
  rw [← add_sum_erase _ _ hmem, zmod2_mul_self]
  have hzero : ∑ p ∈ (antidiagonal (2 * j)).erase (j, j), coeff p.1 B * coeff p.2 B = 0 := by
    refine sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · intro p _
      simp only [Prod.fst_swap, Prod.snd_swap]
      rw [mul_comm]
      exact zmod2_add_self _
    · intro p hp _ heq
      have h1 := mem_erase.mp hp
      have h2 := mem_antidiagonal.mp h1.2
      have h3 : p.2 = p.1 := by
        have := congrArg Prod.fst heq
        simpa using this
      exact h1.1 (Prod.ext (by show p.1 = j; omega) (by show p.2 = j; omega))
    · intro p hp
      have h1 := mem_erase.mp hp
      have h2 := mem_antidiagonal.mp h1.2
      refine mem_erase.mpr ⟨?_, ?_⟩
      · intro heq
        have ha := congrArg Prod.fst heq
        have hb := congrArg Prod.snd heq
        simp only [Prod.fst_swap, Prod.snd_swap] at ha hb
        exact h1.1 (Prod.ext hb ha)
      · rw [mem_antidiagonal, Prod.fst_swap, Prod.snd_swap]
        omega
    · intro p _
      exact Prod.swap_swap p
  rw [hzero, add_zero]

/-- Over `ℤ`: `coeff (2j) (H²) ≡ coeff j H (mod 2)`. -/
theorem coeff_two_mul_sq_modEq (H : ℤ⟦X⟧) (j : ℕ) :
    coeff (2 * j) (H ^ 2) ≡ coeff j H [ZMOD 2] := by
  have key := coeff_two_mul_sq_zmod2 (map (Int.castRingHom (ZMod 2)) H) j
  rw [← map_pow, coeff_map, coeff_map, Int.coe_castRingHom] at key
  exact (ZMod.intCast_eq_intCast_iff _ _ 2).1 key

/-! ### The two directions -/

/-- A square `P = H²` satisfies `P ≡ R² (mod 4)` coefficientwise. -/
theorem modEq_four_of_sq (H : ℤ⟦X⟧) (n : ℕ) :
    coeff n (H ^ 2) ≡ coeff n (evenReduction (H ^ 2) ^ 2) [ZMOD 4] := by
  set R := evenReduction (H ^ 2) with hR
  -- `H ≡ R (mod 2)` coefficientwise
  have hdiv : ∀ j, (2 : ℤ) ∣ coeff j H - coeff j R := by
    intro j
    rw [hR, coeff_evenReduction]
    have h1 := coeff_two_mul_sq_modEq H j
    have h2 : coeff (2 * j) (H ^ 2) % 2 ≡ coeff (2 * j) (H ^ 2) [ZMOD 2] :=
      Int.mod_modEq _ _
    exact (h2.trans h1).dvd
  -- `H = R + 2K`
  let K : ℤ⟦X⟧ := mk fun j => (coeff j H - coeff j R) / 2
  have hHK : H = R + 2 * K := by
    ext j
    rw [map_add, ← map_ofNat C 2, coeff_C_mul, coeff_mk, Int.mul_ediv_cancel' (hdiv j)]
    ring
  have hsq : H ^ 2 = R ^ 2 + 4 * (R * K + K ^ 2) := by
    rw [hHK]; ring
  rw [Int.modEq_iff_dvd]
  refine ⟨-(coeff n (R * K + K ^ 2)), ?_⟩
  conv_lhs => rw [hsq, map_add, ← map_ofNat C 4, coeff_C_mul]
  ring

/-- Conversely `P ≡ R² (mod 4)` with `P(0) = 1` makes `P` a square. -/
theorem sq_of_modEq_four (P : ℤ⟦X⟧) (hP : constantCoeff P = 1)
    (h : ∀ n, coeff n P ≡ coeff n (evenReduction P ^ 2) [ZMOD 4]) :
    ∃ H : ℤ⟦X⟧, P = H ^ 2 := by
  set R := evenReduction P with hR
  have hR0 : constantCoeff R = 1 := by
    rw [hR]
    show coeff (2 * 0) P % 2 = 1
    rw [mul_zero, coeff_zero_eq_constantCoeff_apply, hP]
    norm_num
  -- `R` is a unit
  set Rinv := invOfUnit R 1 with hRinv
  have hRR : R * Rinv = 1 := mul_invOfUnit R 1 (by rw [hR0]; rfl)
  -- `P = R² + 4J`
  let J : ℤ⟦X⟧ := mk fun n => (coeff n P - coeff n (R ^ 2)) / 4
  have hJ : P = R ^ 2 + C 4 * J := by
    ext n
    rw [map_add, coeff_C_mul, coeff_mk, Int.mul_ediv_cancel' (h n).symm.dvd]
    ring
  have hJ0 : constantCoeff J = 0 := by
    show (coeff 0 P - coeff 0 (R ^ 2)) / 4 = 0
    rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_pow, hP, hR0]
    norm_num
  -- `Z := J R⁻²` has zero constant term
  set Z := J * Rinv ^ 2 with hZ
  have hZ0 : constantCoeff Z = 0 := by
    rw [hZ, map_mul, hJ0, zero_mul]
  obtain ⟨W, -, hW⟩ := exists_one_add_two_mul_sq Z hZ0
  refine ⟨R * (1 + 2 * W), ?_⟩
  have h4 : (C (4 : ℤ) : ℤ⟦X⟧) = 4 := map_ofNat C 4
  rw [mul_pow, hW, hJ, h4, hZ]
  linear_combination (-(4 * J) * (R * Rinv + 1)) * hRR

/-- **Main theorem.**  For `P ∈ ℤ⟦X⟧` with `P(0) = 1`: `P` is a square in
`ℤ⟦X⟧` iff `P ≡ R² (mod 4)` coefficientwise, where
`R = ∑_j (p_{2j} mod 2) X^j`. -/
theorem sq_iff_modEq_four (P : ℤ⟦X⟧) (hP : constantCoeff P = 1) :
    (∃ H : ℤ⟦X⟧, P = H ^ 2) ↔
      ∀ n, coeff n P ≡ coeff n (evenReduction P ^ 2) [ZMOD 4] :=
  ⟨fun ⟨H, hH⟩ n => hH ▸ modEq_four_of_sq H n, sq_of_modEq_four P hP⟩

/-! ### Finiteness for polynomials -/

/-- Beyond the degree of a polynomial `p`, the coefficients of `R²` vanish. -/
theorem coeff_evenReduction_sq_eq_zero (p : Polynomial ℤ) {n : ℕ} (hn : p.natDegree < n) :
    coeff n (evenReduction (p : ℤ⟦X⟧) ^ 2) = 0 := by
  rw [sq, coeff_mul]
  refine sum_eq_zero fun q hq => ?_
  have hsum := mem_antidiagonal.mp hq
  rcases Nat.lt_or_ge p.natDegree (2 * q.1) with h | h
  · have : coeff q.1 (evenReduction (p : ℤ⟦X⟧)) = 0 := by
      rw [coeff_evenReduction, Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt h]
      rfl
    rw [this, zero_mul]
  · have h' : p.natDegree < 2 * q.2 := by omega
    have : coeff q.2 (evenReduction (p : ℤ⟦X⟧)) = 0 := by
      rw [coeff_evenReduction, Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt h']
      rfl
    rw [this, mul_zero]

/-- For a polynomial `p` with `p(0) = 1` the square test is the finite check of
the congruences at the coefficients `0, …, deg p`. -/
theorem sq_iff_modEq_four_of_polynomial (p : Polynomial ℤ) (hp : p.coeff 0 = 1) :
    (∃ H : ℤ⟦X⟧, (p : ℤ⟦X⟧) = H ^ 2) ↔
      ∀ n ≤ p.natDegree,
        p.coeff n ≡ coeff n (evenReduction (p : ℤ⟦X⟧) ^ 2) [ZMOD 4] := by
  have hP : constantCoeff (p : ℤ⟦X⟧) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hp]
  rw [sq_iff_modEq_four _ hP]
  constructor
  · intro h n _
    rw [← Polynomial.coeff_coe]
    exact h n
  · intro h n
    rcases Nat.lt_or_ge p.natDegree n with hn | hn
    · rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt hn,
        coeff_evenReduction_sq_eq_zero p hn]
    · rw [Polynomial.coeff_coe]
      exact h n hn

end Erdos85
