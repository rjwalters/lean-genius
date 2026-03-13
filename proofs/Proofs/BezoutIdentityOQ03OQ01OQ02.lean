import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic

/-
# Non-Coprime CRT: Image Characterization (bezout-identity-oq-03-oq-01-oq-02)

## Problem
When gcd(m,n) = d > 1, the natural map ℤ → ℤ/mℤ × ℤ/nℤ (sending x to (x mod m, x mod n))
is no longer surjective. Characterize the image.

## Key Results
1. **Solvability**: x ≡ a (mod m) ∧ x ≡ b (mod n) has a solution iff d | (a - b)
2. **Image characterization**: Im = {(a,b) ∈ ℤ/mℤ × ℤ/nℤ | a ≡ b (mod d)}
3. **Uniqueness**: Solutions are unique modulo lcm(m,n)

## Status
- All theorems proved (0 sorries)
-/

namespace NonCoprimeCRT

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: SOLVABILITY CONDITION
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Forward direction**: If x ≡ a (mod m) and x ≡ b (mod n), then gcd(m,n) | (a - b). -/
theorem solvable_implies_gcd_dvd (m n a b x : ℤ)
    (hm : x ≡ a [ZMOD m]) (hn : x ≡ b [ZMOD n]) :
    (Int.gcd m n : ℤ) ∣ (a - b) := by
  -- x ≡ a [ZMOD m] means m ∣ (a - x) by Int.modEq_iff_dvd
  have h1 : m ∣ (a - x) := Int.modEq_iff_dvd.mp hm
  have h2 : n ∣ (b - x) := Int.modEq_iff_dvd.mp hn
  have hab : a - b = (a - x) - (b - x) := by ring
  rw [hab]
  exact dvd_sub (dvd_trans (Int.gcd_dvd_left m n) h1) (dvd_trans (Int.gcd_dvd_right m n) h2)

/-- **Backward direction**: If gcd(m,n) | (a - b), then the system is solvable. -/
theorem gcd_dvd_implies_solvable (m n a b : ℤ)
    (h : (Int.gcd m n : ℤ) ∣ (a - b)) :
    ∃ x : ℤ, x ≡ a [ZMOD m] ∧ x ≡ b [ZMOD n] := by
  have hbez : (Int.gcd m n : ℤ) = m * Int.gcdA m n + n * Int.gcdB m n :=
    Int.gcd_eq_gcd_ab m n
  obtain ⟨k, hk⟩ := h
  -- Solution: x = a - m * gcdA * k
  refine ⟨a - m * Int.gcdA m n * k, ?_, ?_⟩
  · -- x ≡ a (mod m): need m ∣ (a - x) = m * gcdA * k
    rw [Int.modEq_iff_dvd]
    exact ⟨Int.gcdA m n * k, by ring⟩
  · -- x ≡ b (mod n): need n ∣ (b - x) = b - a + m * gcdA * k
    rw [Int.modEq_iff_dvd]
    exact ⟨-(Int.gcdB m n * k), by linear_combination -hk - k * hbez⟩

/-- **Generalized CRT (Solvability Criterion)**: solvable iff gcd(m,n) | (a - b). -/
theorem generalized_crt_iff (m n a b : ℤ) :
    (∃ x : ℤ, x ≡ a [ZMOD m] ∧ x ≡ b [ZMOD n]) ↔
    (Int.gcd m n : ℤ) ∣ (a - b) :=
  ⟨fun ⟨x, hm, hn⟩ => solvable_implies_gcd_dvd m n a b x hm hn,
   gcd_dvd_implies_solvable m n a b⟩

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: UNIQUENESS MODULO LCM
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Uniqueness modulo lcm**: If x ≡ y (mod m) and x ≡ y (mod n),
    then x ≡ y (mod lcm(m,n)). -/
theorem crt_unique_mod_lcm (m n x y : ℤ)
    (hm : x ≡ y [ZMOD m]) (hn : x ≡ y [ZMOD n]) :
    x ≡ y [ZMOD Int.lcm m n] := by
  rw [Int.modEq_iff_dvd] at *
  -- Go through natAbs: m.natAbs | (y-x).natAbs, n.natAbs | (y-x).natAbs
  have hm' : m.natAbs ∣ (y - x).natAbs := Int.natAbs_dvd_natAbs.mpr hm
  have hn' : n.natAbs ∣ (y - x).natAbs := Int.natAbs_dvd_natAbs.mpr hn
  have hlcm : Int.lcm m n ∣ (y - x).natAbs := Nat.lcm_dvd hm' hn'
  -- Convert back: (k : ℕ) ∣ z.natAbs → ↑k ∣ z
  obtain ⟨c, hc⟩ := hlcm
  have hc' : (↑((y - x).natAbs) : ℤ) = ↑(Int.lcm m n) * ↑c := by exact_mod_cast hc
  cases Int.natAbs_eq (y - x) with
  | inl h => exact ⟨↑c, by linarith⟩
  | inr h => exact ⟨-(↑c : ℤ), by linarith⟩

/-- **Uniqueness**: Two solutions to the same system are congruent mod lcm. -/
theorem crt_unique_iff_lcm (m n x y a b : ℤ)
    (hxa : x ≡ a [ZMOD m]) (hxb : x ≡ b [ZMOD n])
    (hya : y ≡ a [ZMOD m]) (hyb : y ≡ b [ZMOD n]) :
    x ≡ y [ZMOD Int.lcm m n] :=
  crt_unique_mod_lcm m n x y (hxa.trans hya.symm) (hxb.trans hyb.symm)

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: RELATIONSHIP BETWEEN mn, lcm, AND gcd
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Fundamental identity**: m * n = gcd(m,n) * lcm(m,n). -/
theorem gcd_mul_lcm_eq (m n : ℕ) :
    m * n = Nat.gcd m n * Nat.lcm m n :=
  (Nat.gcd_mul_lcm m n).symm

/-- In the coprime case, lcm(m,n) = m*n. -/
theorem coprime_lcm_eq_mul (m n : ℕ) (h : Nat.Coprime m n) :
    Nat.lcm m n = m * n := by
  simp [Nat.lcm, h.gcd_eq_one]

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: EXPLICIT SOLUTION FORMULA
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Explicit solution for the generalized CRT. -/
def genCRTSolution (m n a b : ℤ) : ℤ :=
  a - m * Int.gcdA m n * ((a - b) / (Int.gcd m n : ℤ))

/-- The explicit solution satisfies the first congruence (unconditionally). -/
theorem genCRT_mod_left (m n a b : ℤ) :
    genCRTSolution m n a b ≡ a [ZMOD m] := by
  unfold genCRTSolution
  rw [Int.modEq_iff_dvd]
  exact ⟨Int.gcdA m n * ((a - b) / (Int.gcd m n : ℤ)), by ring⟩

/-- The explicit solution satisfies the second congruence when d | (a - b). -/
theorem genCRT_mod_right (m n a b : ℤ)
    (h : (Int.gcd m n : ℤ) ∣ (a - b)) :
    genCRTSolution m n a b ≡ b [ZMOD n] := by
  unfold genCRTSolution
  rw [Int.modEq_iff_dvd]
  set k := (a - b) / (Int.gcd m n : ℤ)
  have hbez : (Int.gcd m n : ℤ) = m * Int.gcdA m n + n * Int.gcdB m n :=
    Int.gcd_eq_gcd_ab m n
  have hk_val : a - b = k * (Int.gcd m n : ℤ) :=
    (Int.ediv_mul_cancel h).symm
  -- Need: n ∣ (b - (a - m * gcdA * k))
  -- = b - a + m * gcdA * k = -(a - b) + m * gcdA * k
  -- = -(d * k) + m * gcdA * k = k * (m * gcdA - d) = k * (-n * gcdB) = -n * gcdB * k
  exact ⟨-(Int.gcdB m n * k), by linear_combination -hk_val - k * hbez⟩

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: SPECIAL CASES AND EXAMPLES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- When coprime, any system is solvable (standard CRT). -/
theorem coprime_always_solvable (m n a b : ℤ) (h : Int.gcd m n = 1) :
    ∃ x : ℤ, x ≡ a [ZMOD m] ∧ x ≡ b [ZMOD n] := by
  apply gcd_dvd_implies_solvable
  rw [h]
  exact one_dvd _

section ConcreteExamples

/-- Example: x ≡ 1 (mod 4), x ≡ 3 (mod 6). gcd(4,6)=2, 2|(-2). Solvable, x=9. -/
example : (9 : ℤ) ≡ 1 [ZMOD 4] := by decide
example : (9 : ℤ) ≡ 3 [ZMOD 6] := by decide
example : Int.gcd 4 6 = 2 := by native_decide
example : (2 : ℤ) ∣ (1 - 3) := ⟨-1, by norm_num⟩

/-- Example: x ≡ 1 (mod 4), x ≡ 2 (mod 6). gcd(4,6)=2, 2∤(-1). UNSOLVABLE. -/
example : ¬ (2 : ℤ) ∣ (1 - 2) := by omega

/-- Example: x ≡ 0 (mod 6), x ≡ 3 (mod 9). gcd(6,9)=3, 3|(-3). Solvable, x=12. -/
example : (12 : ℤ) ≡ 0 [ZMOD 6] := by decide
example : (12 : ℤ) ≡ 3 [ZMOD 9] := by decide

/-- Uniqueness mod lcm(6,9)=18: both 12 and 30 work. -/
example : (30 : ℤ) ≡ 0 [ZMOD 6] := by decide
example : (30 : ℤ) ≡ 3 [ZMOD 9] := by decide
example : (30 : ℤ) ≡ 12 [ZMOD 18] := by decide

end ConcreteExamples

/-
═══════════════════════════════════════════════════════════════════════════════
PART VI: THE GENERALIZED CRT AS A COMPLETE CHARACTERIZATION
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Complete characterization (ModEq form)**:
    solvable iff a ≡ b (mod gcd(m,n)). -/
theorem generalized_crt_modEq (m n a b : ℤ) :
    (∃ x : ℤ, x ≡ a [ZMOD m] ∧ x ≡ b [ZMOD n]) ↔
    a ≡ b [ZMOD Int.gcd m n] := by
  rw [generalized_crt_iff]
  constructor
  · intro h
    rw [Int.modEq_iff_dvd]
    obtain ⟨k, hk⟩ := h
    exact ⟨-k, by linarith⟩
  · intro h
    rw [Int.modEq_iff_dvd] at h
    obtain ⟨k, hk⟩ := h
    exact ⟨-k, by linarith⟩

/-- **Full generalized CRT**: existence + uniqueness. -/
theorem generalized_crt_full (m n a b : ℤ)
    (h : a ≡ b [ZMOD Int.gcd m n]) :
    ∃ x : ℤ, (x ≡ a [ZMOD m] ∧ x ≡ b [ZMOD n]) ∧
    ∀ y : ℤ, (y ≡ a [ZMOD m] ∧ y ≡ b [ZMOD n]) → x ≡ y [ZMOD Int.lcm m n] := by
  obtain ⟨x, hxa, hxb⟩ := (generalized_crt_modEq m n a b).mpr h
  exact ⟨x, ⟨hxa, hxb⟩, fun y ⟨hya, hyb⟩ =>
    crt_unique_mod_lcm m n x y (hxa.trans hya.symm) (hxb.trans hyb.symm)⟩

/-
═══════════════════════════════════════════════════════════════════════════════
SUMMARY

The non-coprime CRT says:
1. SOLVABILITY: x ≡ a (mod m), x ≡ b (mod n) solvable ⟺ gcd(m,n) | (a-b)
2. UNIQUENESS: solutions are unique mod lcm(m,n)
3. FORMULA: x = a - m·gcdA(m,n)·((a-b)/gcd(m,n))
4. REDUCTION: when gcd(m,n) = 1, recovers standard CRT
═══════════════════════════════════════════════════════════════════════════════ -/

#check @solvable_implies_gcd_dvd
#check @gcd_dvd_implies_solvable
#check @generalized_crt_iff
#check @crt_unique_mod_lcm
#check @crt_unique_iff_lcm
#check @gcd_mul_lcm_eq
#check @coprime_lcm_eq_mul
#check @genCRTSolution
#check @genCRT_mod_left
#check @genCRT_mod_right
#check @coprime_always_solvable
#check @generalized_crt_modEq
#check @generalized_crt_full

end NonCoprimeCRT
