/-
  Dehn Invariants for Platonic Solids: Cube Isolation (OQ-04)

  Source: Dehn (1900), Sydler (1965), Jessen (1968), Niven (1956)
  Tags: geometry, dissection, dehn-invariant, hilbert-3, impossible

  Proves that among the five Platonic solids, ONLY the cube has zero
  Dehn invariant. Hence the cube is isolated in its scissors-congruence
  class from all other Platonic solids.

  ## Key New Result (arccos(1/√5)/π is irrational)

  Proved via a Chebyshev integer sequence argument analogous to the
  Niven theorem used in OQ-02 for arccos(1/3)/π.

  Define d_n with d_0 = 2, d_1 = 6, d_{n+2} = 6·d_{n+1} - 25·d_n.
  Then d_n = 5^n · 2cos(n · arccos(3/5)), and 5 ∤ d_n for all n.
  If arccos(3/5)/π = p/q, then d_q = ±2 · 5^q, so 5 | d_q.
  Contradiction. Hence arccos(3/5)/π is irrational.

  The dodecahedron dihedral angle arccos(-1/√5) = π - arccos(1/√5),
  and 2·arccos(1/√5) = π - arccos(3/5), so irrationality propagates.

  ## Axiom Budget

  0 axioms (fully proved):
  - `tmul_infinite_order_ne_zero` (OQ02OQ02): PROVED via ℝ flat over ℤ (Bézout + torsion-free)
  - `icoAngle_irrational`: PROVED via Chebyshev sequence for arccos(1/9)

  ## Classification Table (among Platonic solids)

  | Solid         | Edges | Dihedral Angle       | D = 0? |
  |---------------|-------|----------------------|--------|
  | Cube          | 12    | π/2                  | YES    |
  | Tetrahedron   | 6     | arccos(1/3)          | No     |
  | Octahedron    | 12    | arccos(-1/3) = π-tet | No     |
  | Dodecahedron  | 30    | arccos(-1/√5)        | No     |
  | Icosahedron   | 30    | arccos(-√5/3)        | No     |

  Extends: DissectionOfCubesOQ02OQ02.lean (Dehn invariant infrastructure)
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Proofs.DissectionOfCubesOQ02
import Proofs.DissectionOfCubesOQ02OQ02

namespace DissectionOfCubesOQ04

open Real DissectionOfCubesOQ02 DehnSydler

-- ============================================================
-- PART I: Integer Sequence for arccos(3/5)/π Irrationality
-- ============================================================

/-
### The Key Sequence

For cos θ = 3/5, define: d_n = 5^n · 2cos(n·θ).

Recurrence: d_{n+2} = 5^{n+2} · (2cosθ · 2cos((n+1)θ) - 2cos(nθ))
           = 5^{n+2} · (6/5 · 2cos((n+1)θ) - 2cos(nθ))
           = 6 · d_{n+1} - 25 · d_n.

Base: d_0 = 2, d_1 = 5 · (2 · 3/5) = 6.
-/

/-- Integer sequence for arccos(3/5)/π irrationality.
    d_0 = 2, d_1 = 6, d_{n+2} = 6·d_{n+1} − 25·d_n.
    Key: d_n = 5^n · 2cos(n · arccos(3/5)). -/
def cosThreeFifthsSeq : ℕ → ℤ
  | 0     => 2
  | 1     => 6
  | (n+2) => 6 * cosThreeFifthsSeq (n+1) - 25 * cosThreeFifthsSeq n

@[simp] theorem cosThreeFifthsSeq_zero : cosThreeFifthsSeq 0 = 2 := rfl
@[simp] theorem cosThreeFifthsSeq_one  : cosThreeFifthsSeq 1 = 6 := rfl
theorem cosThreeFifthsSeq_succ (n : ℕ) :
    cosThreeFifthsSeq (n+2) = 6 * cosThreeFifthsSeq (n+1) - 25 * cosThreeFifthsSeq n := rfl

/-- 5 does not divide cosThreeFifthsSeq k for any k.

Proof: d_{n+2} = 6·d_{n+1} - 25·d_n ≡ d_{n+1} (mod 5) since 6 ≡ 1
and 25 ≡ 0 (mod 5). So if 5 ∤ d_{n+1}, then 5 ∤ d_{n+2}.
Base: d_0 = 2, d_1 = 6 — neither divisible by 5. -/
theorem five_ndvd_cosThreeFifthsSeq : ∀ k : ℕ, ¬((5 : ℤ) ∣ cosThreeFifthsSeq k) := by
  suffices h : ∀ k : ℕ,
      ¬((5 : ℤ) ∣ cosThreeFifthsSeq k) ∧ ¬((5 : ℤ) ∣ cosThreeFifthsSeq (k+1)) from
    fun k => (h k).1
  intro k
  induction k with
  | zero => exact ⟨by norm_num [cosThreeFifthsSeq], by norm_num [cosThreeFifthsSeq]⟩
  | succ n ih =>
    constructor
    · exact ih.2
    · rw [cosThreeFifthsSeq_succ]
      intro h
      obtain ⟨c, hc⟩ := h
      -- 5 | 6·d_{n+1} - 25·d_n, and 5 | 25·d_n, so 5 | 6·d_{n+1}
      have h6dvd : (5 : ℤ) ∣ 6 * cosThreeFifthsSeq (n+1) :=
        ⟨c + 25 * cosThreeFifthsSeq n, by omega⟩
      have hprime : Prime (5 : ℤ) := by norm_num
      rcases hprime.dvd_or_dvd h6dvd with h56 | h5n
      · exact absurd h56 (by norm_num)
      · exact ih.2 h5n

/-- Key relation: d_n = 5^n · 2cos(n · arccos(3/5)).

This is the arithmetic backbone of the irrationality proof. -/
theorem cosThreeFifthsSeq_eq_cos (k : ℕ) :
    (cosThreeFifthsSeq k : ℝ) =
    (5 : ℝ)^k * (2 * Real.cos (↑k * Real.arccos (3/5))) := by
  suffices h : ∀ n : ℕ,
    (cosThreeFifthsSeq n : ℝ) =
      (5 : ℝ)^n * (2 * Real.cos (↑n * Real.arccos (3/5))) ∧
    (cosThreeFifthsSeq (n+1) : ℝ) =
      (5 : ℝ)^(n+1) * (2 * Real.cos (↑(n+1) * Real.arccos (3/5)))
    from (h k).1
  intro n
  induction n with
  | zero =>
    refine ⟨by simp [cosThreeFifthsSeq, Real.cos_zero], ?_⟩
    simp only [cosThreeFifthsSeq_one, Nat.cast_one, pow_one, one_mul]
    rw [Real.cos_arccos (by norm_num : (-1:ℝ) ≤ 3/5) (by norm_num : (3/5:ℝ) ≤ 1)]
    norm_num
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    have hrec : (cosThreeFifthsSeq (m+2) : ℝ) =
        6 * (cosThreeFifthsSeq (m+1) : ℝ) - 25 * (cosThreeFifthsSeq m : ℝ) := by
      simp only [cosThreeFifthsSeq_succ]; push_cast; ring
    rw [hrec, ih.2, ih.1, cos_step,
        Real.cos_arccos (by norm_num : (-1:ℝ) ≤ 3/5) (by norm_num : (3/5:ℝ) ≤ 1)]
    push_cast; ring

/-- arccos(3/5)/π is irrational.

Proof: If arccos(3/5)/π = p/q ∈ ℚ, then d_q = ±2 · 5^q (from the
cosine relation and cos(q·arccos(3/5)) = cos(pπ) = ±1). So 5 | d_q
(since q ≥ 1). But 5 ∤ d_n for all n. Contradiction. -/
theorem arccos_three_fifths_irrational :
    ¬∃ q : ℚ, Real.arccos (3/5 : ℝ) = q * Real.pi := by
  intro ⟨q, hq⟩
  have hb_pos : 0 < q.den := q.pos
  have hmul : (q.den : ℝ) * Real.arccos (3/5) = (q.num : ℝ) * Real.pi := by
    rw [hq]; push_cast; rw [Rat.cast_def]; field_simp
  have hcos_eq : Real.cos ((↑q.den : ℝ) * Real.arccos (3/5)) =
      (-1 : ℝ)^q.num.natAbs := by
    have : (↑q.den : ℝ) * Real.arccos (3/5) = (↑q.num : ℝ) * Real.pi := hmul
    rw [this]; exact cos_int_mul_pi q.num
  have hseq := cosThreeFifthsSeq_eq_cos q.den
  rw [hcos_eq] at hseq
  have hden_ne : q.den ≠ 0 := hb_pos.ne'
  have hpm : (-1 : ℝ)^q.num.natAbs = 1 ∨ (-1 : ℝ)^q.num.natAbs = -1 := by
    induction q.num.natAbs with
    | zero => left; simp
    | succ k ih =>
      rcases ih with h | h
      · right; rw [pow_succ, h]; ring
      · left; rw [pow_succ, h]; ring
  rcases hpm with h1 | h1
  · rw [h1] at hseq
    have hval : cosThreeFifthsSeq q.den = 2 * (5 : ℤ)^q.den := by
      have h : (cosThreeFifthsSeq q.den : ℝ) = ↑(2 * (5 : ℤ)^q.den) := by
        rw [hseq]; push_cast; ring
      exact_mod_cast h
    exact five_ndvd_cosThreeFifthsSeq q.den
      (hval ▸ dvd_mul_of_dvd_right (dvd_pow_self 5 hden_ne) 2)
  · rw [h1] at hseq
    have hval : cosThreeFifthsSeq q.den = -2 * (5 : ℤ)^q.den := by
      have h : (cosThreeFifthsSeq q.den : ℝ) = ↑(-2 * (5 : ℤ)^q.den) := by
        rw [hseq]; push_cast; ring
      exact_mod_cast h
    exact five_ndvd_cosThreeFifthsSeq q.den
      (hval ▸ dvd_mul_of_dvd_right (dvd_pow_self 5 hden_ne) (-2))

-- ============================================================
-- PART II: Dodecahedron Dihedral Angle Irrationality
-- ============================================================

/-
### Chain of Irrationality

arccos(3/5)/π irrational
  → arccos(-3/5)/π irrational   [arccos(-x) = π - arccos(x)]
  → arccos(1/√5)/π irrational   [2·arccos(1/√5) = arccos(-3/5)]
  → arccos(-1/√5)/π irrational  [arccos(-x) = π - arccos(x)]

The key geometric identity: 2·arccos(1/√5) = arccos(-3/5).
Proof: cos(2·arccos(1/√5)) = 2·(1/√5)² - 1 = 2/5 - 1 = -3/5.
-/

/-- The regular dodecahedron's dihedral angle.
    (12 pentagonal faces, 30 edges, dihedral angle ≈ 116.57°) -/
noncomputable def dodAngle : ℝ := Real.arccos (-1/Real.sqrt 5)

/-- Helper: 1/√5 is in [0, 1]. -/
private lemma one_div_sqrt5_nonneg : (0 : ℝ) ≤ 1/Real.sqrt 5 := by positivity

private lemma one_div_sqrt5_le_one : (1 : ℝ)/Real.sqrt 5 ≤ 1 := by
  rw [div_le_one (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5))]
  exact Real.one_le_sqrt.mpr (by norm_num)

/-- 2·arccos(1/√5) = arccos(-3/5): the half-angle identity.

Proof: Both sides are in [0, π] (arccos(1/√5) ≤ π/2 since 1/√5 ≥ 0,
so 2·arccos(1/√5) ≤ π). And cos(2·arccos(1/√5)) = 2/5 - 1 = -3/5. -/
theorem two_arccos_sqrt5_eq : 2 * Real.arccos (1/Real.sqrt 5) = Real.arccos (-3/5) := by
  rw [← Real.arccos_cos]
  · congr 1
    rw [Real.cos_two_mul,
        Real.cos_arccos (by linarith [one_div_sqrt5_nonneg] : (-1:ℝ) ≤ 1/Real.sqrt 5)
                        one_div_sqrt5_le_one]
    have hsq : Real.sqrt 5 * Real.sqrt 5 = 5 :=
      Real.mul_self_sqrt (by norm_num : (5:ℝ) ≥ 0)
    field_simp
    nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 5 by norm_num)]
  · have := Real.arccos_nonneg (1/Real.sqrt 5)
    linarith
  · have h_le : Real.arccos (1/Real.sqrt 5) ≤ Real.pi / 2 := by
      rwa [Real.arccos_le_pi_div_two]
    linarith

/-- arccos(1/√5)/π is irrational.

Derived from arccos(3/5)/π irrationality via:
2·arccos(1/√5) = arccos(-3/5) = π - arccos(3/5). -/
theorem arccos_sqrt5_irrational :
    ¬∃ q : ℚ, Real.arccos (1/Real.sqrt 5) = q * Real.pi := by
  intro ⟨q, hq⟩
  -- 2·arccos(1/√5) = π - arccos(3/5)
  have h2eq : 2 * Real.arccos (1/Real.sqrt 5) = Real.pi - Real.arccos (3/5) := by
    rw [two_arccos_sqrt5_eq, Real.arccos_neg]
  -- So arccos(3/5) = π - 2q·π = (1 - 2q)·π ∈ π·ℚ
  apply arccos_three_fifths_irrational
  exact ⟨1 - 2 * q, by linarith [h2eq.symm.trans (by rw [hq]; push_cast; ring)]⟩

/-- arccos(-1/√5)/π is irrational. -/
theorem dodAngle_irrational : ¬∃ q : ℚ, dodAngle = q * Real.pi := by
  intro ⟨q, hq⟩
  -- dodAngle = arccos(-1/√5) = π - arccos(1/√5)
  have hneg : dodAngle = Real.pi - Real.arccos (1/Real.sqrt 5) := by
    unfold dodAngle
    rw [show (-1 : ℝ)/Real.sqrt 5 = -(1/Real.sqrt 5) by ring, Real.arccos_neg]
  apply arccos_sqrt5_irrational
  exact ⟨1 - q, by linarith [hneg ▸ hq]⟩

-- ============================================================
-- PART III: Dodecahedron Has Nonzero Dehn Invariant
-- ============================================================

/-- [dodAngle] has infinite order in ℝ/πℤ. -/
theorem dodAngle_infinite_order :
    ∀ n : ℤ, n ≠ 0 → n • angleClass dodAngle ≠ 0 := by
  intro n hn hzero
  apply dodAngle_irrational
  rw [zsmul_eq_zero_iff] at hzero
  obtain ⟨m, hm⟩ := hzero
  have hn_ne : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  exact ⟨(m : ℚ) / (n : ℚ), by push_cast; field_simp; linarith⟩

/-- **The regular dodecahedron has nonzero Dehn invariant.**

A regular dodecahedron has 30 edges, all with dihedral angle arccos(-1/√5).
Since arccos(-1/√5)/π is irrational (proved above), the angle class
[arccos(-1/√5)] has infinite order in ℝ/πℤ. By the flatness axiom
(ℝ flat over ℤ), the edge term 30a ⊗ [arccos(-1/√5)] ≠ 0. -/
theorem dod_dehn_ne_zero (a : ℝ) (ha : a > 0) :
    edgeTerm (30 * a) dodAngle ≠ 0 := by
  unfold edgeTerm
  apply tmul_infinite_order_ne_zero
  · linarith
  · exact dodAngle_infinite_order

-- ============================================================
-- PART IV: Icosahedron
-- ============================================================

/-
The regular icosahedron has 20 triangular faces, 12 vertices, 30 edges.
Its dihedral angle is arccos(-√5/3) ≈ 138.19°.

Irrationality of arccos(-√5/3)/π proved via coupled Chebyshev sequences over ℤ[√5].
Define f_n = 3^n · 2cos(n·θ) where θ = icoAngle and 3·2cos(θ) = -2√5.
The recurrence f_{n+2} = -2√5·f_{n+1} - 9·f_n decomposes as:
  A_{n+2} = -10·B_{n+1} - 9·A_n
  B_{n+2} =  -2·A_{n+1} - 9·B_n
Mod-3: 3∤A_{2k} and 3∤B_{2k+1}. If θ/π = p/q ∈ ℚ, A_q + B_q·√5 = ±2·3^q.
Since √5 is irrational, B_q = 0, so 3|A_q — contradicting mod-3.
-/

/-- The regular icosahedron's dihedral angle.
    (20 triangular faces, 30 edges, dihedral angle ≈ 138.19°) -/
noncomputable def icoAngle : ℝ := Real.arccos (-Real.sqrt 5 / 3)

-- ============================================================
-- PART IV-B: Coupled integer sequences for icoAngle irrationality
-- ============================================================

/-- Coupled integer sequence: f_n = 3^n · 2cos(n·icoAngle) = A_n + B_n·√5.
    Recurrence (from 3·2cos(icoAngle) = -2√5):
      A_{n+2} = -10·B_{n+1} - 9·A_n
      B_{n+2} =  -2·A_{n+1} - 9·B_n -/
def icoSeqAB : ℕ → ℤ × ℤ
  | 0     => (2, 0)
  | 1     => (0, -2)
  | (n+2) => (-10 * (icoSeqAB (n+1)).2 - 9 * (icoSeqAB n).1,
              -2  * (icoSeqAB (n+1)).1 - 9 * (icoSeqAB n).2)

@[simp] theorem icoSeqAB_zero : icoSeqAB 0 = (2, 0)  := rfl
@[simp] theorem icoSeqAB_one  : icoSeqAB 1 = (0, -2) := rfl
theorem icoSeqAB_succ (n : ℕ) :
    icoSeqAB (n + 2) =
      (-10 * (icoSeqAB (n+1)).2 - 9 * (icoSeqAB n).1,
       -2  * (icoSeqAB (n+1)).1 - 9 * (icoSeqAB n).2) := rfl

/-- Mod-3 invariant: ¬3∣A_{2m} and ¬3∣B_{2m+1} for all m. -/
theorem icoSeqAB_ndvd : ∀ m : ℕ,
    ¬(3 : ℤ) ∣ (icoSeqAB (2*m)).1 ∧ ¬(3 : ℤ) ∣ (icoSeqAB (2*m+1)).2 := by
  intro m
  induction m with
  | zero => exact ⟨by norm_num [icoSeqAB_zero], by norm_num [icoSeqAB_one]⟩
  | succ k ih =>
    obtain ⟨hA, hB⟩ := ih
    have hA2 : (icoSeqAB (2*k+2)).1 =
        -10 * (icoSeqAB (2*k+1)).2 - 9 * (icoSeqAB (2*k)).1 := by
      have : icoSeqAB (2*k+2) = icoSeqAB ((2*k)+2) := by congr 1; ring
      rw [this, icoSeqAB_succ]
    have hB3 : (icoSeqAB (2*k+3)).2 =
        -2 * (icoSeqAB (2*k+2)).1 - 9 * (icoSeqAB (2*k+1)).2 := by
      have : icoSeqAB (2*k+3) = icoSeqAB ((2*k+1)+2) := by congr 1; ring
      rw [this, icoSeqAB_succ]
    have hA_new : ¬(3 : ℤ) ∣ (icoSeqAB (2*k+2)).1 := by
      rw [hA2]; intro h; apply hB
      have h9 : (3 : ℤ) ∣ 9 * (icoSeqAB (2*k)).1 := ⟨3 * (icoSeqAB (2*k)).1, by ring⟩
      have h10 : (3 : ℤ) ∣ 10 * (icoSeqAB (2*k+1)).2 := by
        obtain ⟨c, hc⟩ := h; obtain ⟨d, hd⟩ := h9; exact ⟨-(c + d), by omega⟩
      exact (IsCoprime.dvd_of_dvd_mul_left (by norm_num : IsCoprime (3 : ℤ) 10) h10)
    refine ⟨?_, ?_⟩
    · rwa [show 2*(k+1) = 2*k+2 by omega]
    · rw [show 2*(k+1)+1 = 2*k+3 by omega, hB3]; intro h; apply hA_new
      have h9 : (3 : ℤ) ∣ 9 * (icoSeqAB (2*k+1)).2 := ⟨3 * (icoSeqAB (2*k+1)).2, by ring⟩
      have h2 : (3 : ℤ) ∣ 2 * (icoSeqAB (2*k+2)).1 := by
        obtain ⟨c, hc⟩ := h; obtain ⟨d, hd⟩ := h9; exact ⟨-(c + d), by omega⟩
      exact (IsCoprime.dvd_of_dvd_mul_left (by norm_num : IsCoprime (3 : ℤ) 2) h2)

private lemma sqrt5_le_three : Real.sqrt 5 ≤ 3 := by
  have hsq : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 5]

private lemma cos_icoAngle : Real.cos icoAngle = -Real.sqrt 5 / 3 := by
  unfold icoAngle
  apply Real.cos_arccos
  · rw [neg_div, neg_le_neg_iff, div_le_one (by norm_num : (0:ℝ) < 3)]
    exact sqrt5_le_three
  · linarith [div_nonneg (Real.sqrt_nonneg 5) (show (0:ℝ) ≤ 3 by norm_num)]

/-- A_n + B_n·√5 = 3^n · 2cos(n·icoAngle) -/
theorem icoSeqAB_eq_cos : ∀ n : ℕ,
    ((icoSeqAB n).1 : ℝ) + (icoSeqAB n).2 * Real.sqrt 5 =
    (3 : ℝ)^n * (2 * Real.cos (↑n * icoAngle)) := by
  suffices h : ∀ n : ℕ,
    ((icoSeqAB n).1 : ℝ) + (icoSeqAB n).2 * Real.sqrt 5 =
        (3:ℝ)^n * (2 * Real.cos (↑n * icoAngle)) ∧
    ((icoSeqAB (n+1)).1 : ℝ) + (icoSeqAB (n+1)).2 * Real.sqrt 5 =
        (3:ℝ)^(n+1) * (2 * Real.cos (↑(n+1) * icoAngle))
  from fun n => (h n).1
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [icoSeqAB_zero, Real.cos_zero]
    · simp only [icoSeqAB_one, Nat.cast_one, pow_one, one_mul]
      push_cast; rw [cos_icoAngle]; ring
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    have hlhs : ((icoSeqAB (m+2)).1 : ℝ) + (icoSeqAB (m+2)).2 * Real.sqrt 5 =
        -2 * Real.sqrt 5 * (((icoSeqAB (m+1)).1 : ℝ) + (icoSeqAB (m+1)).2 * Real.sqrt 5) -
        9 * (((icoSeqAB m).1 : ℝ) + (icoSeqAB m).2 * Real.sqrt 5) := by
      rw [icoSeqAB_succ]; push_cast
      have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      linear_combination 2 * ((icoSeqAB (m+1)).2 : ℝ) * hsq
    rw [hlhs, ih.1, ih.2]
    have hstep : Real.cos (↑(m + 2) * icoAngle) =
        2 * Real.cos icoAngle * Real.cos (↑(m + 1) * icoAngle) -
        Real.cos (↑m * icoAngle) := cos_step icoAngle m
    conv_rhs => rw [show (2 : ℝ) * Real.cos (↑(m+2) * icoAngle) =
        2 * (2 * Real.cos icoAngle * Real.cos (↑(m+1) * icoAngle) -
             Real.cos (↑m * icoAngle)) from by rw [hstep]]
    rw [cos_icoAngle]; push_cast; ring

/-- arccos(-√5/3)/π is irrational. -/
theorem icoAngle_irrational : ¬∃ q : ℚ, icoAngle = q * Real.pi := by
  intro ⟨q, hq⟩
  set N := q.den
  have hN_pos : 0 < N := q.pos
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN_pos.ne'
  have hmul : (N : ℝ) * icoAngle = q.num * Real.pi := by
    rw [hq, Rat.cast_def]
    field_simp [hN_ne, show (q.den : ℝ) = N from rfl]; ring
  have hcos_N : Real.cos ((N : ℝ) * icoAngle) = (-1 : ℝ)^q.num.natAbs := by
    rw [hmul]; exact cos_int_mul_pi q.num
  have hseq := icoSeqAB_eq_cos N
  rw [hcos_N] at hseq
  have hpm : (-1 : ℝ)^q.num.natAbs = 1 ∨ (-1 : ℝ)^q.num.natAbs = -1 := by
    induction q.num.natAbs with
    | zero => left; simp
    | succ j ihj => rcases ihj with h | h
      · right; rw [pow_succ, h]; ring
      · left;  rw [pow_succ, h]; ring
  have h5_irr : Irrational (Real.sqrt 5) :=
    Nat.Prime.irrational_sqrt (by norm_num : Nat.Prime 5)
  have hB_zero : (icoSeqAB N).2 = 0 := by
    by_contra hne
    have hB_ne : ((icoSeqAB N).2 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hne
    have hint : ∃ z : ℤ, ((icoSeqAB N).2 : ℝ) * Real.sqrt 5 = z := by
      rcases hpm with h1 | h1 <;> rw [h1] at hseq
      · exact ⟨2 * (3:ℤ)^N - (icoSeqAB N).1, by push_cast; linarith⟩
      · exact ⟨-2 * (3:ℤ)^N - (icoSeqAB N).1, by push_cast; linarith⟩
    obtain ⟨z, hz⟩ := hint
    have h_sqrt5 : Real.sqrt 5 = (z : ℝ) / (icoSeqAB N).2 := by
      rw [eq_div_iff hB_ne]; linarith
    apply h5_irr
    rw [Set.mem_range]
    exact ⟨(z : ℚ) / ((icoSeqAB N).2 : ℚ), by
      rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast]; linarith [h_sqrt5]⟩
  simp only [hB_zero, Int.cast_zero, zero_mul, add_zero] at hseq
  have h3_dvd_A : (3 : ℤ) ∣ (icoSeqAB N).1 := by
    rcases hpm with h1 | h1 <;> rw [h1] at hseq
    · have hA : (icoSeqAB N).1 = 2 * (3:ℤ)^N := by
        have : ((icoSeqAB N).1 : ℝ) = 2 * (3:ℝ)^N := by push_cast; linarith
        exact_mod_cast this
      rw [hA]; exact dvd_mul_of_dvd_right (dvd_pow_self 3 hN_pos.ne') 2
    · have hA : (icoSeqAB N).1 = -(2 * (3:ℤ)^N) := by
        have : ((icoSeqAB N).1 : ℝ) = -(2 * (3:ℝ)^N) := by push_cast; linarith
        exact_mod_cast this
      rw [hA]; exact dvd_neg.mpr (dvd_mul_of_dvd_right (dvd_pow_self 3 hN_pos.ne') 2)
  rcases Nat.even_or_odd N with ⟨k, hk⟩ | ⟨k, hk⟩
  · apply (icoSeqAB_ndvd k).1
    have hk2 : 2*k = N := by omega
    rw [hk2]; exact h3_dvd_A
  · apply (icoSeqAB_ndvd k).2
    have : (icoSeqAB (2*k+1)).2 = 0 := by
      rw [show 2*k+1 = N by omega]; exact hB_zero
    rw [this]; exact dvd_zero 3

/-- [icoAngle] has infinite order in ℝ/πℤ. -/
theorem icoAngle_infinite_order :
    ∀ n : ℤ, n ≠ 0 → n • angleClass icoAngle ≠ 0 := by
  intro n hn hzero
  apply icoAngle_irrational
  rw [zsmul_eq_zero_iff] at hzero
  obtain ⟨m, hm⟩ := hzero
  have hn_ne : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  exact ⟨(m : ℚ) / (n : ℚ), by push_cast; field_simp; linarith⟩

/-- **The regular icosahedron has nonzero Dehn invariant.** -/
theorem ico_dehn_ne_zero (a : ℝ) (ha : a > 0) :
    edgeTerm (30 * a) icoAngle ≠ 0 := by
  unfold edgeTerm
  apply tmul_infinite_order_ne_zero
  · linarith
  · exact icoAngle_infinite_order

-- ============================================================
-- PART V: Classification — The Cube is Isolated
-- ============================================================

/-
### The Complete Classification

Among the five Platonic solids, the Dehn invariant completely
distinguishes the cube from all others:

- **Cube**: D = 0 (all 12 edges have dihedral angle π/2, a rational
  multiple of π; hence all edge terms vanish in ℝ ⊗_ℤ (ℝ/πℤ)).

- **All others**: D ≠ 0 (proved above for each solid individually).

Geometric consequence: The cube cannot be obtained by scissors
congruence from any of the other four Platonic solids.
This is an extension of Hilbert's Third Problem (1900) from
the single pair (cube, tetrahedron) to all Platonic solid pairs
involving the cube.
-/

/-- **The Cube is Isolated Among Platonic Solids**:
Among the five Platonic solids, only the cube has zero Dehn invariant.
The other four — tetrahedron, octahedron, dodecahedron, icosahedron —
all have nonzero Dehn invariant and are therefore not scissors congruent
to the cube (nor, by Dehn's theorem, to each other across zero/nonzero
Dehn invariant classes). -/
theorem cube_isolated_dehn_invariant (a : ℝ) (ha : a > 0) :
    -- Cube: 12 edges × π/2 → Dehn invariant = 0
    edgeTerm (12 * a) (Real.pi / 2) = 0 ∧
    -- Tetrahedron: 6 edges × arccos(1/3) → Dehn invariant ≠ 0
    edgeTerm (6 * a) tetAngle ≠ 0 ∧
    -- Octahedron: 12 edges × arccos(-1/3) → Dehn invariant ≠ 0
    edgeTerm (12 * a) octAngle ≠ 0 ∧
    -- Dodecahedron: 30 edges × arccos(-1/√5) → Dehn invariant ≠ 0
    edgeTerm (30 * a) dodAngle ≠ 0 ∧
    -- Icosahedron: 30 edges × arccos(-√5/3) → Dehn invariant ≠ 0
    edgeTerm (30 * a) icoAngle ≠ 0 :=
  ⟨cube_dehn_zero a,
   tet_dehn_ne_zero a ha,
   oct_dehn_ne_zero a ha,
   dod_dehn_ne_zero a ha,
   ico_dehn_ne_zero a ha⟩

/-- Among the Platonic solids, the cube is the unique solid with
zero Dehn invariant (for any edge length a > 0). -/
theorem cube_unique_zero_dehn (a : ℝ) (ha : a > 0) :
    (edgeTerm (12 * a) (Real.pi / 2) = 0) ∧
    (∀ x : ℝ, x = tetAngle ∨ x = octAngle ∨ x = dodAngle ∨ x = icoAngle →
      ∀ n : ℕ, 0 < n → edgeTerm (n * a) x ≠ 0) := by
  refine ⟨cube_dehn_zero a, fun x hx n hn => ?_⟩
  -- n * a ≠ 0 since n > 0 and a > 0
  have hna : (n : ℝ) * a ≠ 0 :=
    mul_ne_zero (Nat.cast_pos.mpr hn).ne' ha.ne'
  rcases hx with rfl | rfl | rfl | rfl
  · -- Tetrahedron: [tetAngle] has infinite order
    unfold edgeTerm
    exact tmul_infinite_order_ne_zero _ _ hna tetAngle_infinite_order
  · -- Octahedron: angleClass octAngle = -angleClass tetAngle (infinite order preserved)
    unfold edgeTerm
    apply tmul_infinite_order_ne_zero _ _ hna
    intro m hm hzero
    rw [octAngle_class, smul_neg, neg_eq_zero] at hzero
    exact tetAngle_infinite_order m hm hzero
  · -- Dodecahedron: [dodAngle] has infinite order (proved above)
    unfold edgeTerm
    exact tmul_infinite_order_ne_zero _ _ hna dodAngle_infinite_order
  · -- Icosahedron: [icoAngle] has infinite order (proved above via axiom)
    unfold edgeTerm
    exact tmul_infinite_order_ne_zero _ _ hna icoAngle_infinite_order

-- ============================================================
-- PART VI: Axiom Audit
-- ============================================================

/-
## Axiom Budget

### New axioms introduced in this file: 0
- `icoAngle_irrational` is now a proved theorem (Chebyshev ℤ[√5] argument).

### Inherited axioms (from OQ02OQ02): 0
(tmul_infinite_order_ne_zero is now PROVED via ℝ flat over ℤ — Bézout domain + NoZeroSMulDivisors)

### Total axiom count: 0 (reduced from 2)

### New theorems proved (0 sorries):
- `five_ndvd_cosThreeFifthsSeq` — 5 ∤ d_n for the new sequence
- `cosThreeFifthsSeq_eq_cos` — cos relation for d_n
- `arccos_three_fifths_irrational` — arccos(3/5)/π ∉ ℚ
- `two_arccos_sqrt5_eq` — 2·arccos(1/√5) = arccos(-3/5)
- `arccos_sqrt5_irrational` — arccos(1/√5)/π ∉ ℚ
- `dodAngle_irrational` — arccos(-1/√5)/π ∉ ℚ
- `dodAngle_infinite_order` — [arccos(-1/√5)] has infinite order
- `dod_dehn_ne_zero` — D(dodecahedron) ≠ 0
- `icoSeqAB_ndvd` — mod-3 invariant for coupled ℤ[√5] Chebyshev sequence
- `icoSeqAB_eq_cos` — A_n + B_n·√5 = 3^n·2cos(n·icoAngle)
- `icoAngle_irrational` — arccos(-√5/3)/π ∉ ℚ (proved, not axiom)
- `icoAngle_infinite_order` — [arccos(-√5/3)] has infinite order
- `ico_dehn_ne_zero` — D(icosahedron) ≠ 0
- `cube_isolated_dehn_invariant` — Complete classification table

### Sorries: 0
- All sorries eliminated. cube_unique_zero_dehn proved via tmul_infinite_order_ne_zero
  for each angle uniformly: oct via octAngle_class = -tetAngle, dod/ico via their
  infinite order theorems.
-/

-- Verification
#check arccos_three_fifths_irrational
#check dodAngle_irrational
#check dod_dehn_ne_zero
#check cube_isolated_dehn_invariant

end DissectionOfCubesOQ04
