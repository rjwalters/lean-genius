/-
# Dissection of Cubes — OQ-04 — OQ-02
## Dehn-style irrationality for a higher-dimensional dihedral angle: the 5-cell arccos(1/4)

The parent entry `DissectionOfCubesOQ04.lean` proves that the dihedral angles of the
dodecahedron and icosahedron are irrational multiples of `π`, via the Niven/Chebyshev
integer-sequence technique, and asks (OQ-02):

  *Can this technique be applied to prove irrationality results for other dihedral angles
   arising in higher-dimensional polytopes?*

This file answers **yes** for the first genuinely higher-dimensional example.  The regular
`4`-simplex — the **5-cell**, the 4-dimensional analogue of the tetrahedron — has dihedral
angle `arccos(1/4)` (the regular `n`-simplex has dihedral angle `arccos(1/n)`).  We prove

  **`arccos(1/4)` is an irrational multiple of `π`** (`simplex4Angle_irrational`),

so, exactly as in the Dehn–Hilbert theory, the 5-cell has a nonzero Dehn invariant and cannot
be scissors-congruent to a 4-cube cross-section built from right dihedral angles alone.

## The technique, adapted

Because `2·cos(arccos(1/4)) = 1/2` has denominator a power of `2`, the right scaling is `2^n`
(not `4^n`): set `f_n = 2^n · 2cos(n·θ)` with `θ = arccos(1/4)`.  The Chebyshev recurrence
`2cos((n+2)θ) = (2cosθ)·2cos((n+1)θ) − 2cos(nθ)` becomes the **integer** recurrence

  `f_0 = 2,  f_1 = 1,  f_{n+2} = f_{n+1} − 4·f_n`.

Modulo `2` this is `f_{n+2} ≡ f_{n+1}`, and `f_1 = 1` is odd, so **`f_n` is odd for every
`n ≥ 1`** (`two_ndvd_cosQuarterSeq_pos`).  But if `θ = (p/q)·π` then
`cos(q·θ) = cos(p·π) = ±1`, so `f_q = ±2^{q+1}` is even for `q ≥ 1` — a contradiction.

The parity obstruction (prime `2`) replaces the mod-`5` / mod-`3` obstructions of the parent
file; the `2^n` scaling is what makes the prime `2` available even though `4` is not squarefree.

All results are over `ℝ`, elementary, and axiom-free.

## References
- Hilbert's third problem; Dehn (1901); Sydler (1965).
- Niven, I. (1956). *Irrational Numbers.* Carus Math. Monographs 11 (Niven's theorem: the only
  rational values of `cos(rπ)` for rational `r` are `0, ±1/2, ±1`).
- Coxeter, H. S. M. *Regular Polytopes.* (Dihedral angle `arccos(1/n)` of the regular `n`-simplex.)
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

namespace DissectionOfCubesOQ04OQ02

open Real

/-! ## Trigonometric helper lemmas (restated for self-containment) -/

/-- Cosine three-term recurrence: `cos((k+2)θ) = 2cosθ·cos((k+1)θ) − cos(kθ)`. -/
theorem cos_step (θ : ℝ) (k : ℕ) :
    Real.cos ((↑(k + 2)) * θ) =
    2 * Real.cos θ * Real.cos ((↑(k + 1)) * θ) - Real.cos (↑k * θ) := by
  have h1 : (↑(k + 2) : ℝ) * θ = (↑(k + 1)) * θ + θ := by push_cast; ring
  have h2 : (↑k : ℝ) * θ = (↑(k + 1)) * θ - θ := by push_cast; ring
  rw [h1, Real.cos_add, h2, Real.cos_sub]
  ring

/-- `cos(n·π) = (-1)^n` for natural `n`. -/
theorem cos_nat_mul_pi (n : ℕ) : Real.cos (↑n * Real.pi) = (-1 : ℝ) ^ n := by
  induction n with
  | zero => simp [Real.cos_zero]
  | succ k ih =>
    have : (↑(k + 1) : ℝ) * Real.pi = ↑k * Real.pi + Real.pi := by push_cast; ring
    rw [this, Real.cos_add, ih, Real.cos_pi, Real.sin_pi]
    ring

/-- `cos(n·π) = (-1)^|n|` for integer `n`. -/
theorem cos_int_mul_pi (n : ℤ) : Real.cos (↑n * Real.pi) = (-1 : ℝ) ^ n.natAbs := by
  cases n with
  | ofNat m => exact cos_nat_mul_pi m
  | negSucc m =>
    have : (↑(Int.negSucc m) : ℝ) * Real.pi = -((↑(m + 1) : ℝ) * Real.pi) := by
      push_cast; ring
    rw [this, Real.cos_neg]
    exact cos_nat_mul_pi (m + 1)

/-! ## The integer sequence for `arccos(1/4)` -/

/-- Integer sequence for the `arccos(1/4)/π` irrationality proof.
`f_0 = 2, f_1 = 1, f_{n+2} = f_{n+1} − 4·f_n`.  Key: `f_n = 2^n · 2cos(n·arccos(1/4))`. -/
def cosQuarterSeq : ℕ → ℤ
  | 0     => 2
  | 1     => 1
  | (n+2) => cosQuarterSeq (n+1) - 4 * cosQuarterSeq n

@[simp] theorem cosQuarterSeq_zero : cosQuarterSeq 0 = 2 := rfl
@[simp] theorem cosQuarterSeq_one  : cosQuarterSeq 1 = 1 := rfl
theorem cosQuarterSeq_succ (n : ℕ) :
    cosQuarterSeq (n+2) = cosQuarterSeq (n+1) - 4 * cosQuarterSeq n := rfl

/-- **Parity obstruction (successor form).** `2` never divides `f_{k+1}`: mod `2` the recurrence
is `f_{n+2} ≡ f_{n+1}`, and `f_1 = 1` is odd, so all later terms are odd. -/
theorem two_ndvd_cosQuarterSeq_succ : ∀ k : ℕ, ¬((2 : ℤ) ∣ cosQuarterSeq (k + 1)) := by
  intro k
  induction k with
  | zero => norm_num [cosQuarterSeq]
  | succ n ih =>
    rw [cosQuarterSeq_succ]
    intro h
    obtain ⟨c, hc⟩ := h
    -- `f_{n+1} = (f_{n+1} − 4 f_n) + 4 f_n = 2c + 4 f_n = 2(c + 2 f_n)`, so `2 ∣ f_{n+1}`.
    exact ih ⟨c + 2 * cosQuarterSeq n, by omega⟩

/-- **Parity obstruction.** `2` never divides `f_n` for `n ≥ 1`. -/
theorem two_ndvd_cosQuarterSeq_pos {n : ℕ} (hn : 1 ≤ n) : ¬((2 : ℤ) ∣ cosQuarterSeq n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact two_ndvd_cosQuarterSeq_succ k

/-- **Arithmetic backbone.** `f_n = 2^n · 2cos(n·arccos(1/4))`. -/
theorem cosQuarterSeq_eq_cos (k : ℕ) :
    (cosQuarterSeq k : ℝ) = (2 : ℝ) ^ k * (2 * Real.cos (↑k * Real.arccos (1 / 4))) := by
  suffices h : ∀ n : ℕ,
      (cosQuarterSeq n : ℝ) = (2 : ℝ) ^ n * (2 * Real.cos (↑n * Real.arccos (1 / 4))) ∧
      (cosQuarterSeq (n + 1) : ℝ) =
        (2 : ℝ) ^ (n + 1) * (2 * Real.cos (↑(n + 1) * Real.arccos (1 / 4)))
    from (h k).1
  intro n
  induction n with
  | zero =>
    refine ⟨by simp [cosQuarterSeq, Real.cos_zero], ?_⟩
    simp only [cosQuarterSeq_one, Nat.cast_one, pow_one, one_mul, Nat.zero_add,
      Real.cos_arccos (by norm_num : (-1 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1)]
    norm_num
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    have hrec : (cosQuarterSeq (m + 2) : ℝ) =
        (cosQuarterSeq (m + 1) : ℝ) - 4 * (cosQuarterSeq m : ℝ) := by
      simp only [cosQuarterSeq_succ]; push_cast; ring
    rw [hrec, ih.2, ih.1, cos_step,
        Real.cos_arccos (by norm_num : (-1 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1)]
    push_cast; ring

/-! ## The 5-cell dihedral angle -/

/-- The dihedral angle of the regular `4`-simplex (the **5-cell**): `arccos(1/4)`. -/
noncomputable def simplex4Angle : ℝ := Real.arccos (1 / 4)

/-- **Main result.** The 5-cell's dihedral angle `arccos(1/4)` is an irrational multiple of `π`.

If `arccos(1/4) = (p/q)·π` then `f_q = ±2^{q+1}` is even for `q ≥ 1`, contradicting that `f_n`
is odd for all `n ≥ 1`. -/
theorem simplex4Angle_irrational : ¬∃ q : ℚ, simplex4Angle = q * Real.pi := by
  rintro ⟨q, hq⟩
  rw [simplex4Angle] at hq
  have hb_pos : 0 < q.den := q.pos
  have hmul : (q.den : ℝ) * Real.arccos (1 / 4) = (q.num : ℝ) * Real.pi := by
    rw [hq, Rat.cast_def]; field_simp
  have hcos_eq : Real.cos ((↑q.den : ℝ) * Real.arccos (1 / 4)) = (-1 : ℝ) ^ q.num.natAbs := by
    rw [hmul]; exact cos_int_mul_pi q.num
  have hseq := cosQuarterSeq_eq_cos q.den
  rw [hcos_eq] at hseq
  have hden_pos : 1 ≤ q.den := hb_pos
  have hpm : (-1 : ℝ) ^ q.num.natAbs = 1 ∨ (-1 : ℝ) ^ q.num.natAbs = -1 := by
    rcases Nat.even_or_odd q.num.natAbs with h | h
    · exact Or.inl h.neg_one_pow
    · exact Or.inr h.neg_one_pow
  rcases hpm with h1 | h1
  · rw [h1] at hseq
    have hval : cosQuarterSeq q.den = 2 * (2 : ℤ) ^ q.den := by
      have h : (cosQuarterSeq q.den : ℝ) = ↑(2 * (2 : ℤ) ^ q.den) := by
        rw [hseq]; push_cast; ring
      exact_mod_cast h
    exact two_ndvd_cosQuarterSeq_pos hden_pos
      (hval ▸ Dvd.intro _ rfl)
  · rw [h1] at hseq
    have hval : cosQuarterSeq q.den = -(2 * (2 : ℤ) ^ q.den) := by
      have h : (cosQuarterSeq q.den : ℝ) = ↑(-(2 * (2 : ℤ) ^ q.den)) := by
        rw [hseq]; push_cast; ring
      exact_mod_cast h
    exact two_ndvd_cosQuarterSeq_pos hden_pos
      (hval ▸ (Dvd.intro _ rfl).neg_right)

/-- Restatement: `arccos(1/4)` is not a rational multiple of `π`. -/
theorem arccos_quarter_irrational : ¬∃ q : ℚ, Real.arccos (1 / 4 : ℝ) = q * Real.pi :=
  simplex4Angle_irrational

#check @simplex4Angle_irrational
#check @cosQuarterSeq_eq_cos
#check @two_ndvd_cosQuarterSeq_pos

end DissectionOfCubesOQ04OQ02
