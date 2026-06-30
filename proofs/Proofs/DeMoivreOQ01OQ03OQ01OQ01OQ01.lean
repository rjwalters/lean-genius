/-
# Sharp injectivity of the Chebyshev monoid homomorphism `n ↦ Cₙ`
  (de-moivre-oq-01-oq-03-oq-01-oq-01-oq-01)

## Open Question (OQ-01 of de-moivre-oq-01-oq-03-oq-01-oq-01)
The parent `de-moivre-oq-01-oq-03-oq-01-oq-01` bundled the integer-index Chebyshev
map into a **monoid homomorphism**
  `chebyshevCEnd R : (ℤ, ·) →* Function.End R[X]`,   `n ↦ (Cₙ ∘ ·)`.
A homomorphism invites the immediate structural question: **is it injective?**
Equivalently, what are its fibers — when do two indices give the *same* Chebyshev
operator `Cₘ ∘ · = Cₙ ∘ ·`?

## Answer: NO, and the failure is *exactly* the even symmetry `C₋ₙ = Cₙ`.

The map is **not** injective: already `chebyshevCEnd R 1 = chebyshevCEnd R (-1)`
because `C₁ = X = C₋₁`.  We pin the fibers down completely:

  `chebyshevCEnd R m = chebyshevCEnd R n  ↔  m = n ∨ m = -n`.

So the only coincidences are the sign flips `n ↔ -n`; the homomorphism is **2-to-1
away from `0`** and injective on the nonnegative cone `{n ≥ 0}`.  Structurally it
factors through the multiplicative monoid map `ℤ → ℕ, n ↦ |n|` (note `|mn| = |m||n|`),
and the induced map on indices `|n|` is injective.

## The engine: `Cₙ` is monic of degree `|n|`
The first-kind integer-index Chebyshev polynomial is **monic of degree `|n|`** for
`n ≥ 1` (and `C₀ = 2` has degree `0 = |0|`).  We prove this from the three-term
recurrence `C_{n+2} = X·C_{n+1} − Cₙ` by two-step induction, exactly mirroring the
gallery's `Tₙ` degree proof (`DeMoivreOQ02OQ03OQ02`).  The degree is the injectivity
invariant: `Cₘ = Cₙ ⟹ |m| = |n|` (compare degrees), and conversely
`|m| = |n| ⟹ Cₘ = Cₙ` via `C_natAbs`.  Combining with `Int.natAbs_eq_natAbs_iff`
gives the `m = ±n` characterization.

## Status
- `0` sorries, `0` axioms, no `native_decide`.
- New content: `Cₙ` monic of degree `|n|` (general `[CommRing R] [Nontrivial R]`),
  the equality criterion `Cₘ = Cₙ ↔ m = ±n`, and the resulting fiber description,
  non-injectivity, and injectivity-on-the-cone for `chebyshevCEnd`.
- Reuses Mathlib's `C_neg`, `C_natAbs`, `C_add_two`, `monic_X_pow_sub_C`, and the
  parent's `chebyshevCEnd` monoid homomorphism.
-/

import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic
import Proofs.DeMoivreOQ01OQ03OQ01OQ01

namespace DeMoivreChebyshevInjectivity

open Polynomial Polynomial.Chebyshev
open DeMoivreChebyshevMonoidHom

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: `Cₙ` IS MONIC OF DEGREE `|n|`
═══════════════════════════════════════════════════════════════════════════════ -/

variable (R : Type*) [CommRing R] [Nontrivial R]

/-- **Monicity and degree of `Cₙ` for positive index.**  For every `n : ℕ`, the
    Chebyshev polynomial `C R (n+1)` is monic of degree `n+1`.  Proof by two-step
    induction on the recurrence `C_{k+2} = X·C_{k+1} − C_k`. -/
theorem C_monic_natDegree_succ (n : ℕ) :
    (C R ((n : ℤ) + 1)).Monic ∧ (C R ((n : ℤ) + 1)).natDegree = n + 1 := by
  induction n using Nat.twoStepInduction with
  | zero =>
    refine ⟨?_, ?_⟩
    · have : ((0 : ℕ) : ℤ) + 1 = 1 := by norm_num
      rw [this, C_one]; exact monic_X
    · have : ((0 : ℕ) : ℤ) + 1 = 1 := by norm_num
      rw [this, C_one]; simp
  | one =>
    have hcast : ((1 : ℕ) : ℤ) + 1 = 2 := by norm_num
    have hC2 : C R (2 : ℤ) = X ^ 2 - Polynomial.C (2 : R) := by
      rw [C_two, ← map_ofNat Polynomial.C 2]
    refine ⟨?_, ?_⟩
    · rw [hcast, hC2]; exact monic_X_pow_sub_C _ (by norm_num)
    · rw [hcast, hC2, natDegree_X_pow_sub_C]
  | more n ih0 ih1 =>
    obtain ⟨hmon0, hdeg0⟩ := ih0
    obtain ⟨hmon1, hdeg1⟩ := ih1
    -- recurrence: C R (n+3) = X * C R (n+2) - C R (n+1)
    have hrec : C R (((n + 2 : ℕ) : ℤ) + 1)
        = X * C R (((n + 1 : ℕ) : ℤ) + 1) - C R (((n : ℕ) : ℤ) + 1) := by
      have h := C_add_two R (((n : ℕ) : ℤ) + 1)
      have e1 : ((n + 2 : ℕ) : ℤ) + 1 = ((n : ℕ) : ℤ) + 1 + 2 := by push_cast; ring
      have e2 : ((n + 1 : ℕ) : ℤ) + 1 = ((n : ℕ) : ℤ) + 1 + 1 := by push_cast; ring
      rw [e1, e2]; exact h
    -- C R (n+2) ≠ 0 (it is monic, hence nonzero in a nontrivial ring)
    have hne1 : C R (((n + 1 : ℕ) : ℤ) + 1) ≠ 0 := hmon1.ne_zero
    -- degree of A := X * C R (n+2)
    have hdA : (X * C R (((n + 1 : ℕ) : ℤ) + 1)).natDegree = n + 3 := by
      rw [natDegree_X_mul hne1, hdeg1]
    -- A is monic
    have hmonA : (X * C R (((n + 1 : ℕ) : ℤ) + 1)).Monic := monic_X.mul hmon1
    -- C R (n+1) has strictly smaller degree
    have hdeg_lt : (C R (((n : ℕ) : ℤ) + 1)).natDegree
        < (X * C R (((n + 1 : ℕ) : ℤ) + 1)).natDegree := by
      rw [hdA, hdeg0]; omega
    have hdeg_lt' : (C R (((n : ℕ) : ℤ) + 1)).degree
        < (X * C R (((n + 1 : ℕ) : ℤ) + 1)).degree := degree_lt_degree hdeg_lt
    refine ⟨?_, ?_⟩
    · rw [hrec, sub_eq_add_neg]
      exact hmonA.add_of_left (by rwa [degree_neg])
    · rw [hrec, natDegree_sub_eq_left_of_natDegree_lt hdeg_lt, hdA]

/-- **Degree of `Cₙ` for natural index.**  `natDegree (C R n) = n`. -/
theorem C_natDegree_nat (m : ℕ) : (C R (m : ℤ)).natDegree = m := by
  cases m with
  | zero => simp
  | succ k =>
    have h := (C_monic_natDegree_succ R k).2
    have e : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
    rw [e]; exact h

/-- **Degree of `Cₙ`.**  For every integer index, `natDegree (C R n) = |n|`. -/
theorem C_natDegree (n : ℤ) : (C R n).natDegree = n.natAbs := by
  rw [← C_natAbs R n, C_natDegree_nat]

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: THE EQUALITY CRITERION `Cₘ = Cₙ ↔ m = ±n`
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Equality of Chebyshev polynomials is exactly equality of `|index|`.**
    `C R m = C R n ↔ |m| = |n|`.  Forward by comparing degrees; backward by the
    even symmetry `C_natAbs`. -/
theorem C_eq_iff_natAbs (m n : ℤ) : C R m = C R n ↔ m.natAbs = n.natAbs := by
  constructor
  · intro h
    have := congrArg Polynomial.natDegree h
    rwa [C_natDegree, C_natDegree] at this
  · intro h
    rw [← C_natAbs R m, ← C_natAbs R n, h]

/-- **Sharp equality criterion.**  `C R m = C R n ↔ m = n ∨ m = -n`: the only
    coincidences among Chebyshev polynomials are the sign flips. -/
theorem C_eq_iff (m n : ℤ) : C R m = C R n ↔ m = n ∨ m = -n := by
  rw [C_eq_iff_natAbs, Int.natAbs_eq_natAbs_iff]

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: FIBERS, NON-INJECTIVITY, AND INJECTIVITY ON THE CONE
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Two Chebyshev endomorphisms agree iff their generating polynomials agree:
    `chebyshevCEnd R m = chebyshevCEnd R n ↔ C R m = C R n`.  (Evaluate at `X`.) -/
theorem chebyshevCEnd_eq_iff_C (m n : ℤ) :
    chebyshevCEnd R m = chebyshevCEnd R n ↔ C R m = C R n := by
  constructor
  · intro h
    have hX : chebyshevCEnd R m X = chebyshevCEnd R n X := by rw [h]
    rwa [chebyshevCEnd_apply, chebyshevCEnd_apply, Polynomial.comp_X,
      Polynomial.comp_X] at hX
  · intro h
    funext p
    rw [chebyshevCEnd_apply, chebyshevCEnd_apply, h]

/-- **Fiber description of the monoid homomorphism.**
    `chebyshevCEnd R m = chebyshevCEnd R n ↔ m = n ∨ m = -n`. -/
theorem chebyshevCEnd_eq_iff (m n : ℤ) :
    chebyshevCEnd R m = chebyshevCEnd R n ↔ m = n ∨ m = -n := by
  rw [chebyshevCEnd_eq_iff_C, C_eq_iff]

/-- **The Chebyshev monoid homomorphism is not injective.**  Witnessed by the
    even symmetry `C₁ = X = C₋₁`, so `1` and `-1` have the same image. -/
theorem chebyshevCEnd_not_injective :
    ¬ Function.Injective (chebyshevCEnd R) := by
  intro hinj
  have h11 : (1 : ℤ) = -1 := by
    apply hinj
    rw [chebyshevCEnd_eq_iff]; right; rfl
  norm_num at h11

/-- **Injectivity on the nonnegative cone.**  Restricted to `{n ≥ 0}`, the monoid
    homomorphism `chebyshevCEnd` *is* injective: distinct nonnegative indices give
    distinct Chebyshev operators. -/
theorem chebyshevCEnd_injOn_nonneg :
    Set.InjOn (chebyshevCEnd R) {n : ℤ | 0 ≤ n} := by
  intro m hm n hn h
  rw [chebyshevCEnd_eq_iff] at h
  simp only [Set.mem_setOf_eq] at hm hn
  rcases h with h | h
  · exact h
  · omega

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: CONSISTENCY CHECKS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- `C₂ = X² − 2` has degree `2 = |2|` over `ℝ`. -/
example : (C ℝ 2).natDegree = 2 := by
  have := C_natDegree ℝ 2; simpa using this

/-- The sign-flip coincidence `C₃ = C₋₃` over `ℝ`. -/
example : C ℝ 3 = C ℝ (-3) := by
  rw [C_eq_iff]; right; rfl

/-- `C₂ ≠ C₃` (different degrees), so the indices `2` and `3` are distinguished. -/
example : C ℝ 2 ≠ C ℝ 3 := by
  rw [Ne, C_eq_iff]; decide

#check @C_natDegree
#check @C_eq_iff
#check @chebyshevCEnd_eq_iff
#check @chebyshevCEnd_not_injective

end DeMoivreChebyshevInjectivity
