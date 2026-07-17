/-
  Factor-Remainder Nullstellensatz OQ-01: Strong Nullstellensatz I(V(J)) = √J

  The strong Nullstellensatz (Hilbert 1893) states that for an ideal J
  in k[x₁,...,xₙ] over an algebraically closed field k:

    I(V(J)) = √J

  where V(J) is the zero locus and I(V) is the vanishing ideal.

  This is ALREADY IN MATHLIB as:
    `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`

  This file provides a bridge from the gallery's Factor-Remainder
  infrastructure to Mathlib's Nullstellensatz.

  Parent: FactorRemainderTheorem.lean
-/

import Mathlib

namespace FactorRemainderNullstellensatzOQ01

open MvPolynomial

variable {σ : Type*} {k : Type*} [Field k] [IsAlgClosed k]

-- ============================================================
-- PART I: Mathlib's Nullstellensatz
-- ============================================================

/-- The strong Nullstellensatz, directly from Mathlib.
    I(V(J)) = √J for any ideal J in k[x₁,...,xₙ].
    (v4.31: Mathlib's `zeroLocus`/`vanishingIdeal` now take the field
    explicitly and `zeroLocus` takes the ideal directly; the upstream
    theorem now requires `Finite σ`, which is genuinely necessary —
    the statement fails for infinitely many variables.) -/
theorem strong_nullstellensatz [Finite σ] (I : Ideal (MvPolynomial σ k)) :
    vanishingIdeal k (zeroLocus k I) = I.radical :=
  vanishingIdeal_zeroLocus_eq_radical I

-- ============================================================
-- PART II: Corollaries
-- ============================================================

/-- Weak Nullstellensatz: J is proper iff V(J) is nonempty.
    Equivalently: J = (1) iff V(J) = ∅. -/
theorem weak_nullstellensatz [Finite σ] (I : Ideal (MvPolynomial σ k))
    (hI : I ≠ ⊤) :
    (zeroLocus k I).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro h
  have := vanishingIdeal_zeroLocus_eq_radical (K := k) I
  rw [h, vanishingIdeal_empty] at this
  exact hI (Ideal.radical_eq_top.mp this.symm)

/-- A polynomial vanishes on V(J) iff some power is in J. -/
theorem membership_criterion [Finite σ] (I : Ideal (MvPolynomial σ k))
    (f : MvPolynomial σ k) :
    f ∈ vanishingIdeal k (zeroLocus k I) ↔
    f ∈ I.radical :=
  by rw [vanishingIdeal_zeroLocus_eq_radical]

/-- If J is radical (J = √J), then I(V(J)) = J. -/
theorem radical_ideal_correspondence [Finite σ] (I : Ideal (MvPolynomial σ k))
    (hrad : I.IsRadical) :
    vanishingIdeal k (zeroLocus k I) = I := by
  rw [vanishingIdeal_zeroLocus_eq_radical, hrad.radical]

-- ============================================================
-- PART III: Galois Connection
-- ============================================================

omit [IsAlgClosed k] in
/-- V and I form a Galois connection (antitone): V ⊆ V(J) ↔ J ≤ I(V). -/
theorem galois_connection_vi :
    @GaloisConnection
      (Ideal (MvPolynomial σ k))
      (Set (σ → k))ᵒᵈ
      _
      _
      (zeroLocus k)
      (vanishingIdeal k) :=
  zeroLocus_vanishingIdeal_galoisConnection

end FactorRemainderNullstellensatzOQ01
