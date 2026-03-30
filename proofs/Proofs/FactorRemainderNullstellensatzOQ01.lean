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
    I(V(J)) = √J for any ideal J in k[x₁,...,xₙ]. -/
theorem strong_nullstellensatz (I : Ideal (MvPolynomial σ k)) :
    vanishingIdeal (zeroLocus (↑I : Set (MvPolynomial σ k))) = I.radical :=
  vanishingIdeal_zeroLocus_eq_radical I

-- ============================================================
-- PART II: Corollaries
-- ============================================================

/-- Weak Nullstellensatz: J is proper iff V(J) is nonempty.
    Equivalently: J = (1) iff V(J) = ∅. -/
theorem weak_nullstellensatz [Finite σ] (I : Ideal (MvPolynomial σ k))
    (hI : I ≠ ⊤) :
    (zeroLocus (↑I : Set (MvPolynomial σ k))).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro h
  have := vanishingIdeal_zeroLocus_eq_radical I
  rw [h, vanishingIdeal_empty] at this
  exact hI (Ideal.eq_top_of_radical_eq_top this)

/-- A polynomial vanishes on V(J) iff some power is in J. -/
theorem membership_criterion (I : Ideal (MvPolynomial σ k))
    (f : MvPolynomial σ k) :
    f ∈ vanishingIdeal (zeroLocus (↑I : Set (MvPolynomial σ k))) ↔
    f ∈ I.radical :=
  by rw [vanishingIdeal_zeroLocus_eq_radical]

/-- If J is radical (J = √J), then I(V(J)) = J. -/
theorem radical_ideal_correspondence (I : Ideal (MvPolynomial σ k))
    (hrad : I.IsRadical) :
    vanishingIdeal (zeroLocus (↑I : Set (MvPolynomial σ k))) = I := by
  rw [vanishingIdeal_zeroLocus_eq_radical, hrad.radical]

-- ============================================================
-- PART III: Galois Connection
-- ============================================================

/-- V and I form a Galois connection (antitone). -/
theorem galois_connection_vi :
    @GaloisConnection
      (Ideal (MvPolynomial σ k))ᵒᵈ
      (Set (σ → k))
      _
      _
      (fun I => zeroLocus (↑(OrderDual.ofDual I) : Set (MvPolynomial σ k)))
      (fun V => OrderDual.toDual (vanishingIdeal V)) :=
  (zeroLocus_vanishingIdeal_galoisConnection (σ := σ) (k := k)).dual

end FactorRemainderNullstellensatzOQ01
