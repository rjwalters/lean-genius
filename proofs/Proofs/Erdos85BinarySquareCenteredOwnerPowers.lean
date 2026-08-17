import Proofs.Erdos85BinarySquareCenteredOwnerResolution

/-!
# All moments of the centered owner resolution

Pairwise annihilation does not stop at the quadratic and cubic identities.
Every positive power of the centered defect resolution splits colorwise.
This packages the general fact so the search can move directly to the fourth
moment, where selector collisions survive the trace.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A selected summand satisfies the same recursion as its selecting sum. -/
theorem matrix_pow_mul_eq_succ_of_mul_eq_sq
    {V K : Type*} [Fintype V] [DecidableEq V] [CommRing K]
    (C R : Matrix V V K) (hselect : C * R = C * C)
    (n : ℕ) (hn : 1 ≤ n) :
    C ^ n * R = C ^ (n + 1) := by
  cases n with
  | zero => omega
  | succ k =>
      rw [pow_succ C k, Matrix.mul_assoc, hselect, ← Matrix.mul_assoc,
        ← pow_succ C k, ← pow_succ C (k + 1)]

/-- Abstract all-positive-moments Parseval identity. -/
theorem sum_matrix_pow_eq_pow_of_sum_eq_of_mul_sum_eq_sq
    {I V K : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
    [CommRing K]
    (C : I → Matrix V V K) (R : Matrix V V K)
    (hsum : ∑ i, C i = R) (hselect : ∀ i, C i * R = C i * C i)
    (n : ℕ) (hn : 1 ≤ n) :
    ∑ i, C i ^ n = R ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        simpa using hsum
      · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        calc
          ∑ i, C i ^ (n + 1) = ∑ i, C i ^ n * R := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact (matrix_pow_mul_eq_succ_of_mul_eq_sq
              (C i) R (hselect i) n hnpos).symm
          _ = (∑ i, C i ^ n) * R := by rw [Finset.sum_mul]
          _ = R ^ n * R := by rw [ih hnpos]
          _ = R ^ (n + 1) := (pow_succ R n).symm

/-- **All centered-owner moments split colorwise.** -/
theorem binarySquare_regular_sum_centeredOwnerGrams_pow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (hsum : ∑ c, m c = q)
    (n : ℕ) (hn : 1 ≤ n) :
    let C : (secondOrderDefectGraph G).ConnectedComponent → Matrix V V ℤ :=
      fun c =>
        (q : ℤ) •
            ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
              (m c : ℤ) • (1 : Matrix V V ℤ)) -
          (m c : ℤ) • FriendshipTheoremOQ01.onesMatrix V
    let R := (q : ℤ) •
      (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) -
        (secondOrderDefectGraph G).adjMatrix ℤ)
    ∑ c, C c ^ n = R ^ n := by
  dsimp
  let C : (secondOrderDefectGraph G).ConnectedComponent → Matrix V V ℤ :=
    fun c =>
      (q : ℤ) •
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
            (m c : ℤ) • (1 : Matrix V V ℤ)) -
        (m c : ℤ) • FriendshipTheoremOQ01.onesMatrix V
  let R : Matrix V V ℤ := (q : ℤ) •
    (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) -
      (secondOrderDefectGraph G).adjMatrix ℤ)
  apply sum_matrix_pow_eq_pow_of_sum_eq_of_mul_sum_eq_sq C R
  · exact binarySquare_regular_sum_centeredOwnerGrams G hfree (by omega) m hsum
  · intro c
    exact binarySquare_regular_centeredOwnerGram_mul_defectResolution
      G hfree hq hreg hcard m hm hsum c
  · exact hn

/-- Trace form of the all-moments resolution. -/
theorem binarySquare_regular_sum_trace_centeredOwnerGrams_pow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (hsum : ∑ c, m c = q)
    (n : ℕ) (hn : 1 ≤ n) :
    let C : (secondOrderDefectGraph G).ConnectedComponent → Matrix V V ℤ :=
      fun c =>
        (q : ℤ) •
            ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
              (m c : ℤ) • (1 : Matrix V V ℤ)) -
          (m c : ℤ) • FriendshipTheoremOQ01.onesMatrix V
    let R := (q : ℤ) •
      (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) -
        (secondOrderDefectGraph G).adjMatrix ℤ)
    ∑ c, Matrix.trace (C c ^ n) = Matrix.trace (R ^ n) := by
  dsimp
  have hpow := binarySquare_regular_sum_centeredOwnerGrams_pow
    G hfree hq hreg hcard m hm hsum n hn
  have htrace := congrArg Matrix.trace hpow
  simpa only [Matrix.trace_sum] using htrace

end

end Erdos85
