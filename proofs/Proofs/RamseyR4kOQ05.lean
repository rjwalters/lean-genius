/-
  RamseyR4kOQ05.lean

  The full Erdős–Szekeres upper bound for Ramsey numbers.

  ════════════════════════════════════════════════════════════════════════════
  This answers the open question `ramsey-r4k-oq-05` from the parent gallery entry
  `ramsey-r4k`:

    "Can `ramsey_recursion` be generalized to give the full Erdős–Szekeres upper
     bound R(r,s) ≤ C(r+s-2, r-1) by induction on r+s, using
     `ramseyUpperBound_mono_s` and Pascal's identity to close the induction?"

  The answer is YES.  Working over the parent's `RamseyProp`/`ramseyUpperBound`
  API (from `Proofs.RamseyR4k`), we prove

    RamseyProp (C(r+s-2, r-1)) r s      for all r, s ≥ 1,

  i.e. the complete graph on C(r+s-2, r-1) vertices, 2-coloured, always contains a
  red r-clique or a blue s-clique.  Equivalently, R(r,s) ≤ C(r+s-2, r-1), the
  Erdős–Szekeres (1935) bound.  The parent only used the recursion at the single
  point (4,k); here it is discharged for the entire diagonal-and-off-diagonal
  table by a clean strong induction on r + s, with Pascal's identity
  (`Nat.choose_succ_succ'`) closing the step exactly.
  ════════════════════════════════════════════════════════════════════════════

  Classical statement (Erdős–Szekeres 1935 / Ramsey 1930):
    R(r, s) ≤ R(r-1, s) + R(r, s-1),  with  R(r,1) = R(1,s) = 1,
  which unrolls to R(r,s) ≤ C(r+s-2, r-1).  Our `RamseyProp n r s` says K_n → (r,s),
  so the additive recursion `ramsey_recursion` plays the role of the R(r-1,s)+R(r,s-1)
  step and Pascal glues the two binomial coefficients into one.
-/
import Proofs.RamseyR4k

namespace RamseyR4k

open Nat

/-- **Erdős–Szekeres upper bound (strong-induction core).**  For every bound `N`
and all `r, s ≥ 1` with `r + s ≤ N`, the complete graph on `C(r+s-2, r-1)`
vertices has the Ramsey property `RamseyProp _ r s`.  The bound variable `N`
carries the strong induction on `r + s`. -/
theorem ramseyProp_erdos_szekeres_aux :
    ∀ (N r s : ℕ), r + s ≤ N → 1 ≤ r → 1 ≤ s →
      RamseyProp (Nat.choose (r + s - 2) (r - 1)) r s := by
  intro N
  induction N with
  | zero =>
    intro r s hN hr hs
    omega
  | succ N IH =>
    intro r s _ hr hs
    -- Base case r = 1: C(1+s-2, 0) = C(s-1, 0) = 1, and K₁ → (1, s).
    rcases Nat.lt_or_ge r 2 with hr1 | hr2
    · have hr_eq : r = 1 := by omega
      subst hr_eq
      have hc : Nat.choose (1 + s - 2) (1 - 1) = 1 := by simp
      rw [hc]
      exact ramseyProp_one_left 1 s le_rfl
    -- Base case s = 1: C(r+1-2, r-1) = C(r-1, r-1) = 1, and K₁ → (r, 1).
    rcases Nat.lt_or_ge s 2 with hs1 | hs2
    · have hs_eq : s = 1 := by omega
      subst hs_eq
      have hc : Nat.choose (r + 1 - 2) (r - 1) = 1 := by
        have hidx : r + 1 - 2 = r - 1 := by omega
        rw [hidx, Nat.choose_self]
      rw [hc]
      exact ramseyProp_one_right 1 r le_rfl
    -- Inductive step: r ≥ 2 and s ≥ 2.
    · -- IH on (r-1, s):  C((r-1)+s-2, (r-1)-1) = C(r+s-3, r-2)  vertices.
      have ih1 : RamseyProp (Nat.choose (r - 1 + s - 2) (r - 1 - 1)) (r - 1) s :=
        IH (r - 1) s (by omega) (by omega) hs
      -- IH on (r, s-1):  C(r+(s-1)-2, r-1) = C(r+s-3, r-1)  vertices.
      have ih2 : RamseyProp (Nat.choose (r + (s - 1) - 2) (r - 1)) r (s - 1) :=
        IH r (s - 1) (by omega) hr (by omega)
      -- Normalise the two binomial indices to a common r+s-3.
      have e1 : r - 1 + s - 2 = r + s - 3 := by omega
      have e1' : r - 1 - 1 = r - 2 := by omega
      have e2 : r + (s - 1) - 2 = r + s - 3 := by omega
      rw [e1, e1'] at ih1
      rw [e2] at ih2
      -- ramsey_recursion glues them additively.
      have hrec := ramsey_recursion _ _ r s hr2 hs2 ih1 ih2
      -- Pascal's identity turns the sum into the single coefficient C(r+s-2, r-1).
      have hpascal : Nat.choose (r + s - 2) (r - 1)
          = Nat.choose (r + s - 3) (r - 2) + Nat.choose (r + s - 3) (r - 1) := by
        have h1 : r + s - 2 = (r + s - 3) + 1 := by omega
        have h2 : r - 1 = (r - 2) + 1 := by omega
        rw [h1, h2, Nat.choose_succ_succ']
      rw [hpascal]
      exact hrec

/-- **The Erdős–Szekeres upper bound `R(r,s) ≤ C(r+s-2, r-1)`.**  For all
`r, s ≥ 1`, any 2-colouring of the edges of the complete graph on
`C(r+s-2, r-1)` vertices contains a red `r`-clique or a blue `s`-clique.

This is the full generalization of the parent's `ramsey_recursion`, obtained by
strong induction on `r + s` with Pascal's identity closing the step.  It
subsumes every finite Ramsey-number upper bound, including the parent's
`R(4,k) ≤ C(k+2, 3)`. -/
theorem ramseyProp_erdos_szekeres (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    RamseyProp (Nat.choose (r + s - 2) (r - 1)) r s :=
  ramseyProp_erdos_szekeres_aux (r + s) r s le_rfl hr hs

/-- **Erdős–Szekeres stated through `ramseyUpperBound`.**  For `r, s ≥ 1`,
`ramseyUpperBound r s = C(r+s-2, r-1)` witnesses the Ramsey property, i.e.
`R(r,s) ≤ ramseyUpperBound r s`. -/
theorem ramseyProp_ramseyUpperBound (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    RamseyProp (ramseyUpperBound r s) r s := by
  have hpos : ¬ (r = 0 ∨ s = 0) := by omega
  rw [ramseyUpperBound, if_neg hpos]
  exact ramseyProp_erdos_szekeres r s hr hs

/-- **Consistency with the parent's specialization.**  The general bound recovers
`R(4,k) ≤ C(k+2, 3)`: `RamseyProp (C(k+2,3)) 4 k` for every `k ≥ 1`.  (The parent
`RamseyR4k` states the upper bound `ramseyUpperBound 4 k = C(k+2,3)` numerically;
here it is realized as an actual Ramsey guarantee.) -/
theorem ramseyProp_r4k (k : ℕ) (hk : 1 ≤ k) :
    RamseyProp (Nat.choose (k + 2) 3) 4 k := by
  have h := ramseyProp_erdos_szekeres 4 k (by norm_num) hk
  have hidx1 : 4 + k - 2 = k + 2 := by omega
  have hidx2 : 4 - 1 = 3 := by norm_num
  rw [hidx1, hidx2] at h
  exact h

end RamseyR4k
