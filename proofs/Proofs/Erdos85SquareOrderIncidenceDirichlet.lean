import Proofs.Erdos85SquareOrderDefectComponentBalance

/-!
# Dirichlet energy of square-order high incidence

The defect equation `(D+I)k=h1` and the degree law
`deg_D+k=d-1` turn variation of the high-incidence function into an exact
third-moment slack.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Abstract Dirichlet identity for a finite graph sector closed under
adjacency and satisfying the square-order incidence and degree equations. -/
theorem defectIncidence_orientedDirichlet_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (S : Finset V) (k : V → ℕ) (d h : ℕ)
    (hd : 1 ≤ d)
    (hclosed : ∀ ⦃x y : V⦄, x ∈ S → D.Adj x y → y ∈ S)
    (hpoint : ∀ x ∈ S,
      (∑ y ∈ D.neighborFinset x, k y) + k x = h)
    (hdegree : ∀ x ∈ S, D.degree x + k x = d - 1) :
    (∑ x ∈ S, ∑ y ∈ D.neighborFinset x,
        ((k x : ℤ) - k y) ^ 2) =
      2 * ∑ x ∈ S,
        ((d : ℤ) * (k x : ℤ) ^ 2 - (k x : ℤ) ^ 3 -
          (h : ℤ) * k x) := by
  classical
  have hswapNat :
      (∑ x ∈ S, ∑ y ∈ D.neighborFinset x, k y * k y) =
        ∑ x ∈ S, (k x * k x) * D.degree x :=
    sum_closed_neighbor_weights D S (fun x => k x * k x) hclosed
  have hswap :
      (∑ x ∈ S, ∑ y ∈ D.neighborFinset x, (k y : ℤ) ^ 2) =
        ∑ x ∈ S, (k x : ℤ) ^ 2 * D.degree x := by
    have hswapZ := congrArg (fun n : ℕ => (n : ℤ)) hswapNat
    push_cast at hswapZ
    simpa [pow_two] using hswapZ
  calc
    (∑ x ∈ S, ∑ y ∈ D.neighborFinset x,
        ((k x : ℤ) - k y) ^ 2) =
        ∑ x ∈ S, ((D.degree x : ℤ) * (k x : ℤ) ^ 2 +
          (∑ y ∈ D.neighborFinset x, (k y : ℤ) ^ 2) -
          2 * (k x : ℤ) *
            (∑ y ∈ D.neighborFinset x, (k y : ℤ))) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp_rw [sub_sq]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul]
      rw [D.card_neighborFinset_eq_degree]
      rw [Finset.mul_sum]
      ring
    _ = 2 * ∑ x ∈ S, ((D.degree x : ℤ) * (k x : ℤ) ^ 2 -
          (k x : ℤ) *
            (∑ y ∈ D.neighborFinset x, (k y : ℤ))) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hswap]
      have hcomm :
          (∑ x ∈ S, (k x : ℤ) ^ 2 * D.degree x) =
            ∑ x ∈ S, (D.degree x : ℤ) * (k x : ℤ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      have htwo :
          (∑ x ∈ S, 2 * (k x : ℤ) *
              (∑ y ∈ D.neighborFinset x, (k y : ℤ))) =
            2 * ∑ x ∈ S, (k x : ℤ) *
              (∑ y ∈ D.neighborFinset x, (k y : ℤ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hcomm, htwo, Finset.sum_sub_distrib]
      ring
    _ = 2 * ∑ x ∈ S,
        ((d : ℤ) * (k x : ℤ) ^ 2 - (k x : ℤ) ^ 3 -
          (h : ℤ) * k x) := by
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      have hp := hpoint x hx
      have hdg := hdegree x hx
      have hpZ :
          ((∑ y ∈ D.neighborFinset x, k y : ℕ) : ℤ) + k x = h := by
        exact_mod_cast hp
      have hdgZ : (D.degree x : ℤ) + k x = (d : ℤ) - 1 := by
        have hdgZ' : (D.degree x : ℤ) + k x = ((d - 1 : ℕ) : ℤ) := by
          exact_mod_cast hdg
        rw [Nat.cast_sub hd] at hdgZ'
        simpa using hdgZ'
      have hsumZ :
          (∑ y ∈ D.neighborFinset x, (k y : ℤ)) =
            ((∑ y ∈ D.neighborFinset x, k y : ℕ) : ℤ) := by norm_cast
      rw [hsumZ]
      nlinarith

/-- With the square-order first two incidence moments inserted, the oriented
Dirichlet energy is exactly twice the third-moment slack. -/
theorem defectIncidence_orientedDirichlet_eq_thirdMomentSlack
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (S : Finset V) (k : V → ℕ) (d h : ℕ)
    (hd : 1 ≤ d)
    (hclosed : ∀ ⦃x y : V⦄, x ∈ S → D.Adj x y → y ∈ S)
    (hpoint : ∀ x ∈ S,
      (∑ y ∈ D.neighborFinset x, k y) + k x = h)
    (hdegree : ∀ x ∈ S, D.degree x + k x = d - 1)
    (hfirst : (∑ x ∈ S, k x) = (d + 1) * h)
    (hsecond : (∑ x ∈ S, (k x) ^ 2) = h * (h + d)) :
    (∑ x ∈ S, ∑ y ∈ D.neighborFinset x,
        ((k x : ℤ) - k y) ^ 2) =
      2 * ((h : ℤ) * ((d : ℤ) ^ 2 - h) -
        ∑ x ∈ S, (k x : ℤ) ^ 3) := by
  rw [defectIncidence_orientedDirichlet_eq
    D S k d h hd hclosed hpoint hdegree]
  have hfirstZ : (∑ x ∈ S, (k x : ℤ)) = ((d + 1 : ℕ) : ℤ) * h := by
    exact_mod_cast hfirst
  have hsecondZ : (∑ x ∈ S, (k x : ℤ) ^ 2) =
      (h : ℤ) * ((h + d : ℕ) : ℤ) := by
    have hz := congrArg (fun n : ℕ => (n : ℤ)) hsecond
    push_cast at hz
    simpa using hz
  congr 1
  simp_rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hfirstZ, hsecondZ]
  push_cast
  ring

end

end Erdos85
