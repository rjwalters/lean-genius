import Proofs.Erdos85ResidueSignedCount
import Proofs.Erdos85LargePrimeSectorClosure

/-!
# The all-selected squeeze at primes above the degree

When a prime `p > d` divides one defect-component order it divides all
of them, so under `hodd` the automatic parity of the boundary order
makes the selected count odd — the parity terminal's hypotheses are
free.  The mass floor then squeezes the component count against
`|V|/p`; when they meet, every component has order exactly `p` and the
configuration collapses into the closed equal-cycle branch.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An odd vertex count forces an odd number of components once every
component order is odd. -/
theorem odd_card_components_of_all_odd_orders
    (D : SimpleGraph V) [Fintype D.ConnectedComponent]
    (hcardV : Odd (Fintype.card V))
    (hallOdd : ∀ c : D.ConnectedComponent, Odd c.supp.ncard) :
    Odd (Fintype.card D.ConnectedComponent) := by
  have hsum := sum_connectedComponent_supp_ncard D
  have h2 : (∑ c : D.ConnectedComponent, c.supp.ncard) % 2 =
      (∑ c : D.ConnectedComponent, c.supp.ncard % 2) % 2 :=
    Finset.sum_nat_mod _ _ _
  have h3 : (∑ c : D.ConnectedComponent, c.supp.ncard % 2) =
      Fintype.card D.ConnectedComponent := by
    rw [Finset.sum_congr rfl fun c _ ↦ Nat.odd_iff.mp (hallOdd c),
      Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ]
  rw [Nat.odd_iff] at hcardV ⊢
  omega

/-- **Free selection at global sectors.**  If every component order is
divisible by `p` and odd, and the vertex count is odd, then the
`p`-divisible count is odd: the parity terminal's counting hypothesis
comes for free. -/
theorem countOdd_of_all_pDivisible
    (D : SimpleGraph V) [Fintype D.ConnectedComponent] {p : ℕ}
    (hall : ∀ c : D.ConnectedComponent, p ∣ c.supp.ncard)
    (hallOdd : ∀ c : D.ConnectedComponent, Odd c.supp.ncard)
    (hcardV : Odd (Fintype.card V)) :
    Odd (Finset.univ.filter (fun c : D.ConnectedComponent ↦
      p ∣ c.supp.ncard)).card := by
  classical
  have hfilter : Finset.univ.filter (fun c : D.ConnectedComponent ↦
      p ∣ c.supp.ncard) = Finset.univ :=
    Finset.filter_true_of_mem fun c _ ↦ hall c
  rw [hfilter, Finset.card_univ]
  exact odd_card_components_of_all_odd_orders D hcardV hallOdd

/-- **The pigeonhole collapse.**  If every component order is divisible
by `p` and the orders sum to exactly `p` times the component count, then
every order equals `p`. -/
theorem all_orders_eq_of_card_mul_eq_sum
    (D : SimpleGraph V) [Fintype D.ConnectedComponent] {p : ℕ}
    (hall : ∀ c : D.ConnectedComponent, p ∣ c.supp.ncard)
    (hsum : (∑ c : D.ConnectedComponent, c.supp.ncard) =
      p * Fintype.card D.ConnectedComponent) :
    ∀ c : D.ConnectedComponent, c.supp.ncard = p := by
  have hge : ∀ c : D.ConnectedComponent, p ≤ c.supp.ncard := fun c ↦
    Nat.le_of_dvd ((Set.ncard_pos (Set.toFinite _)).mpr
      c.nonempty_supp) (hall c)
  intro c
  by_contra hne
  have hlt : p < c.supp.ncard := lt_of_le_of_ne (hge c) (Ne.symm hne)
  have hstrict : (∑ _c : D.ConnectedComponent, p) <
      ∑ c : D.ConnectedComponent, c.supp.ncard :=
    Finset.sum_lt_sum (fun e _ ↦ hge e) ⟨c, Finset.mem_univ c, hlt⟩
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, mul_comm]
    at hstrict
  omega

/-- **Equal-cycle collapse at a saturated count.**  If every component
order is divisible by `p` and `p` times the component count equals the
vertex count, every component has order exactly `p` — the configuration
lies in the closed equal-cycle branch. -/
theorem all_orders_eq_prime_of_count
    (D : SimpleGraph V) [Fintype D.ConnectedComponent] {p : ℕ}
    (hall : ∀ c : D.ConnectedComponent, p ∣ c.supp.ncard)
    (hcount : p * Fintype.card D.ConnectedComponent = Fintype.card V) :
    ∀ c : D.ConnectedComponent, c.supp.ncard = p := by
  apply all_orders_eq_of_card_mul_eq_sum D hall
  rw [sum_connectedComponent_supp_ncard D, ← hcount]

end

end Erdos85
