import Proofs.Erdos85ComponentLocalObstruction
import Proofs.Erdos85OddBoundaryClean

/-!
# Componentwise bridge to the regular excess band

A connected component below the next asymmetric Moore layer is regular and
has order `d(d-1)+2+e` with `e ≤ d-3`.  This clean form avoids the finite
certificates used by the sharper all-parity second-strict Moore bound.  In
odd degree, parity recovers the familiar `+3` boundary separately.
-/

namespace Erdos85

open SimpleGraph

/-- Any component smaller than `d²` lies in the regular second-order excess
band. -/
theorem connectedComponent_regular_excess_data
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d)
    (hmin : d ≤ G.minDegree) (c : G.ConnectedComponent)
    (hsmall : c.supp.ncard < d * d) :
    ∃ e : ℕ, e ≤ d - 3 ∧
      c.supp.ncard = d * (d - 1) + 2 + e ∧
      ∀ x : c.supp, (G.induce c.supp).degree x = d := by
  classical
  let H := G.induce c.supp
  letI : Nonempty c.supp := Set.nonempty_coe_sort.mpr c.nonempty_supp
  have hfreeH : ¬ containsC4 c.supp H :=
    not_containsC4_induce_connectedComponent G hfree c
  have hminH : d ≤ H.minDegree := by
    apply H.le_minDegree_of_forall_le_degree
    intro x
    rw [degree_induce_connectedComponent_supp G c x]
    exact hmin.trans (G.minDegree_le_degree x.1)
  have hcardH : Fintype.card c.supp = c.supp.ncard := by
    simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp
  have hbelow : Fintype.card c.supp < (d + 1) * (d - 1) + 1 := by
    rw [hcardH]
    have hnext : (d + 1) * (d - 1) + 1 = d * d := by
      obtain ⟨a, rfl⟩ : ∃ a, d = a + 3 := ⟨d - 3, by omega⟩
      norm_num
      ring
    rwa [hnext]
  have hreg : ∀ x : c.supp, H.degree x = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      H hfreeH (by omega) hminH hbelow
  have hlower : d * (d - 1) + 2 ≤ c.supp.ncard :=
    connectedComponent_clean_moore_bound G hfree hd hmin c
  have hgap : d * d = d * (d - 1) + 2 + (d - 2) := by
    obtain ⟨a, rfl⟩ : ∃ a, d = a + 3 := ⟨d - 3, by omega⟩
    have h1 : a + 3 - 1 = a + 2 := by omega
    have h2 : a + 3 - 2 = a + 1 := by omega
    rw [h1, h2]
    ring
  let e := c.supp.ncard - (d * (d - 1) + 2)
  refine ⟨e, ?_, ?_, hreg⟩
  · dsimp [e]
    omega
  · dsimp [e]
    omega

/-- In odd degree the clean symbolic boundary theorem removes the first two
orders as well: a small component starts at `d(d-1)+4`. -/
theorem connectedComponent_regular_excess_data_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (hodd : Odd d)
    (hmin : d ≤ G.minDegree) (c : G.ConnectedComponent)
    (hsmall : c.supp.ncard < d * d) :
    ∃ e : ℕ, e ≤ d - 5 ∧
      c.supp.ncard = d * (d - 1) + 4 + e ∧
      ∀ x : c.supp, (G.induce c.supp).degree x = d := by
  classical
  let H := G.induce c.supp
  letI : Nonempty c.supp := Set.nonempty_coe_sort.mpr c.nonempty_supp
  have hfreeH : ¬ containsC4 c.supp H :=
    not_containsC4_induce_connectedComponent G hfree c
  have hminH : d ≤ H.minDegree := by
    apply H.le_minDegree_of_forall_le_degree
    intro x
    rw [degree_induce_connectedComponent_supp G c x]
    exact hmin.trans (G.minDegree_le_degree x.1)
  have hcardH : Fintype.card c.supp = c.supp.ncard := by
    simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp
  have hbelow : Fintype.card c.supp < (d + 1) * (d - 1) + 1 := by
    rw [hcardH]
    have hnext : (d + 1) * (d - 1) + 1 = d * d := by
      obtain ⟨a, rfl⟩ : ∃ a, d = a + 4 := ⟨d - 4, by omega⟩
      norm_num
      ring
    rwa [hnext]
  have hreg : ∀ x : c.supp, H.degree x = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      H hfreeH (by omega) hminH hbelow
  have hlowerCard : d * (d - 1) + 4 ≤ Fintype.card c.supp :=
    mul_pred_add_four_le_card_of_c4Free_minDegree_odd_clean
      H hd hodd hminH hfreeH
  have hlower : d * (d - 1) + 4 ≤ c.supp.ncard := by
    rwa [hcardH] at hlowerCard
  have hgap : d * d = d * (d - 1) + 4 + (d - 4) := by
    obtain ⟨a, rfl⟩ : ∃ a, d = a + 4 := ⟨d - 4, by omega⟩
    have h1 : a + 4 - 1 = a + 3 := by omega
    have h2 : a + 4 - 4 = a := by omega
    rw [h1, h2]
    ring
  let e := c.supp.ncard - (d * (d - 1) + 4)
  refine ⟨e, ?_, ?_, hreg⟩
  · dsimp [e]
    omega
  · dsimp [e]
    omega

/-- Plateau-core form of the componentwise boundary bridge.  Every proper
small component is regular, lies in the bounded excess band, and is itself
one-step nonextendable. -/
theorem C4PlateauCore.exists_small_component_boundary_data
    {m d : ℕ} (hm : 4 ≤ m) (hd : 3 ≤ d)
    (hcore : C4PlateauCore m d) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧ ¬ containsC4 (Fin m) G ∧
      ∀ c : G.ConnectedComponent, c.supp.ncard < d * d →
        ∃ e : ℕ, e ≤ d - 3 ∧
          c.supp.ncard = d * (d - 1) + 2 + e ∧
          (∀ x : c.supp, (G.induce c.supp).degree x = d) ∧
          (c.supp.ncard < m →
            ¬ C4FreeMinDegreeWitness (c.supp.ncard + 1) d) := by
  rcases hcore with ⟨G, hdec, hmin, hfree, hcover, hnext⟩
  letI : DecidableRel G.Adj := hdec
  refine ⟨G, hdec, hmin, hfree, ?_⟩
  intro c hc
  obtain ⟨e, he, hsize, hreg⟩ :=
    connectedComponent_regular_excess_data G hfree hd hmin.ge c hc
  refine ⟨e, he, hsize, hreg, ?_⟩
  intro hproper hext
  have hglobal := c4FreeMinDegreeWitness_succ_of_component_extension
    G hfree hmin.ge c (by simpa using hproper) hext
  have hglobal' : C4FreeMinDegreeWitness (m + 1) d := by
    simpa using hglobal
  rcases hglobal' with ⟨H, hHdec, hHmin, hHfree⟩
  exact hHfree (hnext H hHdec hHmin)

end Erdos85
