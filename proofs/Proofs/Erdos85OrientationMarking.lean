import Proofs.Erdos85OrientedNonsquareMass
import Proofs.Erdos85EvenCycleOrientation
import Proofs.Erdos85NonresidueSectorConsequences

/-!
# The canonical orientation marking: `hodd` is eliminated

Mark a component *forward-oriented* when its labeled diagonal adjacency
block is translation invariant.  Odd components always are; even
components are forward- or reverse-oriented by the C4-free orientation
dichotomy (`Erdos85EvenCycleOrientation`).  The marking discharges both
hypotheses of the oriented nonsquare-mass machinery, so the nonsquare
branch conclusion — `p` divides the forward-oriented sector anchor
mass — holds at the exact even boundary with **no parity hypothesis on
any component length**.  Composed with the cyclotomic reduction bridge,
every nonresidue prime for `d-3` divides the oriented anchor mass.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {C : Type*} [Fintype C] [DecidableEq C]
variable {ℓ : C → ℕ} [∀ c, NeZero (ℓ c)] {p : ℕ}

/-- Equal integer adjacency-matrix entries give an adjacency
equivalence. -/
theorem adj_iff_of_adjMatrix_int_eq (G : SimpleGraph V)
    [DecidableRel G.Adj] {a b a' b' : V}
    (h : G.adjMatrix ℤ a b = G.adjMatrix ℤ a' b') :
    G.Adj a b ↔ G.Adj a' b' := by
  by_cases h1 : G.Adj a b <;> by_cases h2 : G.Adj a' b' <;>
    simp [SimpleGraph.adjMatrix_apply, h1, h2] at h ⊢

/-- The canonical forward-orientation marking: a component is forward
oriented when its labeled diagonal block is translation invariant. -/
def forwardOriented (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) : C → Prop :=
  fun c ↦ ∀ x y : ZMod (ℓ c),
    G.Adj (u c (x + 1)) (u c (y + 1)) ↔ G.Adj (u c x) (u c y)

noncomputable instance forwardOrientedDecidable
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) :
    DecidablePred (forwardOriented G u) := Classical.decPred _

/-- Forward-oriented components satisfy the forward shift relation —
by definition. -/
theorem forwardOriented_fwd (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) :
    ∀ c : C, p ∣ ℓ c → forwardOriented G u c →
      ∀ x y : ZMod (ℓ c),
        G.Adj (u c (x + 1)) (u c (y + 1)) ↔ G.Adj (u c x) (u c y) :=
  fun _ _ hoc x y ↦ hoc x y

/-- **The dichotomy discharge.**  In a C4-free graph whose defect
components are labeled cycles, a component that is not forward oriented
satisfies the reverse shift relation: odd components are always forward
(the classical circulant theorem), and even components obey the
C4-free even-cycle orientation dichotomy. -/
theorem forwardOriented_rev
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (hfree : ¬ containsC4 V G)
    (u : ∀ c : C, ZMod (ℓ c) → V) (hℓ3 : ∀ c, 3 ≤ ℓ c)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    (hcommZ : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ) :
    ∀ c : C, p ∣ ℓ c → ¬ forwardOriented G u c →
      ∀ x y : ZMod (ℓ c),
        G.Adj (u c (x + 1)) (u c (y - 1)) ↔ G.Adj (u c x) (u c y) := by
  intro c _ hoc
  have huc : Function.Injective (u c) := by
    intro a b hab
    exact sigma_mk_injective (β := fun c ↦ ZMod (ℓ c))
      (hbij.injective (a₁ := ⟨c, a⟩) (a₂ := ⟨c, b⟩) hab)
  rcases Nat.even_or_odd (ℓ c) with heven | hodd
  · rcases graph_equalEvenCycle_diagBlock_orientation (hℓ3 c) heven
      G D hfree (u c) huc hcommZ (huD c) with hfwd | hrev
    · exact absurd
        (fun x y ↦ adj_iff_of_adjMatrix_int_eq G (hfwd x y)) hoc
    · exact fun x y ↦ adj_iff_of_adjMatrix_int_eq G (hrev x y)
  · exact absurd
      (fun x y ↦ graph_equalOddCycle_diagBlock_adj_shift_iff (hℓ3 c)
        hodd G D (u c) huc hcommZ (huD c) x y) hoc

/-- **`hodd`-free nonsquare mass divisibility.**  At a C4-free labeled
cycle system with the Moore square identity, a nonsquare frequency
scalar forces `p` to divide the forward-oriented sector anchor mass —
no parity hypothesis on any component length. -/
theorem prime_dvd_orientedAnchorMass_forwardOriented_of_nonsquare
    {K : Type*} [Field K] [CharZero K] [NeZero p]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (hfree : ¬ containsC4 V G)
    (u : ∀ c : C, ZMod (ℓ c) → V) (hℓ3 : ∀ c, 3 ≤ ℓ c)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    (hcommZ : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    {d : ℕ}
    (hsqZ : G.adjMatrix ℤ * G.adjMatrix ℤ =
      ((d : ℤ) - 1) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V - D.adjMatrix ℤ)
    (hp : p.Prime) (hp2 : 2 < p) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hns : ¬ IsSquare ((d : K) - 1 - (ζ + ζ⁻¹))) :
    p ∣ orientedAnchorMass G u (forwardOriented G u) p :=
  prime_dvd_orientedAnchorMass_of_nonsquare G D u (forwardOriented G u)
    hℓ3 hbij huD hcommZ hsqZ (forwardOriented_fwd G u)
    (forwardOriented_rev G D hfree u hℓ3 hbij huD hcommZ)
    hp hp2 hζ hns

/-- **`hodd`-free nonresidue mass divisibility.**  Every prime `p ≥ 3`
with `d - 3` a quadratic nonresidue mod `p` divides the forward-oriented
sector anchor mass — via the cyclotomic reduction bridge, with no parity
hypothesis on any component length. -/
theorem prime_dvd_orientedAnchorMass_forwardOriented_of_nonresidue
    {K : Type*} [Field K] [CharZero K]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (hfree : ¬ containsC4 V G)
    (u : ∀ c : C, ZMod (ℓ c) → V) (hℓ3 : ∀ c, 3 ≤ ℓ c)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    (hcommZ : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    {d : ℕ} (hd : 3 ≤ d)
    (hsqZ : G.adjMatrix ℤ * G.adjMatrix ℤ =
      ((d : ℤ) - 1) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V - D.adjMatrix ℤ)
    (hp : p.Prime) (hp2 : 2 < p)
    [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hnr : ¬ IsSquare ((d - 3 : ℕ) : ZMod p)) :
    p ∣ orientedAnchorMass G u (forwardOriented G u) p := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hns : ¬ IsSquare ((d : K) - 1 - (ζ + ζ⁻¹)) :=
    not_isSquare_cyclotomic_frequencyScalar_of_nonresidue
      hζ (by omega) hd hnr
  exact prime_dvd_orientedAnchorMass_forwardOriented_of_nonsquare
    G D hfree u hℓ3 hbij huD hcommZ hsqZ hp hp2 hζ hns

end

end Erdos85
