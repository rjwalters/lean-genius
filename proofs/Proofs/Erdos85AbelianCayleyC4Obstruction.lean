import Proofs.Erdos85Problem

/-!
# The abelian Cayley parallelogram obstruction

The q=7 Boza witness uses a nonabelian semidirect group.  This is forced for
any Cayley construction of degree greater than two: in an abelian group, two
connection elements which are not mutual inverses create the 4-cycle
`1 -- a -- ab -- b -- 1`.
-/

namespace Erdos85

/-- The undirected Cayley graph belonging to an inverse-closed connection
predicate which omits the identity. -/
def invClosedCayleyGraph
    {Γ : Type*} [Group Γ]
    (S : Γ → Prop)
    (hinv : ∀ g, S g ↔ S g⁻¹)
    (hone : ¬ S 1) : SimpleGraph Γ where
  Adj x y := S (x⁻¹ * y)
  symm := ⟨by
    intro x y hxy
    have h := (hinv (x⁻¹ * y)).mp hxy
    simpa using h⟩
  loopless := ⟨by
    intro x hxx
    apply hone
    simpa using hxx⟩

/-- **Abelian Cayley parallelogram.**  Two distinct connection elements whose
product is not the identity force a 4-cycle.  In inverse-closed language,
these hypotheses say that `a` and `b` come from two different inverse pairs. -/
theorem commutative_invClosedCayley_containsC4_of_two_generators
    {Γ : Type*} [CommGroup Γ]
    (S : Γ → Prop)
    (hinv : ∀ g, S g ↔ S g⁻¹)
    (hone : ¬ S 1)
    {a b : Γ} (ha : S a) (hb : S b)
    (hab : a ≠ b) (hprod : a * b ≠ 1) :
    containsC4 Γ (invClosedCayleyGraph S hinv hone) := by
  let G := invClosedCayleyGraph S hinv hone
  have h1a : G.Adj 1 a := by
    change S (1⁻¹ * a)
    simpa using ha
  have haab : G.Adj a (a * b) := by
    change S (a⁻¹ * (a * b))
    simpa using hb
  have habb : G.Adj (a * b) b := by
    change S ((a * b)⁻¹ * b)
    have hai : S a⁻¹ := (hinv a).mp ha
    simpa [mul_comm] using hai
  have hb1 : G.Adj b 1 := by
    change S (b⁻¹ * 1)
    simpa using (hinv b).mp hb
  exact containsC4_of_rim h1a haab habb hb1
    (Ne.symm hprod) hab
    (G.ne_of_adj h1a).symm (G.ne_of_adj haab)
    (G.ne_of_adj hb1) (G.ne_of_adj habb).symm

/-- In a C4-free abelian Cayley graph, any two distinct connection elements
must be mutual inverses.  Thus an inverse-closed connection set has at most one
inverse pair (and consequently degree at most two in the finite case). -/
theorem connection_product_eq_one_of_commutative_invClosedCayley_not_containsC4
    {Γ : Type*} [CommGroup Γ]
    (S : Γ → Prop)
    (hinv : ∀ g, S g ↔ S g⁻¹)
    (hone : ¬ S 1)
    (hfree : ¬ containsC4 Γ (invClosedCayleyGraph S hinv hone))
    {a b : Γ} (ha : S a) (hb : S b) (hab : a ≠ b) :
    a * b = 1 := by
  by_contra hprod
  exact hfree
    (commutative_invClosedCayley_containsC4_of_two_generators
      S hinv hone ha hb hab hprod)

/-- **Finite capstone.**  An inverse-closed connection finset defining a
C4-free Cayley graph on an abelian group has cardinality at most two. -/
theorem card_connection_le_two_of_commutative_invClosedCayley_not_containsC4
    {Γ : Type*} [CommGroup Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone)) :
    A.card ≤ 2 := by
  by_contra hcard
  have hlt : 2 < A.card := by omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp hlt
  have habProd : a * b = 1 :=
    connection_product_eq_one_of_commutative_invClosedCayley_not_containsC4
      (· ∈ A) hinv hone hfree ha hb hab
  have hacProd : a * c = 1 :=
    connection_product_eq_one_of_commutative_invClosedCayley_not_containsC4
      (· ∈ A) hinv hone hfree ha hc hac
  have hbInv : b = a⁻¹ := eq_inv_of_mul_eq_one_right habProd
  have hcInv : c = a⁻¹ := eq_inv_of_mul_eq_one_right hacProd
  exact hbc (hbInv.trans hcInv.symm)

end Erdos85
