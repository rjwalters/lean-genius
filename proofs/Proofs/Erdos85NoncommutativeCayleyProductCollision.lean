import Proofs.Erdos85AbelianCayleyC4Obstruction

/-!
# The noncommutative Cayley product-collision obstruction

Node: B.2 / `GAP B-EXIST`.  The abelian parallelogram obstruction is the
commutative shadow of a more general Sidon law.  In any inverse-closed Cayley
graph, a collision between two non-backtracking length-two words with
different first letters produces the four-cycle
`1 -- a -- a*b = c*d -- c -- 1`.

Thus every viable nonabelian odd-order Cayley construction must make the
ordered product map injective after the unavoidable inverse/backtracking
identifications.
-/

namespace Erdos85

/-- A collision `a * b = c * d` between two non-backtracking connection
words with different first letters gives a four-cycle.  No commutativity is
used. -/
theorem invClosedCayley_containsC4_of_product_collision
    {Γ : Type*} [Group Γ]
    (S : Γ → Prop)
    (hinv : ∀ g, S g ↔ S g⁻¹)
    (hone : ¬ S 1)
    {a b c d : Γ}
    (ha : S a) (hb : S b) (hc : S c) (hd : S d)
    (hac : a ≠ c) (hprod : a * b ≠ 1)
    (hcollision : a * b = c * d) :
    containsC4 Γ (invClosedCayleyGraph S hinv hone) := by
  let G := invClosedCayleyGraph S hinv hone
  have h1a : G.Adj 1 a := by
    change S (1⁻¹ * a)
    simpa using ha
  have hap : G.Adj a (a * b) := by
    change S (a⁻¹ * (a * b))
    simpa using hb
  have hpc : G.Adj (a * b) c := by
    change S ((a * b)⁻¹ * c)
    have hdi : S d⁻¹ := (hinv d).mp hd
    rw [hcollision]
    simpa using hdi
  have hc1 : G.Adj c 1 := by
    change S (c⁻¹ * 1)
    simpa using (hinv c).mp hc
  exact containsC4_of_rim h1a hap hpc hc1
    (Ne.symm hprod) hac
    (G.ne_of_adj h1a).symm (G.ne_of_adj hap)
    (G.ne_of_adj hc1) (G.ne_of_adj hpc).symm

/-- **Noncommutative Sidon law.**  In a C4-free inverse-closed Cayley graph,
two non-backtracking length-two connection words with different first letters
have different products. -/
theorem connection_product_ne_of_invClosedCayley_not_containsC4
    {Γ : Type*} [Group Γ]
    (S : Γ → Prop)
    (hinv : ∀ g, S g ↔ S g⁻¹)
    (hone : ¬ S 1)
    (hfree : ¬ containsC4 Γ (invClosedCayleyGraph S hinv hone))
    {a b c d : Γ}
    (ha : S a) (hb : S b) (hc : S c) (hd : S d)
    (hac : a ≠ c) (hprod : a * b ≠ 1) :
    a * b ≠ c * d := by
  intro hcollision
  exact hfree (invClosedCayley_containsC4_of_product_collision
    S hinv hone ha hb hc hd hac hprod hcollision)

end Erdos85

#print axioms Erdos85.invClosedCayley_containsC4_of_product_collision
#print axioms Erdos85.connection_product_ne_of_invClosedCayley_not_containsC4
