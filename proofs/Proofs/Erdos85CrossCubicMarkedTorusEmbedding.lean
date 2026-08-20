import Proofs.Erdos85CrossCubicMassUpperBipartite

/-!
# The sharp cross marked graph lives on diagonal steps of the C8 torus

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The second-shore coordinate paired with the canonical first coordinate
of a shore-type-one edge. -/
noncomputable def shoreTypeOneEdgeSecondCoordinate
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u v : ZMod 8 → V)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j)
    (a : shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 1) : ZMod 8 :=
  Classical.choose
    (shoreTypeOneEdgeFirstCoordinate_support R u v hcover a)

/-- Both canonical coordinates recover the support of the cross edge. -/
theorem shoreTypeOneEdgeCoordinates_support
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u v : ZMod 8 → V)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j)
    (a : shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 1) :
    a.1.1.toFinset =
      {u (shoreTypeOneEdgeFirstCoordinate R u v hcover a),
       v (shoreTypeOneEdgeSecondCoordinate R u v hcover a)} := by
  exact Classical.choose_spec
    (shoreTypeOneEdgeFirstCoordinate_support R u v hcover a)

/-- Injective, disjoint shore coordinates make the chosen second coordinate
equal to the second coordinate in any displayed support representation. -/
theorem shoreTypeOneEdgeSecondCoordinate_eq_of_support
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u v : ZMod 8 → V)
    (hvinj : Function.Injective v)
    (hdisj : ∀ i j, u i ≠ v j)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j)
    (a : shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 1)
    (i j : ZMod 8) (ha : a.1.1.toFinset = {u i, v j}) :
    shoreTypeOneEdgeSecondCoordinate R u v hcover a = j := by
  have hj : v j ∈ a.1.1.toFinset := by rw [ha]; simp
  rw [shoreTypeOneEdgeCoordinates_support R u v hcover a] at hj
  rcases Finset.mem_insert.mp hj with hj | hj
  · exact False.elim (hdisj _ _ hj.symm)
  · exact (hvinj (Finset.mem_singleton.mp hj)).symm

/-- Under the uniform sharp-row bound, every marked adjacency changes both
canonical shore coordinates by one step.  Thus the actual marked graph is a
subgraph of the diagonal-step graph on `ZMod 8 × ZMod 8`. -/
theorem h305_cross_mass_le_550_valueFiveGraph_coordinate_steps
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hHreg : ∀ x, H.degree x = 2) (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hv : ∀ z, H.neighborFinset (v z) = {v (z - 1), v (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (hmodeu : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hmodev : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v)
    (hzeroUV : ∀ k l,
      Fintype.card {p : H.Walk (u k) (v l) | p.length = 3} = 0)
    (hzeroVU : ∀ k l,
      Fintype.card {p : H.Walk (v l) (u k) | p.length = 3} = 0)
    (hupper : let U := (Finset.univ : Finset (ZMod 8)).image u
      let S := shoreTypeEdgeFinset R U 1
      ∀ a ∈ S, (∑ b ∈ cubicResidualEdgeFinset R Cedge a,
        (residualFiberCubicWalkCount R Cedge a b) ^ 2) ≤ 550)
    ⦃a b : shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 1⦄
    (hab : (h305CrossCubicValueFiveGraph R Cedge
      ((Finset.univ : Finset (ZMod 8)).image u)).Adj a b) :
    (shoreTypeOneEdgeFirstCoordinate R u v hcover b =
        shoreTypeOneEdgeFirstCoordinate R u v hcover a - 1 ∨
      shoreTypeOneEdgeFirstCoordinate R u v hcover b =
        shoreTypeOneEdgeFirstCoordinate R u v hcover a + 1) ∧
    (shoreTypeOneEdgeSecondCoordinate R u v hcover b =
        shoreTypeOneEdgeSecondCoordinate R u v hcover a - 1 ∨
      shoreTypeOneEdgeSecondCoordinate R u v hcover b =
        shoreTypeOneEdgeSecondCoordinate R u v hcover a + 1) := by
  classical
  dsimp only at hupper
  let i := shoreTypeOneEdgeFirstCoordinate R u v hcover a
  let j := shoreTypeOneEdgeSecondCoordinate R u v hcover a
  have ha := shoreTypeOneEdgeCoordinates_support R u v hcover a
  have hbM : b.1 ∈ cubicValueFiveEdgeFinset R Cedge a.1 := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hab.2⟩
  have horient := h305_cross_mass_le_550_valueFiveEdge_orientation
    H R Cedge hservice hfree hHreg hRreg hCreg u v huinj hvinj hu hv
      hdisj hcover hmodeu hmodev hzeroUV hzeroVU a.1 i j ha
        (hupper a.1 a.2)
  rcases horient with ⟨b₀, b₁, hM, hb₀, hb₁⟩ |
      ⟨b₀, b₁, hM, hb₀, hb₁⟩
  all_goals
    rw [hM] at hbM
    rcases Finset.mem_insert.mp hbM with hb | hb
    · subst b₀
      constructor
      · left
        exact shoreTypeOneEdgeFirstCoordinate_eq_of_support
          R u v huinj hdisj hcover b (i - 1) _ hb₀
      · first
        | left; exact shoreTypeOneEdgeSecondCoordinate_eq_of_support
            R u v hvinj hdisj hcover b _ (j - 1) hb₀
        | right; exact shoreTypeOneEdgeSecondCoordinate_eq_of_support
            R u v hvinj hdisj hcover b _ (j + 1) hb₀
    · have hb' : b.1 = b₁ := Finset.mem_singleton.mp hb
      subst b₁
      constructor
      · right
        exact shoreTypeOneEdgeFirstCoordinate_eq_of_support
          R u v huinj hdisj hcover b (i + 1) _ hb₁
      · first
        | right; exact shoreTypeOneEdgeSecondCoordinate_eq_of_support
            R u v hvinj hdisj hcover b _ (j + 1) hb₁
        | left; exact shoreTypeOneEdgeSecondCoordinate_eq_of_support
            R u v hvinj hdisj hcover b _ (j - 1) hb₁

/-- The two coordinate steps retain the stronger straight-versus-crossed
correlation from the local sharp orientation theorem. -/
theorem h305_cross_mass_le_550_valueFiveGraph_coordinate_orientation
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hHreg : ∀ x, H.degree x = 2) (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hv : ∀ z, H.neighborFinset (v z) = {v (z - 1), v (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (hmodeu : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hmodev : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v)
    (hzeroUV : ∀ k l,
      Fintype.card {p : H.Walk (u k) (v l) | p.length = 3} = 0)
    (hzeroVU : ∀ k l,
      Fintype.card {p : H.Walk (v l) (u k) | p.length = 3} = 0)
    (hupper : let U := (Finset.univ : Finset (ZMod 8)).image u
      let S := shoreTypeEdgeFinset R U 1
      ∀ a ∈ S, (∑ b ∈ cubicResidualEdgeFinset R Cedge a,
        (residualFiberCubicWalkCount R Cedge a b) ^ 2) ≤ 550)
    ⦃a b : shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 1⦄
    (hab : (h305CrossCubicValueFiveGraph R Cedge
      ((Finset.univ : Finset (ZMod 8)).image u)).Adj a b) :
    (((shoreTypeOneEdgeFirstCoordinate R u v hcover b =
          shoreTypeOneEdgeFirstCoordinate R u v hcover a - 1) ∧
        shoreTypeOneEdgeSecondCoordinate R u v hcover b =
          shoreTypeOneEdgeSecondCoordinate R u v hcover a - 1) ∨
      ((shoreTypeOneEdgeFirstCoordinate R u v hcover b =
          shoreTypeOneEdgeFirstCoordinate R u v hcover a + 1) ∧
        shoreTypeOneEdgeSecondCoordinate R u v hcover b =
          shoreTypeOneEdgeSecondCoordinate R u v hcover a + 1)) ∨
    (((shoreTypeOneEdgeFirstCoordinate R u v hcover b =
          shoreTypeOneEdgeFirstCoordinate R u v hcover a - 1) ∧
        shoreTypeOneEdgeSecondCoordinate R u v hcover b =
          shoreTypeOneEdgeSecondCoordinate R u v hcover a + 1) ∨
      ((shoreTypeOneEdgeFirstCoordinate R u v hcover b =
          shoreTypeOneEdgeFirstCoordinate R u v hcover a + 1) ∧
        shoreTypeOneEdgeSecondCoordinate R u v hcover b =
          shoreTypeOneEdgeSecondCoordinate R u v hcover a - 1)) := by
  classical
  dsimp only at hupper
  let i := shoreTypeOneEdgeFirstCoordinate R u v hcover a
  let j := shoreTypeOneEdgeSecondCoordinate R u v hcover a
  have ha := shoreTypeOneEdgeCoordinates_support R u v hcover a
  have hbM : b.1 ∈ cubicValueFiveEdgeFinset R Cedge a.1 := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hab.2⟩
  have horient := h305_cross_mass_le_550_valueFiveEdge_orientation
    H R Cedge hservice hfree hHreg hRreg hCreg u v huinj hvinj hu hv
      hdisj hcover hmodeu hmodev hzeroUV hzeroVU a.1 i j ha
        (hupper a.1 a.2)
  rcases horient with ⟨b₀, b₁, hM, hb₀, hb₁⟩ |
      ⟨b₀, b₁, hM, hb₀, hb₁⟩
  · rw [hM] at hbM
    rcases Finset.mem_insert.mp hbM with hb | hb
    · left; left
      subst b₀
      exact ⟨shoreTypeOneEdgeFirstCoordinate_eq_of_support
          R u v huinj hdisj hcover b (i - 1) _ hb₀,
        shoreTypeOneEdgeSecondCoordinate_eq_of_support
          R u v hvinj hdisj hcover b _ (j - 1) hb₀⟩
    · left; right
      have hb' : b.1 = b₁ := Finset.mem_singleton.mp hb
      subst b₁
      exact ⟨shoreTypeOneEdgeFirstCoordinate_eq_of_support
          R u v huinj hdisj hcover b (i + 1) _ hb₁,
        shoreTypeOneEdgeSecondCoordinate_eq_of_support
          R u v hvinj hdisj hcover b _ (j + 1) hb₁⟩
  · rw [hM] at hbM
    rcases Finset.mem_insert.mp hbM with hb | hb
    · right; left
      subst b₀
      exact ⟨shoreTypeOneEdgeFirstCoordinate_eq_of_support
          R u v huinj hdisj hcover b (i - 1) _ hb₀,
        shoreTypeOneEdgeSecondCoordinate_eq_of_support
          R u v hvinj hdisj hcover b _ (j + 1) hb₀⟩
    · right; right
      have hb' : b.1 = b₁ := Finset.mem_singleton.mp hb
      subst b₁
      exact ⟨shoreTypeOneEdgeFirstCoordinate_eq_of_support
          R u v huinj hdisj hcover b (i + 1) _ hb₁,
        shoreTypeOneEdgeSecondCoordinate_eq_of_support
          R u v hvinj hdisj hcover b _ (j - 1) hb₁⟩

end

end Erdos85

#print axioms Erdos85.shoreTypeOneEdgeCoordinates_support
#print axioms Erdos85.shoreTypeOneEdgeSecondCoordinate_eq_of_support
#print axioms Erdos85.h305_cross_mass_le_550_valueFiveGraph_coordinate_steps
#print axioms
  Erdos85.h305_cross_mass_le_550_valueFiveGraph_coordinate_orientation
