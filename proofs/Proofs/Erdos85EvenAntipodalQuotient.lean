import Proofs.Erdos85EvenFirstOrderAntipodal

/-!
# The general even first-order antipodal quotient

This module turns the one-regular antipodal graph into its canonical
fixed-point-free involution.  It is the first step toward constructing the
integral quotient matrix satisfying `Q²=(d-2)I+2J`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (antipodalGraph G).Adj]
variable (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) (hdeven : Even d)
variable (hmin : d ≤ G.minDegree)
variable (hcard : Fintype.card V = d * (d - 1) + 2)

/-- The unique antipodal neighbor of a vertex in the even first-order
template. -/
def firstOrderEvenAntipode (x : V) : V :=
  (degree_eq_one_iff_existsUnique_adj.mp
    (antipodalGraph_degree_eq_one_of_firstOrder_even
      G hfree hd hdeven hmin hcard x)).choose

private abbrev p := firstOrderEvenAntipode G hfree hd hdeven hmin hcard

/-- The selected vertex is adjacent in the antipodal matching. -/
theorem firstOrderEvenAntipode_mem (x : V) :
    p G hfree hd hdeven hmin hcard x ∈ antipodalNeighbors G x := by
  exact (degree_eq_one_iff_existsUnique_adj.mp
    (antipodalGraph_degree_eq_one_of_firstOrder_even
      G hfree hd hdeven hmin hcard x)).choose_spec.1

/-- Characterization by uniqueness in the antipodal matching. -/
theorem firstOrderEvenAntipode_eq_of_mem (x y : V)
    (hy : y ∈ antipodalNeighbors G x) :
    y = p G hfree hd hdeven hmin hcard x := by
  have hspec := (degree_eq_one_iff_existsUnique_adj.mp
    (antipodalGraph_degree_eq_one_of_firstOrder_even
      G hfree hd hdeven hmin hcard x)).choose_spec
  exact hspec.2 y hy

/-- The antipode is distinct and nonadjacent, and the pair has no common
neighbor. -/
theorem firstOrderEvenAntipode_spec (x : V) :
    p G hfree hd hdeven hmin hcard x ≠ x ∧
    ¬ G.Adj x (p G hfree hd hdeven hmin hcard x) ∧
    (G.neighborFinset x ∩
      G.neighborFinset (p G hfree hd hdeven hmin hcard x)).card = 0 := by
  exact (mem_antipodalNeighbors G x
    (p G hfree hd hdeven hmin hcard x)).mp
      (firstOrderEvenAntipode_mem G hfree hd hdeven hmin hcard x)

/-- The antipode map is a fixed-point-free involution. -/
theorem firstOrderEvenAntipode_involutive (x : V) :
    p G hfree hd hdeven hmin hcard
      (p G hfree hd hdeven hmin hcard x) = x := by
  symm
  apply firstOrderEvenAntipode_eq_of_mem G hfree hd hdeven hmin hcard
  exact (mem_antipodalNeighbors_comm G x
    (p G hfree hd hdeven hmin hcard x)).mp
      (firstOrderEvenAntipode_mem G hfree hd hdeven hmin hcard x)

/-- Membership in the antipodal fiber is equality with the selected
antipode. -/
theorem mem_antipodalNeighbors_iff_eq_firstOrderEvenAntipode (x y : V) :
    y ∈ antipodalNeighbors G x ↔
      y = p G hfree hd hdeven hmin hcard x := by
  constructor
  · exact firstOrderEvenAntipode_eq_of_mem G hfree hd hdeven hmin hcard x y
  · rintro rfl
    exact firstOrderEvenAntipode_mem G hfree hd hdeven hmin hcard x

/-- The matching neighborhood is literally the singleton containing the
selected antipode. -/
theorem antipodalGraph_neighborFinset_eq_singleton (x : V) :
    (antipodalGraph G).neighborFinset x =
      {p G hfree hd hdeven hmin hcard x} := by
  ext y
  rw [antipodalGraph_neighborFinset]
  simp [mem_antipodalNeighbors_iff_eq_firstOrderEvenAntipode
    G hfree hd hdeven hmin hcard]

/-- Right multiplication by the antipodal matching permutes columns by the
antipode. -/
theorem adjMatrix_mul_antipodalGraph_apply (x y : V) :
    (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) x y =
      G.adjMatrix ℤ x (p G hfree hd hdeven hmin hcard y) := by
  rw [(antipodalGraph G).mul_adjMatrix_apply,
    antipodalGraph_neighborFinset_eq_singleton G hfree hd hdeven hmin hcard]
  simp only [SimpleGraph.adjMatrix_apply, Finset.sum_boole,
    Finset.filter_singleton]
  by_cases hxy : G.Adj x (p G hfree hd hdeven hmin hcard y) <;>
    simp [hxy]

/-- Left multiplication by the matching permutes rows by the antipode. -/
theorem antipodalGraph_mul_adjMatrix_apply (x y : V) :
    ((antipodalGraph G).adjMatrix ℤ * G.adjMatrix ℤ) x y =
      G.adjMatrix ℤ (p G hfree hd hdeven hmin hcard x) y := by
  rw [G.mul_adjMatrix_apply]
  simp only [SimpleGraph.adjMatrix_apply]
  rw [Finset.sum_boole]
  have hfilt : (G.neighborFinset y).filter
      (fun z => (antipodalGraph G).Adj x z) =
      if G.Adj (p G hfree hd hdeven hmin hcard x) y then
        {p G hfree hd hdeven hmin hcard x} else ∅ := by
    ext z
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset,
      show (antipodalGraph G).Adj x z ↔
        z = p G hfree hd hdeven hmin hcard x from
          mem_antipodalNeighbors_iff_eq_firstOrderEvenAntipode
            G hfree hd hdeven hmin hcard x z]
    by_cases hxy : G.Adj (p G hfree hd hdeven hmin hcard x) y
    · rw [if_pos hxy]
      simp only [Finset.mem_singleton]
      constructor
      · exact fun hz => hz.2
      · intro hz
        subst z
        exact ⟨hxy.symm, rfl⟩
    · rw [if_neg hxy]
      simp only [Finset.notMem_empty, iff_false]
      rintro ⟨hyz, hz⟩
      subst z
      exact hxy hyz.symm
  rw [hfilt]
  by_cases hxy : G.Adj (p G hfree hd hdeven hmin hcard x) y
  · simp [hxy]
  · simp [hxy]

/-- The canonical antipode is an automorphism of the original graph. -/
theorem firstOrderEvenAntipode_adj_iff (x y : V) :
    G.Adj (p G hfree hd hdeven hmin hcard x)
        (p G hfree hd hdeven hmin hcard y) ↔
      G.Adj x y := by
  have hcomm := adjMatrix_comm_antipodalGraph_of_firstOrder_even
    G hfree hd hdeven hmin hcard
  have hentry := congr_fun₂ hcomm x
    (p G hfree hd hdeven hmin hcard y)
  have hleft :
      (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) x
          (p G hfree hd hdeven hmin hcard y) = G.adjMatrix ℤ x y := by
    rw [adjMatrix_mul_antipodalGraph_apply G hfree hd hdeven hmin hcard,
      firstOrderEvenAntipode_involutive G hfree hd hdeven hmin hcard]
  have hright :
      ((antipodalGraph G).adjMatrix ℤ * G.adjMatrix ℤ) x
          (p G hfree hd hdeven hmin hcard y) =
        G.adjMatrix ℤ (p G hfree hd hdeven hmin hcard x)
          (p G hfree hd hdeven hmin hcard y) :=
    antipodalGraph_mul_adjMatrix_apply G hfree hd hdeven hmin hcard _ _
  rw [hleft, hright] at hentry
  by_cases hxy : G.Adj x y <;>
    by_cases hpq : G.Adj (p G hfree hd hdeven hmin hcard x)
      (p G hfree hd hdeven hmin hcard y) <;>
    simp [SimpleGraph.adjMatrix_apply, hxy, hpq] at hentry ⊢

/-- Equivalence relation generated by the antipodal involution. -/
def firstOrderEvenAntipodeSetoid : Setoid V where
  r x y := x = y ∨ x = p G hfree hd hdeven hmin hcard y
  iseqv := by
    refine ⟨fun x => Or.inl rfl, ?_, ?_⟩
    · intro x y hxy
      rcases hxy with rfl | hxy
      · exact Or.inl rfl
      · right
        have hpcongr := congrArg (p G hfree hd hdeven hmin hcard) hxy
        exact (hpcongr.trans
          (firstOrderEvenAntipode_involutive
            G hfree hd hdeven hmin hcard y)).symm
    · intro x y z hxy hyz
      rcases hxy with rfl | hxy
      · exact hyz
      · rcases hyz with rfl | hyz
        · exact Or.inr hxy
        · left
          calc
            x = p G hfree hd hdeven hmin hcard y := hxy
            _ = p G hfree hd hdeven hmin hcard
                (p G hfree hd hdeven hmin hcard z) :=
              congrArg (p G hfree hd hdeven hmin hcard) hyz
            _ = z := firstOrderEvenAntipode_involutive
              G hfree hd hdeven hmin hcard z

noncomputable instance firstOrderEvenAntipodeSetoid.instDecidableRel :
    DecidableRel
      (firstOrderEvenAntipodeSetoid G hfree hd hdeven hmin hcard : V → V → Prop) :=
  Classical.decRel _

/-- The type of antipodal pairs. -/
abbrev EvenFirstOrderQuotient :=
  Quotient (firstOrderEvenAntipodeSetoid G hfree hd hdeven hmin hcard)

/-- Every quotient fiber consists of a vertex and its distinct antipode. -/
theorem card_firstOrderEvenQuotient_fiber (x : V) :
    Fintype.card {y : V //
      Quotient.mk (firstOrderEvenAntipodeSetoid
        G hfree hd hdeven hmin hcard) y =
      Quotient.mk (firstOrderEvenAntipodeSetoid
        G hfree hd hdeven hmin hcard) x} = 2 := by
  rw [Fintype.card_subtype]
  have heq :
      Finset.univ.filter (fun y : V =>
        Quotient.mk (firstOrderEvenAntipodeSetoid
          G hfree hd hdeven hmin hcard) y =
        Quotient.mk (firstOrderEvenAntipodeSetoid
          G hfree hd hdeven hmin hcard) x) =
      {x, p G hfree hd hdeven hmin hcard x} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    rw [Quotient.eq]
    change (y = x ∨ y = p G hfree hd hdeven hmin hcard x) ↔ _
    rfl
  have hnot : x ∉ ({p G hfree hd hdeven hmin hcard x} : Finset V) := by
    rw [Finset.mem_singleton]
    exact (firstOrderEvenAntipode_spec
      G hfree hd hdeven hmin hcard x).1.symm
  rw [heq, Finset.card_insert_of_notMem hnot]
  simp

/-- The quotient has half as many vertices as the original graph. -/
theorem two_mul_card_EvenFirstOrderQuotient :
    2 * Fintype.card (EvenFirstOrderQuotient
      G hfree hd hdeven hmin hcard) = Fintype.card V := by
  let q : V → EvenFirstOrderQuotient G hfree hd hdeven hmin hcard :=
    fun x => Quotient.mk
      (firstOrderEvenAntipodeSetoid G hfree hd hdeven hmin hcard) x
  have hfiber : ∀ X : EvenFirstOrderQuotient
      G hfree hd hdeven hmin hcard,
      Fintype.card {x : V // q x = X} = 2 := by
    intro X
    refine Quotient.inductionOn X ?_
    intro x
    exact card_firstOrderEvenQuotient_fiber
      G hfree hd hdeven hmin hcard x
  have hcount := Fintype.card_congr (Equiv.sigmaFiberEquiv q)
  rw [Fintype.card_sigma] at hcount
  simp_rw [hfiber] at hcount
  simpa [mul_comm] using hcount

/-- Numerical cardinality equation for the antipodal quotient. -/
theorem two_mul_card_EvenFirstOrderQuotient_eq :
    2 * Fintype.card (EvenFirstOrderQuotient
      G hfree hd hdeven hmin hcard) = d * (d - 1) + 2 := by
  rw [two_mul_card_EvenFirstOrderQuotient G hfree hd hdeven hmin hcard,
    hcard]

/-- Two antipodal fibers are adjacent when a representative is adjacent to
either lift of the other fiber. -/
def firstOrderEvenFiberAdj (x y : V) : Prop :=
  G.Adj x y ∨ G.Adj x (p G hfree hd hdeven hmin hcard y)

theorem firstOrderEvenFiberAdj_left_antipode (x y : V) :
    firstOrderEvenFiberAdj G hfree hd hdeven hmin hcard
        (p G hfree hd hdeven hmin hcard x) y ↔
      firstOrderEvenFiberAdj G hfree hd hdeven hmin hcard x y := by
  rw [firstOrderEvenFiberAdj, firstOrderEvenFiberAdj]
  have hcross : G.Adj (p G hfree hd hdeven hmin hcard x) y ↔
      G.Adj x (p G hfree hd hdeven hmin hcard y) := by
    have h := firstOrderEvenAntipode_adj_iff
      G hfree hd hdeven hmin hcard x
        (p G hfree hd hdeven hmin hcard y)
    rw [firstOrderEvenAntipode_involutive
      G hfree hd hdeven hmin hcard] at h
    exact h
  have hauto := firstOrderEvenAntipode_adj_iff
    G hfree hd hdeven hmin hcard x y
  constructor
  · rintro (h | h)
    · exact Or.inr (hcross.mp h)
    · exact Or.inl (hauto.mp h)
  · rintro (h | h)
    · exact Or.inr (hauto.mpr h)
    · exact Or.inl (hcross.mpr h)

theorem firstOrderEvenFiberAdj_right_antipode (x y : V) :
    firstOrderEvenFiberAdj G hfree hd hdeven hmin hcard x
        (p G hfree hd hdeven hmin hcard y) ↔
      firstOrderEvenFiberAdj G hfree hd hdeven hmin hcard x y := by
  rw [firstOrderEvenFiberAdj, firstOrderEvenFiberAdj,
    firstOrderEvenAntipode_involutive G hfree hd hdeven hmin hcard]
  exact or_comm

theorem firstOrderEvenFiberAdj_congr {x x' y y' : V}
    (hxx : (firstOrderEvenAntipodeSetoid
      G hfree hd hdeven hmin hcard : V → V → Prop) x x')
    (hyy : (firstOrderEvenAntipodeSetoid
      G hfree hd hdeven hmin hcard : V → V → Prop) y y') :
    firstOrderEvenFiberAdj G hfree hd hdeven hmin hcard x y ↔
      firstOrderEvenFiberAdj G hfree hd hdeven hmin hcard x' y' := by
  rcases hxx with rfl | hxx
  · rcases hyy with rfl | hyy
    · rfl
    · subst y
      exact firstOrderEvenFiberAdj_right_antipode
        G hfree hd hdeven hmin hcard x y'
  · subst x
    rcases hyy with rfl | hyy
    · exact firstOrderEvenFiberAdj_left_antipode
        G hfree hd hdeven hmin hcard x' y
    · subst y
      exact (firstOrderEvenFiberAdj_left_antipode
        G hfree hd hdeven hmin hcard x'
          (p G hfree hd hdeven hmin hcard y')).trans
        (firstOrderEvenFiberAdj_right_antipode
          G hfree hd hdeven hmin hcard x' y')

/-- Well-defined adjacency on antipodal fibers. -/
def firstOrderEvenQuotientAdj :
    EvenFirstOrderQuotient G hfree hd hdeven hmin hcard →
      EvenFirstOrderQuotient G hfree hd hdeven hmin hcard → Prop :=
  Quotient.lift₂
    (fun x y => firstOrderEvenFiberAdj G hfree hd hdeven hmin hcard x y)
    (fun _ _ _ _ hx hy => propext
      (firstOrderEvenFiberAdj_congr
        G hfree hd hdeven hmin hcard hx hy))

theorem firstOrderEvenQuotientAdj_mk (x y : V) :
    firstOrderEvenQuotientAdj G hfree hd hdeven hmin hcard
      (Quotient.mk (firstOrderEvenAntipodeSetoid
        G hfree hd hdeven hmin hcard) x)
      (Quotient.mk (firstOrderEvenAntipodeSetoid
        G hfree hd hdeven hmin hcard) y) ↔
      firstOrderEvenFiberAdj G hfree hd hdeven hmin hcard x y := Iff.rfl

/-- The canonical simple graph on the antipodal quotient. -/
def firstOrderEvenQuotientGraph :
    SimpleGraph (EvenFirstOrderQuotient G hfree hd hdeven hmin hcard) where
  Adj := firstOrderEvenQuotientAdj G hfree hd hdeven hmin hcard
  symm := by
    constructor
    intro X Y hXY
    revert hXY
    refine Quotient.inductionOn₂ X Y ?_
    intro x y hxy
    rw [firstOrderEvenQuotientAdj_mk] at hxy ⊢
    rcases hxy with hxy | hxpy
    · exact Or.inl hxy.symm
    · right
      have hcross := firstOrderEvenAntipode_adj_iff
        G hfree hd hdeven hmin hcard x
          (p G hfree hd hdeven hmin hcard y)
      rw [firstOrderEvenAntipode_involutive
        G hfree hd hdeven hmin hcard] at hcross
      exact (hcross.mpr hxpy).symm
  loopless := by
    constructor
    intro X hXX
    revert hXX
    refine Quotient.inductionOn X ?_
    intro x hxx
    rw [firstOrderEvenQuotientAdj_mk, firstOrderEvenFiberAdj] at hxx
    rcases hxx with hloop | hant
    · exact G.loopless.irrefl x hloop
    · exact (firstOrderEvenAntipode_spec
        G hfree hd hdeven hmin hcard x).2.1 hant

noncomputable instance firstOrderEvenQuotientGraph.instDecidableAdj :
    DecidableRel (firstOrderEvenQuotientGraph
      G hfree hd hdeven hmin hcard).Adj := Classical.decRel _

/-- The quotient neighborhood of `[x]` is the image of the original
neighborhood of `x`. -/
theorem firstOrderEvenQuotient_neighborFinset_mk (x : V) :
    (firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard).neighborFinset
        (Quotient.mk (firstOrderEvenAntipodeSetoid
          G hfree hd hdeven hmin hcard) x) =
      Finset.image (fun y =>
        Quotient.mk (firstOrderEvenAntipodeSetoid
          G hfree hd hdeven hmin hcard) y) (G.neighborFinset x) := by
  ext Y
  refine Quotient.inductionOn Y ?_
  intro y
  rw [SimpleGraph.mem_neighborFinset]
  change firstOrderEvenQuotientAdj G hfree hd hdeven hmin hcard
      (Quotient.mk (firstOrderEvenAntipodeSetoid
        G hfree hd hdeven hmin hcard) x)
      (Quotient.mk (firstOrderEvenAntipodeSetoid
        G hfree hd hdeven hmin hcard) y) ↔ _
  rw [firstOrderEvenQuotientAdj_mk]
  constructor
  · rintro (hxy | hxpy)
    · rw [Finset.mem_image]
      exact ⟨y, (G.mem_neighborFinset x y).mpr hxy, rfl⟩
    · rw [Finset.mem_image]
      refine ⟨p G hfree hd hdeven hmin hcard y,
        (G.mem_neighborFinset x _).mpr hxpy, ?_⟩
      apply Quotient.sound
      exact Or.inr rfl
  · intro himage
    rw [Finset.mem_image] at himage
    obtain ⟨z, hzx, hzy⟩ := himage
    rw [Quotient.eq] at hzy
    have hxz : G.Adj x z := (G.mem_neighborFinset x z).mp hzx
    rcases hzy with hzy | hzy
    · exact Or.inl (by simpa [hzy] using hxz)
    · exact Or.inr (by simpa [hzy] using hxz)

/-- Distinct neighbors of a vertex lie in distinct antipodal fibers. -/
theorem firstOrderEvenQuotient_mk_injOn_neighborFinset (x : V) :
    Set.InjOn
      (fun y => Quotient.mk (firstOrderEvenAntipodeSetoid
        G hfree hd hdeven hmin hcard) y) (G.neighborFinset x) := by
  intro y hy z hz hyz
  rw [Quotient.eq] at hyz
  rcases hyz with hyz | hyz
  · exact hyz
  · exfalso
    have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hy
    have hxz : G.Adj x z := (G.mem_neighborFinset x z).mp hz
    have hzero := (firstOrderEvenAntipode_spec
      G hfree hd hdeven hmin hcard z).2.2
    have hxmem : x ∈ G.neighborFinset z ∩
        G.neighborFinset (p G hfree hd hdeven hmin hcard z) := by
      refine Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset z x).mpr hxz.symm, ?_⟩
      rw [← hyz]
      exact (G.mem_neighborFinset y x).mpr hxy.symm
    rw [Finset.card_eq_zero.mp hzero] at hxmem
    exact Finset.notMem_empty _ hxmem

/-- The antipodal quotient is `d`-regular. -/
theorem firstOrderEvenQuotient_degree
    (X : EvenFirstOrderQuotient G hfree hd hdeven hmin hcard) :
    (firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard).degree X = d := by
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 3 := ⟨d - 3, by omega⟩
    norm_num
    nlinarith
  refine Quotient.inductionOn X ?_
  intro x
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    firstOrderEvenQuotient_neighborFinset_mk]
  rw [Finset.card_image_iff.mpr
    (firstOrderEvenQuotient_mk_injOn_neighborFinset
      G hfree hd hdeven hmin hcard x)]
  rw [G.card_neighborFinset_eq_degree]
  exact degree_eq_of_minDegree_card_lt_nextMooreLayer
    G hfree (by omega) hmin hbelow x

private theorem firstOrderEven_card_common_eq_one
    (x y : V) (hxy : x ≠ y)
    (hanti : x ≠ p G hfree hd hdeven hmin hcard y) :
    (G.neighborFinset x ∩ G.neighborFinset y).card = 1 := by
  rw [card_common_eq_if_antipodal_of_firstOrder_even
    G hfree hd hdeven hmin hcard x y hxy, if_neg]
  rw [mem_antipodalNeighbors_iff_eq_firstOrderEvenAntipode
    G hfree hd hdeven hmin hcard]
  intro hy
  apply hanti
  rw [hy, firstOrderEvenAntipode_involutive
    G hfree hd hdeven hmin hcard]

theorem firstOrderEvenQuotient_common_eq_two
    {X Y : EvenFirstOrderQuotient G hfree hd hdeven hmin hcard} (hXY : X ≠ Y) :
    ((firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard).neighborFinset X ∩
      (firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard).neighborFinset Y).card = 2 := by
  classical
  revert hXY
  refine Quotient.inductionOn₂ X Y ?_
  intro x y hXY
  let q : V → EvenFirstOrderQuotient G hfree hd hdeven hmin hcard :=
    fun z => Quotient.mk (firstOrderEvenAntipodeSetoid G hfree hd hdeven hmin hcard) z
  have hrel : ¬ (x = y ∨ x = p G hfree hd hdeven hmin hcard y) := by
    intro h
    apply hXY
    exact Quotient.sound h
  have hxy : x ≠ y := fun h => hrel (Or.inl h)
  have hxpy : x ≠ p G hfree hd hdeven hmin hcard y := fun h => hrel (Or.inr h)
  let A := G.neighborFinset x ∩ G.neighborFinset y
  let B := G.neighborFinset x ∩
    G.neighborFinset (p G hfree hd hdeven hmin hcard y)
  have hAcard : A.card = 1 := by
    exact firstOrderEven_card_common_eq_one
      G hfree hd hdeven hmin hcard x y hxy hxpy
  have hxpy_ne : x ≠ p G hfree hd hdeven hmin hcard y := hxpy
  have hx_ne_ppy : x ≠ p G hfree hd hdeven hmin hcard (p G hfree hd hdeven hmin hcard y) := by
    intro h
    apply hxy
    exact h.trans (firstOrderEvenAntipode_involutive G hfree hd hdeven hmin hcard y)
  have hBcard : B.card = 1 := by
    exact firstOrderEven_card_common_eq_one G hfree hd hdeven hmin hcard
      x (p G hfree hd hdeven hmin hcard y) hxpy_ne hx_ne_ppy
  let C :=
    (firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard).neighborFinset (q x) ∩
      (firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard).neighborFinset (q y)
  let U := Finset.image q A ∪ Finset.image q B
  have hCU : C ⊆ U := by
    intro Z hZ
    refine Quotient.inductionOn Z ?_ hZ
    intro z hz
    have hzparts := Finset.mem_inter.mp hz
    have hxz : firstOrderEvenFiberAdj G hfree hd hdeven hmin hcard x z := by
      apply (firstOrderEvenQuotientAdj_mk G hfree hd hdeven hmin hcard x z).mp
      exact ((firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard).mem_neighborFinset
        (q x) (q z)).mp hzparts.1
    have hyz : firstOrderEvenFiberAdj G hfree hd hdeven hmin hcard y z := by
      apply (firstOrderEvenQuotientAdj_mk G hfree hd hdeven hmin hcard y z).mp
      exact ((firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard).mem_neighborFinset
        (q y) (q z)).mp hzparts.2
    change Quotient.mk (firstOrderEvenAntipodeSetoid G hfree hd hdeven hmin hcard) z ∈
      Finset.image q A ∪ Finset.image q B
    rw [Finset.mem_union]
    rcases hxz with hxz | hxpz <;> rcases hyz with hyz | hypz
    · left
      rw [Finset.mem_image]
      refine ⟨z, Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset x z).mpr hxz,
          (G.mem_neighborFinset y z).mpr hyz⟩, rfl⟩
    · right
      rw [Finset.mem_image]
      have hzpy : G.Adj z (p G hfree hd hdeven hmin hcard y) := by
        have h := (firstOrderEvenAntipode_adj_iff G hfree hd hdeven hmin hcard
          y (p G hfree hd hdeven hmin hcard z)).mpr hypz
        rw [firstOrderEvenAntipode_involutive
          G hfree hd hdeven hmin hcard] at h
        exact h.symm
      refine ⟨z, Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset x z).mpr hxz,
          (G.mem_neighborFinset (p G hfree hd hdeven hmin hcard y) z).mpr hzpy.symm⟩, rfl⟩
    · right
      rw [Finset.mem_image]
      let z' := p G hfree hd hdeven hmin hcard z
      have hz'x : G.Adj x z' := hxpz
      have hz'py : G.Adj (p G hfree hd hdeven hmin hcard y) z' :=
        (firstOrderEvenAntipode_adj_iff G hfree hd hdeven hmin hcard y z).2 hyz
      refine ⟨z', Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset x z').mpr hz'x,
          (G.mem_neighborFinset (p G hfree hd hdeven hmin hcard y) z').mpr hz'py⟩, ?_⟩
      apply Quotient.sound
      exact Or.inr rfl
    · left
      rw [Finset.mem_image]
      let z' := p G hfree hd hdeven hmin hcard z
      have hz'x : G.Adj x z' := hxpz
      have hz'y : G.Adj y z' := hypz
      refine ⟨z', Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset x z').mpr hz'x,
          (G.mem_neighborFinset y z').mpr hz'y⟩, ?_⟩
      apply Quotient.sound
      exact Or.inr rfl
  have hupper : C.card ≤ 2 := by
    calc
      C.card ≤ U.card := Finset.card_le_card hCU
      _ ≤ (Finset.image q A).card + (Finset.image q B).card :=
        Finset.card_union_le _ _
      _ ≤ A.card + B.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2 := by rw [hAcard, hBcard]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hAcard
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hBcard
  have haA : a ∈ A := by rw [ha]; simp
  have hbB : b ∈ B := by rw [hb]; simp
  have hquotAdj {u v : V} (huv : G.Adj u v) :
      (firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard).Adj (q u) (q v) := by
    apply (firstOrderEvenQuotientAdj_mk G hfree hd hdeven hmin hcard u v).2
    exact Or.inl huv
  have hquotAdjAnt {u v : V} (huv : G.Adj u (p G hfree hd hdeven hmin hcard v)) :
      (firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard).Adj (q u) (q v) := by
    apply (firstOrderEvenQuotientAdj_mk G hfree hd hdeven hmin hcard u v).2
    exact Or.inr huv
  have hqaC : q a ∈ C := by
    change q a ∈
      (firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard).neighborFinset (q x) ∩
        (firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard).neighborFinset (q y)
    rw [Finset.mem_inter]
    have haa := Finset.mem_inter.mp haA
    exact ⟨((firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard).mem_neighborFinset
        (q x) (q a)).2 (hquotAdj ((G.mem_neighborFinset x a).mp haa.1)),
      ((firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard).mem_neighborFinset
        (q y) (q a)).2 (hquotAdj ((G.mem_neighborFinset y a).mp haa.2))⟩
  have hqbC : q b ∈ C := by
    change q b ∈
      (firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard).neighborFinset (q x) ∩
        (firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard).neighborFinset (q y)
    rw [Finset.mem_inter]
    have hbb := Finset.mem_inter.mp hbB
    have hxb : G.Adj x b := (G.mem_neighborFinset x b).mp hbb.1
    have hpyb : G.Adj (p G hfree hd hdeven hmin hcard y) b :=
      (G.mem_neighborFinset (p G hfree hd hdeven hmin hcard y) b).mp hbb.2
    have hypb : G.Adj y (p G hfree hd hdeven hmin hcard b) := by
      have h := firstOrderEvenAntipode_adj_iff G hfree hd hdeven hmin hcard
        y (p G hfree hd hdeven hmin hcard b)
      rw [firstOrderEvenAntipode_involutive
        G hfree hd hdeven hmin hcard] at h
      exact h.mp hpyb
    exact ⟨((firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard).mem_neighborFinset
        (q x) (q b)).2 (hquotAdj hxb),
      ((firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard).mem_neighborFinset
        (q y) (q b)).2 (hquotAdjAnt hypb)⟩
  have hqab : q a ≠ q b := by
    intro heq
    rw [Quotient.eq] at heq
    rcases heq with hab | hab
    · subst b
      have haa := Finset.mem_inter.mp haA
      have hbb := Finset.mem_inter.mp hbB
      have hzero := (firstOrderEvenAntipode_spec
        G hfree hd hdeven hmin hcard y).2.2
      have : a ∈ G.neighborFinset y ∩
          G.neighborFinset (p G hfree hd hdeven hmin hcard y) :=
        Finset.mem_inter.mpr ⟨haa.2, hbb.2⟩
      rw [Finset.card_eq_zero.mp hzero] at this
      exact Finset.notMem_empty _ this
    · have haa := Finset.mem_inter.mp haA
      have hbb := Finset.mem_inter.mp hbB
      have hzero := (firstOrderEvenAntipode_spec
        G hfree hd hdeven hmin hcard b).2.2
      have : x ∈ G.neighborFinset b ∩
          G.neighborFinset (p G hfree hd hdeven hmin hcard b) := by
        refine Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset b x).mpr
            ((G.mem_neighborFinset x b).mp hbb.1).symm, ?_⟩
        rw [← hab]
        exact (G.mem_neighborFinset a x).mpr
          ((G.mem_neighborFinset x a).mp haa.1).symm
      rw [Finset.card_eq_zero.mp hzero] at this
      exact Finset.notMem_empty _ this
  have hlower : 2 ≤ C.card := by
    have := Finset.one_lt_card.mpr ⟨q a, hqaC, q b, hqbC, hqab⟩
    omega
  change C.card = 2
  omega

/-- The quotient adjacency matrix has the strongly regular identity
`Q² = (d-2)I + 2J`. -/
theorem firstOrderEvenQuotient_adjMatrix_sq :
    let H := firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard
    H.adjMatrix ℤ * H.adjMatrix ℤ =
      (d - 2 : ℤ) • (1 : Matrix
        (EvenFirstOrderQuotient G hfree hd hdeven hmin hcard)
        (EvenFirstOrderQuotient G hfree hd hdeven hmin hcard) ℤ) +
      (2 : ℤ) • FriendshipTheoremOQ01.onesMatrix
        (EvenFirstOrderQuotient G hfree hd hdeven hmin hcard) := by
  dsimp only
  ext X Y
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    FriendshipTheoremOQ01.onesMatrix, Matrix.of_apply, smul_eq_mul]
  by_cases hXY : X = Y
  · subst Y
    rw [(firstOrderEvenQuotientGraph
      G hfree hd hdeven hmin hcard).adjMatrix_mul_self_apply_self,
      firstOrderEvenQuotient_degree G hfree hd hdeven hmin hcard]
    simp
  · rw [adjMatrix_sq_apply_eq_card_common,
      firstOrderEvenQuotient_common_eq_two
        G hfree hd hdeven hmin hcard hXY]
    simp [hXY]


end

end Erdos85
