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

/-- Rank-one determinant formula needed by the quotient spectral argument. -/
lemma det_scalar_sub_two_onesMatrix
    {W : Type*} [Fintype W] [DecidableEq W]
    (hn : 2 ≤ Fintype.card W) (c : ℤ) :
    (c • (1 : Matrix W W ℤ) -
      (2 : ℤ) • FriendshipTheoremOQ01.onesMatrix W).det =
      c ^ (Fintype.card W - 1) *
        (c - 2 * (Fintype.card W : ℤ)) := by
  set n := Fintype.card W with hn_def
  by_cases hc : c = 0
  · subst c
    have hJ0 : (FriendshipTheoremOQ01.onesMatrix W).det = 0 :=
      FriendshipTheoremOQ01.det_onesMatrix_eq_zero (by omega)
    rw [zero_smul, zero_sub, ← neg_smul, Matrix.det_smul, hJ0, mul_zero]
    simp [zero_pow (show n - 1 ≠ 0 by omega)]
  · have hcq : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc
    suffices hq :
        (((c • (1 : Matrix W W ℤ) -
          (2 : ℤ) • FriendshipTheoremOQ01.onesMatrix W).det : ℤ) : ℚ) =
        ((c ^ (n - 1) * (c - 2 * (n : ℤ)) : ℤ) : ℚ) by
      exact_mod_cast hq
    let M := c • (1 : Matrix W W ℤ) -
      (2 : ℤ) • FriendshipTheoremOQ01.onesMatrix W
    change (Int.castRingHom ℚ) M.det = _
    rw [RingHom.map_det]
    have hmap : RingHom.mapMatrix (Int.castRingHom ℚ) M =
        (c : ℚ) • (1 : Matrix W W ℚ) -
          (2 : ℚ) • Matrix.of (fun (_ : W) (_ : W) => (1 : ℚ)) := by
      ext i j
      simp only [M, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        FriendshipTheoremOQ01.onesMatrix, Matrix.of_apply, smul_eq_mul,
        map_sub, map_mul, Int.coe_castRingHom]
      split <;> simp
    rw [hmap]
    have hfactor :
        (c : ℚ) • (1 : Matrix W W ℚ) -
            (2 : ℚ) • Matrix.of (fun (_ : W) (_ : W) => (1 : ℚ)) =
          (c : ℚ) • ((1 : Matrix W W ℚ) -
            ((c : ℚ)⁻¹ * 2) •
              Matrix.of (fun (_ : W) (_ : W) => (1 : ℚ))) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.of_apply, smul_eq_mul]
      by_cases hij : i = j <;> simp only [hij, if_pos, if_neg]
      all_goals field_simp
    rw [hfactor, Matrix.det_smul,
      FriendshipTheoremOQ01.det_one_sub_smul_ones_gen]
    have h1 : Fintype.card W = n - 1 + 1 := by omega
    rw [h1, pow_succ, show n - 1 + 1 = n from by omega]
    push_cast
    field_simp

/-- Product identity for the nontrivial quotient characteristic polynomial
when the quotient order is even. -/
theorem firstOrderEvenQuotient_charpoly_product
    (hn_even : Even (Fintype.card (EvenFirstOrderQuotient
      G hfree hd hdeven hmin hcard))) :
    ∃ f : Polynomial ℤ,
      ((firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard).adjMatrix
          ℤ).charpoly =
        (Polynomial.X - Polynomial.C (d : ℤ)) * f ∧
      f * f.comp (-Polynomial.X) =
        -((Polynomial.X ^ 2 - Polynomial.C (d - 2 : ℤ)) ^
          (Fintype.card (EvenFirstOrderQuotient
            G hfree hd hdeven hmin hcard) - 1)) := by
  let W := EvenFirstOrderQuotient G hfree hd hdeven hmin hcard
  let H := firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard
  let n := Fintype.card W
  have hn2 : 2 ≤ n := by
    have htwo := two_mul_card_EvenFirstOrderQuotient_eq
      G hfree hd hdeven hmin hcard
    change 2 * n = d * (d - 1) + 2 at htwo
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 3 := ⟨d - 3, by omega⟩
    norm_num at htwo ⊢
    nlinarith
  haveI : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  have hreg : ∀ X : W, H.degree X = d :=
    firstOrderEvenQuotient_degree G hfree hd hdeven hmin hcard
  obtain ⟨f, hf⟩ := FriendshipTheoremOQ01.X_sub_degree_dvd_adjMatrix_charpoly
    H d hreg
  refine ⟨f, hf, ?_⟩
  let A := H.adjMatrix ℤ
  have hAsq : A * A = (d - 2 : ℤ) • (1 : Matrix W W ℤ) +
      (2 : ℤ) • FriendshipTheoremOQ01.onesMatrix W := by
    exact firstOrderEvenQuotient_adjMatrix_sq
      G hfree hd hdeven hmin hcard
  have hcard2 : 2 * n = d * (d - 1) + 2 := by
    exact two_mul_card_EvenFirstOrderQuotient_eq
      G hfree hd hdeven hmin hcard
  have hd2cast : ((d - 2 : ℕ) : ℤ) = (d : ℤ) - 2 := by
    omega
  have heval : ∀ x : ℤ, (x ^ 2 - (d : ℤ) ^ 2) *
      (f.eval x * f.eval (-x) +
        (x ^ 2 - (d - 2 : ℕ)) ^ (n - 1)) = 0 := by
    intro x
    have hgx : Polynomial.eval x A.charpoly =
        (x - d) * f.eval x := by
      rw [hf]
      simp [Polynomial.eval_mul, Polynomial.eval_sub]
    have hgmx : Polynomial.eval (-x) A.charpoly =
        (-x - d) * f.eval (-x) := by
      rw [hf]
      simp [Polynomial.eval_mul, Polynomial.eval_sub]
    have hg_det := FriendshipTheoremOQ01.charpoly_eval_eq_det H x
    have hgm_det := FriendshipTheoremOQ01.charpoly_eval_eq_det H (-x)
    have hway1 : Polynomial.eval x A.charpoly *
        Polynomial.eval (-x) A.charpoly =
        -(x ^ 2 - (d : ℤ) ^ 2) * (f.eval x * f.eval (-x)) := by
      rw [hgx, hgmx]
      ring
    have hneg_eq : (-x) • (1 : Matrix W W ℤ) - A =
        -(x • 1 + A) := by
      ext i j
      simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
        Matrix.neg_apply, Matrix.one_apply, smul_eq_mul]
      ring
    have hdiff_sq : (x • (1 : Matrix W W ℤ) - A) *
        (x • 1 + A) = x ^ 2 • 1 - A * A := by
      rw [sub_mul, mul_add, mul_add, smul_mul_assoc, Matrix.one_mul,
        smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one,
        smul_smul, sq]
      abel
    have hmatrix_eq : x ^ 2 • (1 : Matrix W W ℤ) - A * A =
        (x ^ 2 - (d - 2 : ℤ)) • (1 : Matrix W W ℤ) -
          (2 : ℤ) • FriendshipTheoremOQ01.onesMatrix W := by
      rw [hAsq]
      ext i j
      simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
        Matrix.one_apply, FriendshipTheoremOQ01.onesMatrix,
        Matrix.of_apply, smul_eq_mul]
      ring
    have htail : x ^ 2 - (d - 2 : ℤ) - 2 * (n : ℤ) =
        x ^ 2 - (d : ℤ) ^ 2 := by
      zify at hcard2
      have hd1cast : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
      rw [hd1cast] at hcard2
      nlinarith [sq (d : ℤ)]
    have hway2 : Polynomial.eval x A.charpoly *
        Polynomial.eval (-x) A.charpoly =
        (x ^ 2 - (d - 2 : ℕ)) ^ (n - 1) *
          (x ^ 2 - (d : ℤ) ^ 2) := by
      rw [hg_det, hgm_det, hneg_eq, Matrix.det_neg]
      rw [show (-1 : ℤ) ^ Fintype.card W = 1 by
        change (-1 : ℤ) ^ n = 1
        exact hn_even.neg_one_pow]
      simp only [one_mul]
      rw [← Matrix.det_mul, hdiff_sq, hmatrix_eq,
        det_scalar_sub_two_onesMatrix hn2, htail]
      rw [hd2cast]
    nlinarith [hway1, hway2]
  let Q := f * f.comp (-Polynomial.X) +
    (Polynomial.X ^ 2 - Polynomial.C (d - 2 : ℤ)) ^ (n - 1)
  have hprod_eval : ∀ x : ℤ,
      Polynomial.eval x
        ((Polynomial.X ^ 2 - Polynomial.C ((d : ℤ) ^ 2)) * Q) = 0 := by
    intro x
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_comp, Polynomial.eval_neg, Q]
    rw [← hd2cast]
    exact heval x
  have hprod_zero :
      (Polynomial.X ^ 2 - Polynomial.C ((d : ℤ) ^ 2)) * Q = 0 := by
    apply Polynomial.funext
    intro x
    simpa using hprod_eval x
  have hne :
      (Polynomial.X ^ 2 - Polynomial.C ((d : ℤ) ^ 2) : Polynomial ℤ) ≠ 0 := by
    intro h
    have hc := congrArg (fun p : Polynomial ℤ => p.coeff 2) h
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_zero, if_true, ite_false] at hc
    omega
  have hQ : Q = 0 := (mul_eq_zero.mp hprod_zero).resolve_left hne
  exact eq_neg_of_add_eq_zero_left hQ

/-- A symmetric irreducible factor appearing in `f(X)f(-X)` has even
multiplicity, even when the product carries a minus-unit. -/
lemma even_exponent_of_mul_comp_eq_neg_irreducible_pow
    (p f : Polynomial ℤ) (m : ℕ)
    (hp : Irreducible p) (hsym : p.comp (-Polynomial.X) = p)
    (hprod : f * f.comp (-Polynomial.X) = -(p ^ m)) : Even m := by
  induction m using Nat.strong_induction_on generalizing f with
  | h m ih =>
    by_cases hm0 : m = 0
    · subst m
      exact Even.zero
    by_cases hm1 : m = 1
    · subst m
      have hpdvd : p ∣ f * f.comp (-Polynomial.X) := by
        rw [hprod, pow_one]
        exact dvd_neg.mpr (dvd_refl p)
      have hpf : p ∣ f := by
        rcases hp.prime.dvd_or_dvd hpdvd with h | h
        · exact h
        · obtain ⟨g, hg⟩ := h
          have hneg_inv : (-Polynomial.X : Polynomial ℤ).comp
              (-Polynomial.X) = Polynomial.X := by
            rw [Polynomial.neg_comp, Polynomial.X_comp, neg_neg]
          have hf_inv : (f.comp (-Polynomial.X)).comp
              (-Polynomial.X) = f := by
            rw [Polynomial.comp_assoc, hneg_inv, Polynomial.comp_X]
          rw [← hf_inv, hg, Polynomial.mul_comp, hsym]
          exact dvd_mul_right p _
      obtain ⟨f₁, hf₁⟩ := hpf
      have hfc : f.comp (-Polynomial.X) =
          p * f₁.comp (-Polynomial.X) := by
        rw [hf₁, Polynomial.mul_comp, hsym]
      have hp2dvd : p ^ 2 ∣ p := by
        refine ⟨-(f₁ * f₁.comp (-Polynomial.X)), ?_⟩
        have hprod' : (p * f₁) * (p * f₁.comp (-Polynomial.X)) = -p := by
          rw [← hf₁, ← hfc]
          simpa using hprod
        calc
          p = -((p * f₁) * (p * f₁.comp (-Polynomial.X))) := by
            rw [hprod']
            simp
          _ = p ^ 2 * (-(f₁ * f₁.comp (-Polynomial.X))) := by
            ring
      have hpone : p ∣ (1 : Polynomial ℤ) := by
        apply (mul_dvd_mul_iff_left hp.ne_zero).mp
        simpa [pow_two] using hp2dvd
      exact (hp.not_isUnit (isUnit_of_dvd_one hpone)).elim
    obtain ⟨r, rfl⟩ : ∃ r, m = r + 2 := ⟨m - 2, by omega⟩
    have hpdvd : p ∣ f * f.comp (-Polynomial.X) := by
      rw [hprod]
      exact dvd_neg.mpr (dvd_pow_self p (by omega))
    have hpf : p ∣ f := by
      rcases hp.prime.dvd_or_dvd hpdvd with h | h
      · exact h
      · obtain ⟨g, hg⟩ := h
        have hneg_inv : (-Polynomial.X : Polynomial ℤ).comp
            (-Polynomial.X) = Polynomial.X := by
          rw [Polynomial.neg_comp, Polynomial.X_comp, neg_neg]
        have hf_inv : (f.comp (-Polynomial.X)).comp
            (-Polynomial.X) = f := by
          rw [Polynomial.comp_assoc, hneg_inv, Polynomial.comp_X]
        rw [← hf_inv, hg, Polynomial.mul_comp, hsym]
        exact dvd_mul_right p _
    obtain ⟨f₁, hf₁⟩ := hpf
    have hfc : f.comp (-Polynomial.X) =
        p * f₁.comp (-Polynomial.X) := by
      rw [hf₁, Polynomial.mul_comp, hsym]
    have hcancel : f₁ * f₁.comp (-Polynomial.X) = -(p ^ r) := by
      have hp2ne : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
      apply mul_left_cancel₀ hp2ne
      calc
        p ^ 2 * (f₁ * f₁.comp (-Polynomial.X)) =
            f * f.comp (-Polynomial.X) := by
              rw [hf₁, Polynomial.mul_comp, hsym]
              ring
        _ = -(p ^ (r + 2)) := hprod
        _ = p ^ 2 * (-(p ^ r)) := by
          rw [show r + 2 = 2 + r by omega, pow_add]
          ring
    obtain ⟨t, ht⟩ := ih r (by omega) f₁ hcancel
    exact ⟨t + 1, by omega⟩

/-- Sub-leading coefficient of a regular graph's nontrivial characteristic
factor. -/
lemma regular_charpoly_quotient_subleading
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (n d : ℕ) (hn : n = Fintype.card W) (hn3 : 3 ≤ n)
    (f : Polynomial ℤ)
    (hf : (H.adjMatrix ℤ).charpoly =
      (Polynomial.X - Polynomial.C (d : ℤ)) * f)
    (hmonic : f.Monic) (hdeg : f.natDegree = n - 1) :
    f.coeff (n - 2) = d := by
  have htrace : Matrix.trace (H.adjMatrix ℤ) = 0 :=
    FriendshipTheoremOQ01.adjMatrix_trace_zero H
  have hcoeff : (H.adjMatrix ℤ).charpoly.coeff (n - 1) = 0 := by
    have h := Matrix.trace_eq_neg_charpoly_coeff (H.adjMatrix ℤ)
    rw [htrace, ← hn] at h
    linarith
  have hlead : f.coeff (n - 1) = 1 := by
    rw [show n - 1 = f.natDegree from hdeg.symm]
    exact hmonic.leadingCoeff
  have hprod : ((Polynomial.X - Polynomial.C (d : ℤ)) * f).coeff
      (n - 1) = f.coeff (n - 2) - d * f.coeff (n - 1) := by
    rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    congr 1
    rw [show n - 1 = (n - 2) + 1 by omega]
    exact Polynomial.coeff_X_mul f (n - 2)
  rw [← hf, hcoeff, hlead, mul_one] at hprod
  linarith

set_option maxHeartbeats 800000 in
include G hfree hd hdeven hmin hcard in
/-- The surviving power-of-two degree family and the quotient product
identity force `d-2` to be a perfect square. -/
theorem d_sub_two_is_square_of_firstOrder_even :
    ∃ s : ℕ, d - 2 = s * s := by
  obtain ⟨k, hk, hdk⟩ := exists_large_power_degree_of_firstOrder_even
    G hfree hd hdeven hmin hcard
  let n := Fintype.card (EvenFirstOrderQuotient
    G hfree hd hdeven hmin hcard)
  let t := 2 ^ (k - 2)
  have hpow : 2 ^ k = 4 * t := by
    have hsplit : k = (k - 2) + 2 := by omega
    rw [hsplit, pow_add]
    norm_num [t]
    ring
  have hdform : d = 4 * t + 2 := by omega
  have hcard2 : 2 * n = d * (d - 1) + 2 :=
    two_mul_card_EvenFirstOrderQuotient_eq
      G hfree hd hdeven hmin hcard
  have hnform : n = 8 * t * t + 6 * t + 2 := by
    rw [hdform] at hcard2
    have hsub : 4 * t + 2 - 1 = 4 * t + 1 := by omega
    rw [hsub] at hcard2
    nlinarith
  have hn_even : Even n := by
    refine ⟨4 * t * t + 3 * t + 1, ?_⟩
    rw [hnform]
    ring
  have hn1_odd : Odd (n - 1) := by
    obtain ⟨a, ha⟩ := hn_even
    have hn2 : 2 ≤ n := by
      rw [hnform]
      omega
    refine ⟨a - 1, ?_⟩
    omega
  by_cases hsquare : ∃ s : ℕ, d - 2 = s * s
  · exact hsquare
  exfalso
  have hns : ∀ s : ℕ, d - 2 ≠ s * s := by
    intro s hs
    exact hsquare ⟨s, hs⟩
  obtain ⟨f, _hf, hprod⟩ := firstOrderEvenQuotient_charpoly_product
    G hfree hd hdeven hmin hcard hn_even
  let p : Polynomial ℤ :=
    Polynomial.X ^ 2 - Polynomial.C (d - 2 : ℤ)
  have hp : Irreducible p := by
    dsimp only [p]
    have hd2cast : ((d - 2 : ℕ) : ℤ) = (d : ℤ) - 2 := by omega
    rw [← hd2cast]
    exact FriendshipTheoremOQ01.sq_sub_irreducible_of_not_square
      (d - 2) (by omega) hns
  have hsym : p.comp (-Polynomial.X) = p := by
    simp [p, Polynomial.sub_comp, Polynomial.pow_comp,
      Polynomial.X_comp]
  have heven := even_exponent_of_mul_comp_eq_neg_irreducible_pow
    p f (n - 1) hp hsym hprod
  exact (Nat.not_even_iff_odd.mpr hn1_odd) heven

set_option maxHeartbeats 800000 in
include G hfree hd hdeven hmin hcard in
/-- If `s²=d-2`, the quotient trace forces `s∣d`. -/
theorem sqrt_d_sub_two_dvd_d_of_firstOrder_even
    (s : ℕ) (hs : d - 2 = s * s) : s ∣ d := by
  obtain ⟨k, hk, hdk⟩ := exists_large_power_degree_of_firstOrder_even
    G hfree hd hdeven hmin hcard
  let W := EvenFirstOrderQuotient G hfree hd hdeven hmin hcard
  let H := firstOrderEvenQuotientGraph G hfree hd hdeven hmin hcard
  let n := Fintype.card W
  let t := 2 ^ (k - 2)
  have hpow : 2 ^ k = 4 * t := by
    have hsplit : k = (k - 2) + 2 := by omega
    rw [hsplit, pow_add]
    norm_num [t]
    ring
  have hdform : d = 4 * t + 2 := by omega
  have hcard2 : 2 * n = d * (d - 1) + 2 :=
    two_mul_card_EvenFirstOrderQuotient_eq
      G hfree hd hdeven hmin hcard
  have hnform : n = 8 * t * t + 6 * t + 2 := by
    rw [hdform] at hcard2
    have hsub : 4 * t + 2 - 1 = 4 * t + 1 := by omega
    rw [hsub] at hcard2
    nlinarith
  have hn3 : 3 ≤ n := by
    have ht : 1 ≤ t := by
      exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
    rw [hnform]
    nlinarith
  have hn_even : Even n := by
    refine ⟨4 * t * t + 3 * t + 1, ?_⟩
    rw [hnform]
    ring
  haveI : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨f, hf, hprod⟩ := firstOrderEvenQuotient_charpoly_product
    G hfree hd hdeven hmin hcard hn_even
  have hf_monic : f.Monic := by
    have hcm := (H.adjMatrix ℤ).charpoly_monic
    rw [hf] at hcm
    have hlead := hcm.leadingCoeff
    rw [Polynomial.leadingCoeff_mul,
      (Polynomial.monic_X_sub_C (d : ℤ)).leadingCoeff, one_mul] at hlead
    exact hlead
  have hf_deg : f.natDegree = n - 1 := by
    have hcd := Matrix.charpoly_natDegree_eq_dim (H.adjMatrix ℤ)
    rw [hf] at hcd
    have hxne := (Polynomial.monic_X_sub_C (d : ℤ)).ne_zero
    rw [Polynomial.natDegree_mul hxne hf_monic.ne_zero,
      Polynomial.natDegree_X_sub_C] at hcd
    change _ = Fintype.card W at hcd
    omega
  have hcoeff : f.coeff (n - 2) = d :=
    regular_charpoly_quotient_subleading H n d rfl hn3 f hf hf_monic hf_deg
  let p : Polynomial ℤ :=
    Polynomial.X ^ 2 - Polynomial.C (d - 2 : ℤ)
  have hdiv : f ∣ p ^ (n - 1) := by
    change f * f.comp (-Polynomial.X) = -(p ^ (n - 1)) at hprod
    refine ⟨-(f.comp (-Polynomial.X)), ?_⟩
    calc
      p ^ (n - 1) = -(f * f.comp (-Polynomial.X)) := by rw [hprod]; simp
      _ = f * -(f.comp (-Polynomial.X)) := by ring
  let φ : ℤ →+* ℚ := Int.castRingHom ℚ
  let F : Polynomial ℚ := f.map φ
  let P : Polynomial ℚ := p.map φ
  have hdivQ : F ∣ P ^ (n - 1) := by
    simpa [F, P, Polynomial.map_pow] using Polynomial.map_dvd φ hdiv
  have hs_cast : (d : ℚ) - 2 = (s : ℚ) * s := by
    have hdval : d = s * s + 2 := by omega
    exact_mod_cast (show (d : ℤ) - 2 = (s : ℤ) * s by omega)
  have hPfactor : P =
      (Polynomial.X - Polynomial.C (s : ℚ)) *
        (Polynomial.X - Polynomial.C (-(s : ℚ))) := by
    dsimp only [P, p, φ]
    simp only [Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, Int.coe_castRingHom,
      Int.cast_sub, Int.cast_ofNat]
    have hs_cast' : ((d : ℤ) : ℚ) - 2 = (s : ℚ) * s := by
      exact_mod_cast (show (d : ℤ) - 2 = (s : ℤ) * s by omega)
    rw [hs_cast']
    simp only [map_neg]
    rw [map_mul]
    ring
  have hPne : P ≠ 0 := by
    rw [hPfactor]
    exact mul_ne_zero (Polynomial.X_sub_C_ne_zero _)
      (Polynomial.X_sub_C_ne_zero _)
  have hsplitP : (P ^ (n - 1)).Splits := by
    rw [hPfactor]
    exact ((Polynomial.Splits.X_sub_C (s : ℚ)).mul
      (Polynomial.Splits.X_sub_C (-(s : ℚ)))).pow (n - 1)
  have hsplitF : F.Splits :=
    hsplitP.of_dvd (pow_ne_zero _ hPne) hdivQ
  have hFmonic : F.Monic := hf_monic.map φ
  have hFne : F ≠ 0 := hFmonic.ne_zero
  have hmpos : 0 < n - 1 := by omega
  have hroot : ∀ r : ℚ, r ∈ F.roots → r = s ∨ r = -(s : ℚ) := by
    intro r hr
    obtain ⟨q, hq⟩ := hdivQ
    have hFr : F.eval r = 0 :=
      (Polynomial.mem_roots hFne).mp hr
    have hPrpow : (P ^ (n - 1)).eval r = 0 := by
      rw [hq, Polynomial.eval_mul, hFr, zero_mul]
    have hPr : P.eval r = 0 := by
      rw [Polynomial.eval_pow] at hPrpow
      exact (pow_eq_zero_iff (by omega : n - 1 ≠ 0)).mp hPrpow
    rw [hPfactor] at hPr
    simp only [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at hPr
    rcases mul_eq_zero.mp hPr with h | h
    · left; linarith
    · right; linarith
  have hsum : ∃ z : ℤ, F.roots.sum = (z : ℚ) * s := by
    have haux : ∀ R : Multiset ℚ,
        (∀ r ∈ R, r = (s : ℚ) ∨ r = -(s : ℚ)) →
        ∃ z : ℤ, R.sum = (z : ℚ) * s := by
      intro R
      induction R using Multiset.induction_on with
      | empty => intro _; exact ⟨0, by simp⟩
      | cons a R ih =>
        intro hall
        have ha := hall a (by simp)
        have htail : ∀ r ∈ R, r = (s : ℚ) ∨ r = -(s : ℚ) := by
          intro r hr
          exact hall r (by simp [hr])
        obtain ⟨z, hz⟩ := ih htail
        rcases ha with ha | ha
        · refine ⟨z + 1, ?_⟩
          simp only [Multiset.sum_cons, ha, hz]
          push_cast
          ring
        · refine ⟨z - 1, ?_⟩
          simp only [Multiset.sum_cons, ha, hz]
          push_cast
          ring
    exact haux F.roots hroot
  obtain ⟨z, hz⟩ := hsum
  have hnext : F.nextCoeff = (d : ℚ) := by
    simp [F, Polynomial.nextCoeff, hf_monic.natDegree_map, hf_deg,
      show n - 1 ≠ 0 by omega, show n - 1 - 1 = n - 2 by omega,
      Polynomial.coeff_map, hcoeff, φ]
  have htraceRoots := hsplitF.nextCoeff_eq_neg_sum_roots_of_monic hFmonic
  rw [hnext, hz] at htraceRoots
  have hdvdZ : (s : ℤ) ∣ (d : ℤ) := by
    refine ⟨-z, ?_⟩
    exact_mod_cast (show (d : ℚ) = (s : ℚ) * (-z : ℚ) by linarith)
  exact_mod_cast hdvdZ

include G hfree hd hdeven hmin hcard in
/-- The even first-order order is impossible. -/
theorem false_of_firstOrder_even : False := by
  obtain ⟨s, hs⟩ := d_sub_two_is_square_of_firstOrder_even
    G hfree hd hdeven hmin hcard
  have hsdvd := sqrt_d_sub_two_dvd_d_of_firstOrder_even
    G hfree hd hdeven hmin hcard s hs
  have hspos : 1 ≤ s := by
    by_contra h
    have hs0 : s = 0 := by omega
    subst s
    simp at hs
    omega
  have hdval : d = s * s + 2 := by omega
  obtain ⟨a, ha⟩ := hsdvd
  have has : s ≤ a := by
    rw [hdval] at ha
    nlinarith
  have hsdvd2 : s ∣ 2 := by
    refine ⟨a - s, ?_⟩
    rw [hdval] at ha
    rw [Nat.mul_sub_left_distrib]
    omega
  have hsle : s ≤ 2 := Nat.le_of_dvd (by omega) hsdvd2
  have hsmall := degree_ne_four_and_ne_six_of_firstOrder_even
    G hfree hmin hcard
  interval_cases s
  · norm_num at hs
    subst d
    norm_num [Nat.even_iff] at hdeven
  · norm_num at hs
    apply hsmall.2
    omega


end

/-- No even-degree first-order near-Moore graph exists. -/
theorem containsC4_of_even_firstOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 3 ≤ d) (hdeven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2) :
    containsC4 V G := by
  classical
  by_contra hfree
  letI : DecidableRel (antipodalGraph G).Adj := Classical.decRel _
  exact false_of_firstOrder_even G hfree hd hdeven hmin hcard

/-- The first order above the strict Moore bound is impossible for every
degree `d≥3`, without a parity assumption. -/
theorem containsC4_of_firstOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 3 ≤ d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2) :
    containsC4 V G := by
  rcases Nat.even_or_odd d with hdeven | hodd
  · exact containsC4_of_even_firstOrder G hd hdeven hmin hcard
  · exact containsC4_of_odd_firstOrder G hd hodd hmin hcard

/-- **Second strict Moore bound.** Every finite `C₄`-free graph of minimum
degree at least `d≥3` has at least `d(d-1)+3` vertices. -/
theorem second_strict_moore_bound
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d)
    (hmin : d ≤ G.minDegree) :
    d * (d - 1) + 3 ≤ Fintype.card V := by
  have hbase := mul_pred_add_two_le_card_of_c4Free_minDegree
    G hd hmin hfree
  by_contra hnot
  have heq : Fintype.card V = d * (d - 1) + 2 := by omega
  exact hfree (containsC4_of_firstOrder G hd hmin heq)

/-- Threshold form of the parity-free second strict Moore bound. -/
theorem minDegreeForC4_firstOrder_le
    {d : ℕ} (hd : 3 ≤ d) :
    minDegreeForC4 (d * (d - 1) + 2) ≤ d := by
  apply Nat.sInf_le
  intro G _ hmin
  exact containsC4_of_firstOrder G hd hmin (by simp)

end Erdos85
