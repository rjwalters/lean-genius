import Proofs.Erdos85Relabel

/-!
# Bipartite Cayley graphs from difference-Sidon sets

A set has the ordered-difference Sidon property when every nonzero ordered
difference has a unique representation.  Its bipartite development over a
finite additive group is regular and `C₄`-free.  This is the graph-theoretic
engine for a quadratic-conductor construction: once a size-`d` difference
Sidon set is embedded in `ZMod M`, it supplies a `d`-regular witness on `2M`
vertices.
-/

open SimpleGraph

namespace Erdos85

/-- Every nonzero ordered difference of elements of `A` has a unique
representation. -/
def IsDifferenceSidon {Γ : Type*} [AddCommGroup Γ]
    (A : Finset Γ) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A →
    ∀ ⦃c⦄, c ∈ A → ∀ ⦃d⦄, d ∈ A →
      a - b = c - d → a = b ∨ (a = c ∧ b = d)

/-- The bipartite Cayley development of `A`: a left vertex `x` is joined to
a right vertex `y` exactly when `y-x ∈ A`. -/
def differenceSidonCayleyGraph
    {Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ]
    (A : Finset Γ) : SimpleGraph (Sum Γ Γ) where
  Adj u v := match u, v with
    | Sum.inl x, Sum.inr y => y - x ∈ A
    | Sum.inr y, Sum.inl x => y - x ∈ A
    | _, _ => False
  symm := ⟨by
    intro u v huv
    cases u <;> cases v <;> simpa using huv⟩
  loopless := ⟨by
    intro u huu
    cases u <;> exact huu⟩

instance differenceSidonCayleyGraph_decidableRel
    {Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ]
    (A : Finset Γ) :
    DecidableRel (differenceSidonCayleyGraph A).Adj := by
  intro u v
  cases u <;> cases v <;> simp only [differenceSidonCayleyGraph]
  · exact instDecidableFalse
  · infer_instance
  · infer_instance
  · exact instDecidableFalse

@[simp] theorem differenceSidonCayleyGraph_adj_left_right
    {Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ]
    (A : Finset Γ) (x y : Γ) :
    (differenceSidonCayleyGraph A).Adj (Sum.inl x) (Sum.inr y) ↔
      y - x ∈ A := by
  rfl

@[simp] theorem differenceSidonCayleyGraph_adj_right_left
    {Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ]
    (A : Finset Γ) (x y : Γ) :
    (differenceSidonCayleyGraph A).Adj (Sum.inr y) (Sum.inl x) ↔
      y - x ∈ A := by
  rfl

@[simp] theorem differenceSidonCayleyGraph_not_adj_left_left
    {Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ]
    (A : Finset Γ) (x y : Γ) :
    ¬ (differenceSidonCayleyGraph A).Adj (Sum.inl x) (Sum.inl y) := by
  simp [differenceSidonCayleyGraph]

@[simp] theorem differenceSidonCayleyGraph_not_adj_right_right
    {Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ]
    (A : Finset Γ) (x y : Γ) :
    ¬ (differenceSidonCayleyGraph A).Adj (Sum.inr x) (Sum.inr y) := by
  simp [differenceSidonCayleyGraph]

/-- Every left vertex has degree `|A|`. -/
theorem differenceSidonCayleyGraph_degree_left
    {Γ : Type*} [Fintype Γ] [AddCommGroup Γ] [DecidableEq Γ]
    (A : Finset Γ) (x : Γ) :
    (differenceSidonCayleyGraph A).degree (Sum.inl x) = A.card := by
  let f : Γ ↪ Sum Γ Γ :=
    ⟨fun a => Sum.inr (a + x), by
      intro a b h
      simp only [Sum.inr.injEq] at h
      exact add_left_injective x h⟩
  have hneighbors :
      (differenceSidonCayleyGraph A).neighborFinset (Sum.inl x) =
        A.map f := by
    ext v
    rcases v with v | v
    · simp [SimpleGraph.mem_neighborFinset, f]
    · simp only [SimpleGraph.mem_neighborFinset,
        differenceSidonCayleyGraph_adj_left_right, Finset.mem_map]
      constructor
      · intro hv
        exact ⟨v - x, hv, by simp [f]⟩
      · rintro ⟨a, ha, hav⟩
        have : a + x = v := by simpa [f] using hav
        simpa [← this] using ha
  rw [SimpleGraph.degree, hneighbors, Finset.card_map]

/-- Every right vertex has degree `|A|`. -/
theorem differenceSidonCayleyGraph_degree_right
    {Γ : Type*} [Fintype Γ] [AddCommGroup Γ] [DecidableEq Γ]
    (A : Finset Γ) (y : Γ) :
    (differenceSidonCayleyGraph A).degree (Sum.inr y) = A.card := by
  let f : Γ ↪ Sum Γ Γ :=
    ⟨fun a => Sum.inl (y - a), by
      intro a b h
      simp only [Sum.inl.injEq] at h
      exact sub_right_injective h⟩
  have hneighbors :
      (differenceSidonCayleyGraph A).neighborFinset (Sum.inr y) =
        A.map f := by
    ext v
    rcases v with v | v
    · simp only [SimpleGraph.mem_neighborFinset,
        differenceSidonCayleyGraph_adj_right_left, Finset.mem_map]
      constructor
      · intro hv
        exact ⟨y - v, hv, by simp [f]⟩
      · rintro ⟨a, ha, hav⟩
        have : y - a = v := by simpa [f] using hav
        simpa [← this] using ha
    · simp [SimpleGraph.mem_neighborFinset, f]
  rw [SimpleGraph.degree, hneighbors, Finset.card_map]

/-- The bipartite Cayley development is regular of degree `|A|`. -/
theorem differenceSidonCayleyGraph_regular
    {Γ : Type*} [Fintype Γ] [AddCommGroup Γ] [DecidableEq Γ]
    (A : Finset Γ) (v : Sum Γ Γ) :
    (differenceSidonCayleyGraph A).degree v = A.card := by
  cases v with
  | inl x => exact differenceSidonCayleyGraph_degree_left A x
  | inr y => exact differenceSidonCayleyGraph_degree_right A y

/-- Two distinct vertices have at most one common neighbour in a
difference-Sidon Cayley graph. -/
theorem differenceSidonCayleyGraph_common_le_one
    {Γ : Type*} [Fintype Γ] [AddCommGroup Γ] [DecidableEq Γ]
    (A : Finset Γ) (hA : IsDifferenceSidon A)
    (u v : Sum Γ Γ) (huv : u ≠ v) :
    ((differenceSidonCayleyGraph A).neighborFinset u ∩
      (differenceSidonCayleyGraph A).neighborFinset v).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro z hz w hw
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
    SimpleGraph.mem_neighborFinset] at hz hw
  rcases u with x | x <;> rcases v with y | y
  · rcases z with z | z
    · exact (differenceSidonCayleyGraph_not_adj_left_left A x z hz.1).elim
    rcases w with w | w
    · exact (differenceSidonCayleyGraph_not_adj_left_left A x w hw.1).elim
    have hzx : z - x ∈ A := hz.1
    have hzy : z - y ∈ A := hz.2.symm
    have hwx : w - x ∈ A := hw.1
    have hwy : w - y ∈ A := hw.2.symm
    have hdiff : (z - x) - (z - y) = (w - x) - (w - y) := by abel
    rcases hA hzx hzy hwx hwy hdiff with heq | hpair
    · exfalso
      apply huv
      simp only [Sum.inl.injEq]
      exact sub_right_injective heq
    · simp only [Sum.inr.injEq]
      exact sub_left_injective hpair.1
  · rcases z with z | z
    · exact (differenceSidonCayleyGraph_not_adj_left_left A x z hz.1).elim
    · exact (differenceSidonCayleyGraph_not_adj_right_right A y z hz.2).elim
  · rcases z with z | z
    · exact (differenceSidonCayleyGraph_not_adj_left_left A y z hz.2).elim
    · exact (differenceSidonCayleyGraph_not_adj_right_right A x z hz.1).elim
  · rcases z with z | z
    · rcases w with w | w
      · have hxz : x - z ∈ A := hz.1
        have hyz : y - z ∈ A := hz.2.symm
        have hxw : x - w ∈ A := hw.1
        have hyw : y - w ∈ A := hw.2.symm
        have hdiff : (x - z) - (y - z) =
            (x - w) - (y - w) := by abel
        rcases hA hxz hyz hxw hyw hdiff with heq | hpair
        · exfalso
          apply huv
          simp only [Sum.inr.injEq]
          exact sub_left_injective heq
        · simp only [Sum.inl.injEq]
          exact sub_right_injective hpair.1
      · exact (differenceSidonCayleyGraph_not_adj_right_right
          A x w hw.1).elim
    · exact (differenceSidonCayleyGraph_not_adj_right_right
        A x z hz.1).elim

/-- The bipartite development of a difference-Sidon set is `C₄`-free. -/
theorem differenceSidonCayleyGraph_not_containsC4
    {Γ : Type*} [Fintype Γ] [AddCommGroup Γ] [DecidableEq Γ]
    (A : Finset Γ) (hA : IsDifferenceSidon A) :
    ¬ containsC4 (Sum Γ Γ) (differenceSidonCayleyGraph A) := by
  apply not_containsC4_of_forall_common_le_one
  intro u v huv
  exact differenceSidonCayleyGraph_common_le_one A hA u v huv

/-- A size-at-least-`d` difference-Sidon subset of `ZMod M` gives a
`d`-minimum-degree `C₄`-free witness on exactly `2M` vertices. -/
theorem c4FreeMinDegreeWitness_two_mul_of_differenceSidon
    {M d : ℕ} [NeZero M] (A : Finset (ZMod M))
    (hA : IsDifferenceSidon A) (hcardA : d ≤ A.card) :
    C4FreeMinDegreeWitness (2 * M) d := by
  let G := differenceSidonCayleyGraph A
  apply c4FreeMinDegreeWitness_of_card_eq G
  · simp only [Fintype.card_sum, ZMod.card]
    omega
  · apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro v
    rw [differenceSidonCayleyGraph_regular]
    exact hcardA
  · exact differenceSidonCayleyGraph_not_containsC4 A hA

end Erdos85
