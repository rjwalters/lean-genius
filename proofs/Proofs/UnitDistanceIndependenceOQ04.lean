/-
# Fractional chromatic lower bound for the unit-distance graph on ℝ²

Open question `unit-distance-independence-oq-04` (Frankl–Wilson 1981):

    The fractional chromatic number of the unit-distance graph on the plane
    satisfies  χ_f(ℝ²) ≥ 3.5,

strengthening the integer bound χ(ℝ²) ≥ 4 (De Grey 2018 even gives ≥ 5).

## What this file proves (axiom-free)

The mathematical engine behind every fractional-chromatic lower bound is the
LP-duality inequality

        χ_f(G) ≥ |V(G)| / α(G)                                      (★)

for every finite graph `G`, where `α(G)` is the independence number.  We
formalise a self-contained fractional chromatic number for finite graphs (the
fractional set-cover LP over independent sets) and prove (★) by the standard
double-counting / averaging argument:

  * every vertex must be covered with total weight ≥ 1, so summing over the
    `|V|` vertices gives `|V| ≤ ∑_I |I| · w(I)`;
  * each weighted set is independent, hence `|I| ≤ α(G)`, giving
    `∑_I |I| · w(I) ≤ α(G) · ∑_I w(I)`.

Dividing yields `∑_I w(I) ≥ |V|/α(G)` for every fractional colouring `w`, so the
infimum `χ_f(G)` is `≥ |V|/α(G)`.

Specialising (★) to any 7-vertex graph with independence number `2` — the
combinatorial signature of the **Moser spindle**, a unit-distance graph in the
plane — gives `χ_f ≥ 7/2 = 3.5`.  The last step, an explicit ℝ²-embedding of
the Moser spindle with all eleven unit distances verified, is recorded as the
remaining open piece in the knowledge base.

## Status

0 axioms, 0 sorries.  `fractionalChromaticNumber` and the bound `(★)` are fully
machine-checked (modulo the ordinary `propext / Classical.choice / Quot.sound`).
This is genuine reusable infrastructure: `(★)` converts *any* independence-ratio
certificate into a fractional chromatic lower bound.
-/
import Mathlib
import Proofs.UnitDistanceIndependence

open Finset

namespace UnitDistanceIndependence.FractionalChromatic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## A fractional chromatic number for finite graphs

A *fractional colouring* is a nonnegative weight `w I` on each finite vertex set
`I`, supported on independent sets, such that every vertex is covered with total
weight at least `1`.  Its cost is `∑_I w I`; the fractional chromatic number is
the infimum of the cost over all fractional colourings. -/

/-- The collection of all vertex subsets, as a `Finset (Finset V)`. -/
noncomputable def allSets : Finset (Finset V) := (Finset.univ : Finset V).powerset

/-- A fractional colouring of `G`: a nonnegative weighting of vertex subsets,
supported on independent sets, that covers every vertex with weight `≥ 1`. -/
def IsFracColoring (G : SimpleGraph V) [DecidableRel G.Adj] (w : Finset V → ℝ) : Prop :=
  (∀ I : Finset V, 0 ≤ w I) ∧
  (∀ I : Finset V, w I ≠ 0 → IsIndepFinset G I) ∧
  (∀ v : V, 1 ≤ ∑ I ∈ allSets.filter (fun I => v ∈ I), w I)

/-- The cost `∑_I w I` of a fractional colouring. -/
noncomputable def fracCost (w : Finset V → ℝ) : ℝ := ∑ I ∈ allSets, w I

/-- The set of achievable fractional-colouring costs of `G`. -/
noncomputable def costSet (G : SimpleGraph V) [DecidableRel G.Adj] : Set ℝ :=
  { x | ∃ w, IsFracColoring G w ∧ fracCost w = x }

/-- **Fractional chromatic number** of a finite graph: the infimum of the cost
over all fractional colourings. -/
noncomputable def fractionalChromaticNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sInf (costSet G)

/-! ## The singleton colouring: `costSet` is nonempty and bounded below -/

/-- Any fractional colouring has nonnegative cost. -/
theorem fracCost_nonneg {G : SimpleGraph V} [DecidableRel G.Adj]
    {w : Finset V → ℝ} (hw : IsFracColoring G w) : 0 ≤ fracCost w :=
  Finset.sum_nonneg (fun I _ => hw.1 I)

/-- `costSet G` is bounded below by `0`. -/
theorem costSet_bddBelow (G : SimpleGraph V) [DecidableRel G.Adj] :
    BddBelow (costSet G) := by
  refine ⟨0, ?_⟩
  rintro x ⟨w, hw, rfl⟩
  exact fracCost_nonneg hw

/-- The indicator weighting of singletons: `w I = 1` if `I` is a singleton, else `0`. -/
noncomputable def singletonWeight : Finset V → ℝ := fun I => if I.card = 1 then 1 else 0

omit [Fintype V] [DecidableEq V] in
theorem singletonWeight_nonneg (I : Finset V) : 0 ≤ singletonWeight I := by
  unfold singletonWeight; split <;> norm_num

/-- The singleton weighting is a valid fractional colouring of any graph. -/
theorem isFracColoring_singletonWeight (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsFracColoring G (singletonWeight (V := V)) := by
  refine ⟨fun I => singletonWeight_nonneg I, ?_, ?_⟩
  · -- support on independent sets: a singleton is independent
    intro I hI
    have hcard : I.card = 1 := by
      unfold singletonWeight at hI; by_contra h; simp [h] at hI
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
    intro u hu v hv huv
    rw [Finset.mem_singleton] at hu hv
    exact absurd (hu.trans hv.symm) huv
  · -- every vertex is covered with weight ≥ 1 (its own singleton contributes 1)
    intro v
    have hmem : ({v} : Finset V) ∈ allSets.filter (fun I => v ∈ I) := by
      rw [Finset.mem_filter]
      refine ⟨?_, Finset.mem_singleton_self v⟩
      rw [allSets, Finset.mem_powerset]; exact Finset.subset_univ _
    have hval : singletonWeight ({v} : Finset V) = 1 := by
      unfold singletonWeight; simp
    calc (1 : ℝ) = singletonWeight ({v} : Finset V) := hval.symm
      _ ≤ ∑ I ∈ allSets.filter (fun I => v ∈ I), singletonWeight I :=
          Finset.single_le_sum (fun I _ => singletonWeight_nonneg I) hmem

theorem costSet_nonempty (G : SimpleGraph V) [DecidableRel G.Adj] :
    (costSet G).Nonempty :=
  ⟨fracCost (singletonWeight (V := V)), singletonWeight (V := V),
    isFracColoring_singletonWeight G, rfl⟩

/-! ## The key double-counting identity and the `|V|/α` bound -/

/-- **Double counting.** Summing each vertex's covering weight over all vertices
equals the size-weighted total `∑_I |I| · w I`. -/
theorem sum_coverage_eq (G : SimpleGraph V) [DecidableRel G.Adj] (w : Finset V → ℝ) :
    (∑ v : V, ∑ I ∈ allSets.filter (fun I => v ∈ I), w I)
      = ∑ I ∈ allSets, (I.card : ℝ) * w I := by
  -- Replace the inner filtered sum by an `if`-guarded sum over all of `allSets`.
  have step1 : ∀ v : V, (∑ I ∈ allSets.filter (fun I => v ∈ I), w I)
      = ∑ I ∈ allSets, (if v ∈ I then w I else 0) := by
    intro v; rw [Finset.sum_filter]
  simp_rw [step1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  -- `∑_v (if v ∈ I then w I else 0) = |I| • w I`
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

/-- **Cost lower bound.** Every fractional colouring of a nonempty-vertex graph
costs at least `|V| / α(G)`. -/
theorem card_div_indep_le_fracCost
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {w : Finset V → ℝ} (hw : IsFracColoring G w) :
    (Fintype.card V : ℝ) / (independenceNumber G : ℝ) ≤ fracCost w := by
  by_cases hα : independenceNumber G = 0
  · -- `α = 0` forces `V` empty, so `|V| = 0` and the bound is `0 ≤ cost`.
    rw [hα]; simp only [Nat.cast_zero, div_zero]
    exact fracCost_nonneg hw
  have hαpos : 0 < independenceNumber G := Nat.pos_of_ne_zero hα
  have hαR : (0 : ℝ) < (independenceNumber G : ℝ) := by exact_mod_cast hαpos
  rw [div_le_iff₀ hαR, mul_comm]
  -- `|V| = ∑_v 1 ≤ ∑_v coverage(v) = ∑_I |I| w I ≤ α · ∑_I w I = α · cost`.
  have hcover : (Fintype.card V : ℝ)
      ≤ ∑ v : V, ∑ I ∈ allSets.filter (fun I => v ∈ I), w I := by
    calc (Fintype.card V : ℝ) = ∑ _v : V, (1 : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      _ ≤ ∑ v : V, ∑ I ∈ allSets.filter (fun I => v ∈ I), w I :=
              Finset.sum_le_sum (fun v _ => hw.2.2 v)
  have hdc := sum_coverage_eq G w
  have hbound : ∑ I ∈ allSets, (I.card : ℝ) * w I
      ≤ (independenceNumber G : ℝ) * fracCost w := by
    rw [fracCost, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro I _
    by_cases hwI : w I = 0
    · rw [hwI]; simp
    · have hindep : IsIndepFinset G I := hw.2.1 I hwI
      have hcardα : (I.card : ℝ) ≤ (independenceNumber G : ℝ) := by
        exact_mod_cast indep_card_le_alpha G I hindep
      have hwpos : 0 ≤ w I := hw.1 I
      calc (I.card : ℝ) * w I ≤ (independenceNumber G : ℝ) * w I :=
              mul_le_mul_of_nonneg_right hcardα hwpos
        _ = (independenceNumber G : ℝ) * w I := rfl
  calc (Fintype.card V : ℝ)
      ≤ ∑ v : V, ∑ I ∈ allSets.filter (fun I => v ∈ I), w I := hcover
    _ = ∑ I ∈ allSets, (I.card : ℝ) * w I := hdc
    _ ≤ (independenceNumber G : ℝ) * fracCost w := hbound

/-- **Fractional clique / LP lower bound (★).** For every finite graph `G`,
`χ_f(G) ≥ |V| / α(G)`. -/
theorem card_div_indep_le_fractionalChromaticNumber
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Fintype.card V : ℝ) / (independenceNumber G : ℝ) ≤ fractionalChromaticNumber G := by
  rw [fractionalChromaticNumber]
  apply le_csInf (costSet_nonempty G)
  rintro x ⟨w, hw, rfl⟩
  exact card_div_indep_le_fracCost G hw

/-! ## The Moser-spindle specialisation

The **Moser spindle** is a unit-distance graph in ℝ² on `7` vertices whose
independence number is `2`.  Applying `(★)` to it yields `χ_f ≥ 7/2 = 3.5`.
Here we record the abstract combinatorial consequence; realising the spindle by
explicit unit-distance coordinates in `Plane` is the remaining open step. -/

/-- **Abstract Moser-spindle bound.** Any finite graph on exactly `7` vertices
with independence number `2` has fractional chromatic number `≥ 7/2 = 3.5`. -/
theorem fractionalChromaticNumber_ge_of_seven_indep_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 7) (hindep : independenceNumber G = 2) :
    (7 : ℝ) / 2 ≤ fractionalChromaticNumber G := by
  have h := card_div_indep_le_fractionalChromaticNumber G
  rw [hcard, hindep] at h
  norm_num at h
  linarith [h]

/-- Restatement in decimal form: such a graph has `χ_f ≥ 3.5`. -/
theorem fractionalChromaticNumber_ge_of_seven_indep_two' {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 7) (hindep : independenceNumber G = 2) :
    (3.5 : ℝ) ≤ fractionalChromaticNumber G := by
  have h := fractionalChromaticNumber_ge_of_seven_indep_two G hcard hindep
  norm_num at h ⊢
  linarith [h]

/-! ## A concrete Moser-spindle graph with `χ_f ≥ 3.5`

We realise the Moser spindle as an abstract graph on `Fin 7` with its standard
11-edge incidence and check, by decidable computation, that its independence
number is `2`.  Combined with the bound `(★)`, this exhibits a concrete finite
graph — combinatorially identical to the planar Moser spindle — with fractional
chromatic number `≥ 3.5`.

Vertex labels (two 60°/120° rhombi sharing the acute vertex `0`):
`0` = shared acute apex; `1,2` = obtuse vertices of rhombus 1, `3` = its far
apex; `4,5` = obtuse vertices of rhombus 2, `6` = its far apex; the spindle edge
joins the far apexes `3–6`. -/

/-- The edge relation of the Moser spindle on `Fin 7` (each undirected edge is
listed once; symmetry/irreflexivity are added by `SimpleGraph.fromRel`). -/
def moserRel : Fin 7 → Fin 7 → Prop := fun a b =>
  (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
  (a = 1 ∧ b = 3) ∨ (a = 2 ∧ b = 3) ∨
  (a = 0 ∧ b = 4) ∨ (a = 0 ∧ b = 5) ∨ (a = 4 ∧ b = 5) ∨
  (a = 4 ∧ b = 6) ∨ (a = 5 ∧ b = 6) ∨ (a = 3 ∧ b = 6)

instance : DecidableRel moserRel := fun a b => by unfold moserRel; infer_instance

/-- The **Moser spindle** as a simple graph on `Fin 7`. -/
def moserSpindle : SimpleGraph (Fin 7) := SimpleGraph.fromRel moserRel

instance : DecidableRel moserSpindle.Adj := fun a b => by
  unfold moserSpindle SimpleGraph.fromRel; infer_instance

/-- The Moser spindle has `7` vertices. -/
theorem moserSpindle_card : Fintype.card (Fin 7) = 7 := by simp

/-- The Moser spindle has independence number `2` (decidable check). -/
theorem moserSpindle_independenceNumber : independenceNumber moserSpindle = 2 := by decide

/-- **Concrete fractional chromatic bound.** The Moser spindle graph on `Fin 7`
has `χ_f ≥ 7/2 = 3.5`, a fully machine-checked witness of the Frankl–Wilson
lower bound at the graph level. -/
theorem moserSpindle_fractionalChromaticNumber_ge :
    (7 : ℝ) / 2 ≤ fractionalChromaticNumber moserSpindle :=
  fractionalChromaticNumber_ge_of_seven_indep_two moserSpindle
    moserSpindle_card moserSpindle_independenceNumber

/-! ## Isomorphism-invariance and transport to any realisation

The bound `χ_f ≥ 3.5` depends only on the *combinatorial type* of the Moser
spindle: it holds for **every** graph isomorphic to `moserSpindle`.  This gives
the clean coordinate-free bridge to the plane.  Concretely, once the spindle is
realised as a unit-distance graph — i.e. once one exhibits a graph isomorphism

    `moserSpindle ≃g unitDistGraph S`

for a suitable 7-point set `S ⊆ Plane` — the planar fractional-chromatic bound
`χ_f(unitDistGraph S) ≥ 3.5` follows immediately, with no further analysis of
the LP.  We prove the two invariances (`α` and the vertex count) and package
the resulting transport theorem.  All of this is axiom-free graph theory; the
only remaining ingredient for the full ℝ² claim is the explicit embedding
(eleven unit distances + ten non-unit distances), recorded in the knowledge
base as the open engineering step. -/

/-- A graph isomorphism carries independent finsets to independent finsets
(under the image map `S ↦ e '' S`), preserving cardinality. -/
theorem isIndepFinset_image_of_iso {V W : Type*} [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    {S : Finset V} (hS : IsIndepFinset G S) :
    IsIndepFinset H (S.image e) := by
  intro a ha b hb hab
  rw [Finset.mem_image] at ha hb
  obtain ⟨u, hu, rfl⟩ := ha
  obtain ⟨v, hv, rfl⟩ := hb
  have huv : u ≠ v := fun h => hab (by rw [h])
  rw [e.map_adj_iff]
  exact hS u hu v hv huv

/-- Every finite graph has an independent set whose cardinality attains the
independence number (the defining `sup` is realised, the empty set witnessing
nonemptiness of the family of independent sets). -/
theorem exists_indep_card_eq_independenceNumber
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ S : Finset V, IsIndepFinset G S ∧ S.card = independenceNumber G := by
  have hne : (Finset.univ.powerset.filter (fun S : Finset V =>
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.Adj u v)).Nonempty := by
    refine ⟨∅, ?_⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, by simp⟩
  obtain ⟨S, hSmem, hSsup⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hSmem
  exact ⟨S, hSmem.2, by rw [independenceNumber]; exact hSsup.symm⟩

/-- One `≤` direction of independence-number invariance: an isomorphism `G ≃g H`
gives `α(G) ≤ α(H)` (map an `α`-attaining independent set of `G` into `H`). -/
theorem independenceNumber_le_of_iso {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (e : G ≃g H) :
    independenceNumber G ≤ independenceNumber H := by
  obtain ⟨S, hS, hcard⟩ := exists_indep_card_eq_independenceNumber G
  have himg : IsIndepFinset H (S.image e) := isIndepFinset_image_of_iso e hS
  have hle : (S.image e).card ≤ independenceNumber H := indep_card_le_alpha H _ himg
  rw [Finset.card_image_of_injective S (EquivLike.injective e)] at hle
  omega

/-- **Independence number is a graph invariant.** A graph isomorphism preserves
the independence number. -/
theorem independenceNumber_congr {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (e : G ≃g H) :
    independenceNumber G = independenceNumber H :=
  le_antisymm (independenceNumber_le_of_iso G H e) (independenceNumber_le_of_iso H G e.symm)

/-- **Transport of the Moser-spindle bound.** Any finite graph isomorphic to the
Moser spindle has fractional chromatic number `≥ 7/2 = 3.5`. -/
theorem fractionalChromaticNumber_ge_of_iso_moserSpindle {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (e : moserSpindle ≃g H) :
    (7 : ℝ) / 2 ≤ fractionalChromaticNumber H := by
  have hcard : Fintype.card W = 7 := by
    have h1 := Fintype.card_congr e.toEquiv
    rw [moserSpindle_card] at h1
    exact h1.symm
  have hindep : independenceNumber H = 2 := by
    rw [← independenceNumber_congr moserSpindle H e]
    exact moserSpindle_independenceNumber
  exact fractionalChromaticNumber_ge_of_seven_indep_two H hcard hindep

/-- Decimal restatement of the transport theorem: `χ_f ≥ 3.5` for any realisation
of the Moser spindle. -/
theorem fractionalChromaticNumber_ge_of_iso_moserSpindle' {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (e : moserSpindle ≃g H) :
    (3.5 : ℝ) ≤ fractionalChromaticNumber H := by
  have h := fractionalChromaticNumber_ge_of_iso_moserSpindle H e
  norm_num at h ⊢
  linarith [h]

end UnitDistanceIndependence.FractionalChromatic
