import Proofs.Erdos85OrientedSquareBranch
import Proofs.Erdos85MixedParityComplete
import Proofs.Erdos85FrequencyScalar
import Proofs.Erdos85MixedSelection

/-!
# Termination of the mixed square frequency branch

The oriented trace sees precisely the forward-oriented selected components.
Under the mixed selection hypotheses every selected component has odd order,
so every selected diagonal block is forward.  Hence the oriented projected
anchor is the ordinary mixed projected anchor, whose three-point parity
pattern is already known.  Convolution constancy from the square branch then
contradicts that pattern, without any common-length assumption.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V C : Type*} [Fintype V] [DecidableEq V]
  [Fintype C] [DecidableEq C]
variable {ℓ : C → ℕ} [∀ c, NeZero (ℓ c)] {p : ℕ} [NeZero p]

/-- If every selected component is marked forward, the oriented and ordinary
mixed projected anchors coincide. -/
theorem orientedProjectedAnchor_eq_mixedProjectedAnchor_of_selected_forward
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) (o : C → Prop) [DecidablePred o]
    (hfwd : ∀ c, p ∣ ℓ c → o c) (s : ZMod p) :
    orientedProjectedAnchor G u o p s = mixedProjectedAnchor G u p s := by
  unfold orientedProjectedAnchor mixedProjectedAnchor
  apply Finset.sum_congr
  · ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact And.left
    · intro hc
      exact ⟨hc, hfwd c hc⟩
  · intro c hc
    rfl

/-- A three-point parity pattern cannot have the square-branch convolution
constancy.  This is the direct abstract bridge from `MixedParityComplete`
to the oriented frequency trace. -/
theorem false_of_oriented_convolution_constancy_of_threePoint_parity
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V)
    (hp7 : 7 ≤ p)
    (b : ZMod p) (hb : b + b = 1)
    (o : C → Prop) [DecidablePred o]
    (hfwd : ∀ c, p ∣ ℓ c → o c)
    (hoddPattern : ∀ y, Odd (mixedProjectedAnchor G u p y) ↔
      y ∉ ({0, b, -b} : Finset (ZMod p)))
    (hconstant : ∀ g,
      g ∉ ({0, b, -b, 1, -1} : Finset (ZMod p)) →
      cyclicConvolution
          (fun y ↦ (orientedProjectedAnchor G u o p y : ℤ))
          (fun y ↦ (orientedProjectedAnchor G u o p y : ℤ)) b =
        cyclicConvolution
          (fun y ↦ (orientedProjectedAnchor G u o p y : ℤ))
          (fun y ↦ (orientedProjectedAnchor G u o p y : ℤ)) g) : False := by
  have heq (y : ZMod p) : orientedProjectedAnchor G u o p y =
      mixedProjectedAnchor G u p y :=
    orientedProjectedAnchor_eq_mixedProjectedAnchor_of_selected_forward
      G u o hfwd y
  obtain ⟨err, herr⟩ := exists_integer_error_of_odd_iff
    (mixedProjectedAnchor G u p) ({0, b, -b} : Finset (ZMod p)) hoddPattern
  apply false_of_large_threePoint_convolution_pattern hp7 b hb
    (fun y ↦ (mixedProjectedAnchor G u p y : ℤ)) err herr
  intro g hg
  simpa only [heq] using hconstant g hg

/-- A half point modulo a prime at least seven avoids `0, ±1`. -/
theorem half_not_zero_one_neg_one {p : ℕ} [NeZero p]
    (hp7 : 7 ≤ p) (b : ZMod p) (hb : b + b = 1) :
    b ∉ ({0, 1, -1} : Finset (ZMod p)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [h] at hb
    have h1 : (1 : ZMod p) = 0 := by linear_combination -hb
    have := ZMod.one_eq_zero_iff.mp h1
    omega
  · intro h
    rw [h] at hb
    have h1 : (1 : ZMod p) = 0 := by linear_combination hb
    have := ZMod.one_eq_zero_iff.mp h1
    omega
  · intro h
    rw [h] at hb
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination -hb
    have hp3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3
    have := Nat.le_of_dvd (by norm_num : 0 < 3) hp3
    omega

/-- **Complete mixed square-branch terminal.**  A valid mixed selection prime
with odd selected lengths and odd selected-component count cannot lie in the
square frequency branch.  No two selected cycles need have the same length. -/
theorem false_of_graph_mixed_frequencyPair_square
    {K : Type*} [Field K] [CharZero K]
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ} [NeZero p]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) (hp7 : 7 ≤ p)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (hodd : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard → Odd c.supp.ncard)
    (hcountOdd : Odd (Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard)).card)
    (b : ZMod p) (hb : b + b = 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {s : K} (hs : s ≠ 0)
    (hscalar : (d : K) - 1 - (ζ + ζ⁻¹) = s * s) : False := by
  let D := secondOrderDefectGraph G
  have hcommZ := adjMatrix_comm_secondOrderDefect_of_even
    G hfree hd heven hmin hcard
  have hsqZ := adjMatrix_sq_eq_sub_secondOrderDefect_of_even
    G hfree hd heven hmin hcard
  have hfwd : ∀ c : D.ConnectedComponent,
      p ∣ c.supp.ncard → forwardOriented G u c := by
    intro c hpc x y
    exact graph_equalOddCycle_diagBlock_adj_shift_iff (hℓ3 c)
      (hodd c hpc) G D (u c) (hu c) hcommZ (huD c) x y
  have hoddPattern : ∀ y, Odd (mixedProjectedAnchor G u p y) ↔
      y ∉ ({0, b, -b} : Finset (ZMod p)) := by
    intro y
    exact odd_mixedProjectedAnchor_iff_threePoint G hfree hd heven hmin
      hcard hp hp7 u hu huRange huD hℓ3 hodd hcountOdd b hb y
  have ha := half_not_zero_one_neg_one hp7 b hb
  have hconstant := graph_forwardOriented_convolution_constant_of_square
    G D hfree u hℓ3 hbij huD hcommZ hsqZ hp (by omega) hζ hs hscalar b ha
  exact false_of_oriented_convolution_constancy_of_threePoint_parity
    G u hp7 b hb (forwardOriented G u) hfwd hoddPattern hconstant

/-- The same mixed selection hypotheses also rule out the nonsquare branch:
the Fourier trace would make every projected anchor count equal, contradicting
the three-point parity pattern. -/
theorem false_of_graph_mixed_frequencyPair_nonsquare
    {K : Type*} [Field K] [CharZero K]
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ} [NeZero p]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) (hp7 : 7 ≤ p)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (hodd : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard → Odd c.supp.ncard)
    (hcountOdd : Odd (Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard)).card)
    (b : ZMod p) (hb : b + b = 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hns : ¬ IsSquare ((d : K) - 1 - (ζ + ζ⁻¹))) : False := by
  let D := secondOrderDefectGraph G
  have hcommZ := adjMatrix_comm_secondOrderDefect_of_even
    G hfree hd heven hmin hcard
  have hsqZ := adjMatrix_sq_eq_sub_secondOrderDefect_of_even
    G hfree hd heven hmin hcard
  have hall := mixedProjectedAnchor_all_eq_of_nonsquare G D u hℓ3 hbij
    huD hcommZ hsqZ hodd hp (by omega) hζ hns
  have hpattern : ∀ y, Odd (mixedProjectedAnchor G u p y) ↔
      y ∉ ({0, b, -b} : Finset (ZMod p)) := by
    intro y
    exact odd_mixedProjectedAnchor_iff_threePoint G hfree hd heven hmin
      hcard hp hp7 u hu huRange huD hℓ3 hodd hcountOdd b hb y
  have hbSpecial := half_not_zero_one_neg_one hp7 b hb
  have h1outside : (1 : ZMod p) ∉ ({0, b, -b} : Finset (ZMod p)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbSpecial
    refine ⟨?_, (fun h ↦ hbSpecial.2.1 h.symm), ?_⟩
    · intro h
      have := ZMod.one_eq_zero_iff.mp h
      omega
    · intro h
      apply hbSpecial.2.2
      have hn := congrArg Neg.neg h
      simpa using hn.symm
  have hzeroNotOdd : ¬ Odd (mixedProjectedAnchor G u p 0) := by
    rw [hpattern]
    simp
  have honeOdd : Odd (mixedProjectedAnchor G u p 1) :=
    (hpattern 1).mpr h1outside
  rw [hall 1 0] at honeOdd
  exact hzeroNotOdd honeOdd

/-- **Complete mixed prime-frequency dichotomy.** Every valid mixed selection
prime is impossible: over `ℂ` the nonzero frequency scalar is either a square
or a nonsquare, and both branches above contradict the mixed three-point
parity theorem. -/
theorem false_of_graph_mixed_frequencyPair_prime
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ} [NeZero p]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) (hp7 : 7 ≤ p)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (hodd : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard → Odd c.supp.ncard)
    (hcountOdd : Odd (Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard)).card)
    (b : ZMod p) (hb : b + b = 1)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p) : False := by
  let scalar : ℂ := (d : ℂ) - 1 - (ζ + ζ⁻¹)
  have hscalar0 : scalar ≠ 0 := complex_frequencyScalar_ne_zero hd hζ
  by_cases hsquare : IsSquare scalar
  · obtain ⟨s, hs⟩ := hsquare
    have hscalar : scalar = s * s := by simpa [pow_two] using hs
    have hs0 : s ≠ 0 := by
      intro hszero
      apply hscalar0
      rw [hscalar, hszero]
      simp
    exact false_of_graph_mixed_frequencyPair_square G hfree hd heven hmin
      hcard hp hp7 u hu huRange huD hℓ3 hbij hodd hcountOdd b hb hζ hs0
      hscalar
  · exact false_of_graph_mixed_frequencyPair_nonsquare G hfree hd heven hmin
      hcard hp hp7 u hu huRange huD hℓ3 hbij hodd hcountOdd b hb hζ hsquare

/-- **Selection obstruction for every extremal graph.**  Since the complete
mixed frequency dichotomy rules out every valid selection prime, the family
of defect-component orders must satisfy `SelectionObstructed`. -/
theorem secondOrder_componentOrders_selectionObstructed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    SelectionObstructed (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦ c.supp.ncard) := by
  classical
  obtain ⟨u, hu, huRange, huD, hℓ3⟩ :=
    exists_mixed_cycle_labeling G hfree hd heven hmin hcard
  letI : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard := fun c ↦ ⟨Nat.ne_of_gt (by
        have hc := hℓ3 c
        omega)⟩
  have hsep : ∀ {c e : (secondOrderDefectGraph G).ConnectedComponent},
      c ≠ e → ∀ x y, u c x ≠ u e y := by
    intro c e hce x y hxy
    have hxc : u c x ∈ c.supp := by
      rw [← huRange c]
      exact ⟨x, rfl⟩
    have hye : u e y ∈ e.supp := by
      rw [← huRange e]
      exact ⟨y, rfl⟩
    have hc := (SimpleGraph.ConnectedComponent.mem_supp_iff c (u c x)).mp hxc
    have he := (SimpleGraph.ConnectedComponent.mem_supp_iff e (u e y)).mp hye
    apply hce
    rw [hxy] at hc
    exact hc.symm.trans he
  have hcover : ∀ v : V, ∃ c x, u c x = v := by
    intro v
    let c := (secondOrderDefectGraph G).connectedComponentMk v
    have hv : v ∈ c.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c v).mpr rfl
    rw [← huRange c] at hv
    obtain ⟨x, hx⟩ := hv
    exact ⟨c, x, hx⟩
  have hbij : Function.Bijective (mixedCycleLabeling u) :=
    mixedCycleLabeling_bijective hu hsep hcover
  rcases exists_selection_or_obstructed (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦ c.supp.ncard) with
    ⟨p, hp, hp7, hodd, hcountOdd⟩ | hobs
  · letI : NeZero p := ⟨hp.ne_zero⟩
    have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
    obtain ⟨k, hk⟩ := hpOdd
    let b : ZMod p := ((k + 1 : ℕ) : ZMod p)
    have hb : b + b = 1 := by
      have h2 : (k + 1) + (k + 1) = p + 1 := by omega
      dsimp [b]
      rw [← Nat.cast_add, h2]
      push_cast [ZMod.natCast_self]
      ring
    let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)
    have hζ : IsPrimitiveRoot ζ p :=
      Complex.isPrimitiveRoot_exp p hp.ne_zero
    exact (false_of_graph_mixed_frequencyPair_prime G hfree hd heven hmin
      hcard hp hp7 u hu huRange huD hℓ3 hbij hodd hcountOdd b hb hζ).elim
  · exact hobs

end

end Erdos85
