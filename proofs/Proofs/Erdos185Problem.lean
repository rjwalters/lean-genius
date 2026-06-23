/-
Erdős Problem #185: Cap Sets in {0,1,2}^n

Source: https://erdosproblems.com/185
Status: PROVED (Furstenberg-Katznelson 1991)

Statement:
Let f₃(n) be the maximal size of a subset of {0,1,2}^n which contains no three
points on a line. Is it true that f₃(n) = o(3^n)?

Answer: YES - Follows from the density Hales-Jewett theorem.

Background:
- Originally posed by Moser
- Three points x, y, z are on a line if x + z = 2y (componentwise mod 3)
- f₃(n) ≥ R₃(3^n) where R₃(N) = max AP-free subset of {1,...,N}
- Moser: f₃(n) ≫ 3^n/√n

Resolution:
Furstenberg-Katznelson (1991) proved the density Hales-Jewett theorem,
which implies f₃(n) = o(3^n).

Related: OEIS A003142, Cap set problem in finite geometry
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Asymptotics Filter

namespace Erdos185

/-
## Part I: Basic Definitions
-/

/--
**The ternary hypercube:**
{0, 1, 2}^n represented as functions from Fin n to ZMod 3.
-/
abbrev TernaryHypercube (n : ℕ) := Fin n → ZMod 3

/--
**Cardinality of the hypercube:**
|{0,1,2}^n| = 3^n.
-/
theorem hypercube_card (n : ℕ) :
    Fintype.card (TernaryHypercube n) = 3^n := by
  simp [TernaryHypercube]

/-
## Part II: Lines in {0,1,2}^n
-/

/--
**Collinear (on a line):**
Three points x, y, z in {0,1,2}^n are on a line if x + z = 2y (in ZMod 3).
Equivalently, y is the "midpoint" of x and z.
-/
def OnLine (x y z : TernaryHypercube n) : Prop :=
  ∀ i : Fin n, x i + z i = 2 * y i

/-- OnLine is symmetric in the outer arguments: if x+z=2y then z+x=2y. -/
theorem onLine_symm {x y z : TernaryHypercube n} (h : OnLine x y z) :
    OnLine z y x := by
  intro i
  have := h i
  rw [add_comm]
  exact this

/-- OnLine is decidable for finite n. -/
instance instDecidableOnLine {n : ℕ} (x y z : TernaryHypercube n) :
    Decidable (OnLine x y z) := by
  unfold OnLine
  infer_instance

/--
**Combinatorial line:**
A line in {0,1,2}^n parameterized by a subset of coordinates.
For non-varying coordinates, we fix a value; for varying ones, we take 0, 1, 2.
-/
structure CombinatorialLine (n : ℕ) where
  varying : Finset (Fin n)    -- Coordinates that vary
  fixed : Fin n → ZMod 3      -- Values for non-varying coordinates
  nonempty : varying.Nonempty -- At least one coordinate varies

/--
**Points on a combinatorial line:**
A combinatorial line contains exactly 3 points.
-/
def CombinatorialLine.points (L : CombinatorialLine n) : Finset (TernaryHypercube n) :=
  Finset.univ.image (fun t : ZMod 3 => fun i =>
    if i ∈ L.varying then t else L.fixed i)

/-
## Part III: Cap Sets
-/

/--
**Cap Set:**
A subset of {0,1,2}^n with no three collinear points.
-/
def IsCapSet (S : Finset (TernaryHypercube n)) : Prop :=
  ∀ x y z : TernaryHypercube n, x ∈ S → y ∈ S → z ∈ S →
    x ≠ y → y ≠ z → x ≠ z → ¬OnLine x y z

/--
**Cap set (combinatorial line version):**
No combinatorial line is contained in S.
-/
def IsCapSetCombinatorial (S : Finset (TernaryHypercube n)) : Prop :=
  ∀ L : CombinatorialLine n, ¬(L.points ⊆ S)

/-- The empty set is a cap set. -/
theorem isCapSet_empty : IsCapSet (∅ : Finset (TernaryHypercube n)) := by
  intro x _ _ hx
  exact absurd hx (Finset.notMem_empty x)

/-- Any pair of distinct points forms a cap set. -/
theorem isCapSet_pair (a b : TernaryHypercube n) (hab : a ≠ b) :
    IsCapSet ({a, b} : Finset (TernaryHypercube n)) := by
  intro x y z hx hy hz hxy hyz hxz
  simp [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
  -- Each of x, y, z is either a or b, but they're all distinct — impossible with 2 values
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    simp_all

/-- Subsets of cap sets are cap sets. -/
theorem isCapSet_subset {S T : Finset (TernaryHypercube n)} (hST : S ⊆ T) (hT : IsCapSet T) :
    IsCapSet S :=
  fun x y z hx hy hz hxy hyz hxz => hT x y z (hST hx) (hST hy) (hST hz) hxy hyz hxz

/-- A singleton is a cap set. -/
theorem isCapSet_singleton (a : TernaryHypercube n) :
    IsCapSet ({a} : Finset (TernaryHypercube n)) := by
  intro x _ _ hx hy _
  simp at hx hy; subst hx; subst hy; intro h; exact absurd rfl h

/--
**f₃(n):**
The maximum size of a cap set in {0,1,2}^n.
-/
noncomputable def f3 (n : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ S : Finset (TernaryHypercube n), IsCapSet S ∧ S.card = m }

/-- The set of achievable cap set cardinalities is bounded above by 3^n. -/
private lemma f3_bddAbove (n : ℕ) :
    BddAbove { m : ℕ | ∃ S : Finset (TernaryHypercube n), IsCapSet S ∧ S.card = m } :=
  ⟨3^n, fun m hm => by
    obtain ⟨S, _, rfl⟩ := hm
    calc S.card ≤ (Finset.univ : Finset (TernaryHypercube n)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card (TernaryHypercube n) := by rw [Finset.card_univ]
      _ = 3^n := hypercube_card n⟩

/-- The set of achievable cap set cardinalities is nonempty (the empty set is always a cap set). -/
private lemma f3_nonempty (n : ℕ) :
    (0 : ℕ) ∈ { m : ℕ | ∃ S : Finset (TernaryHypercube n), IsCapSet S ∧ S.card = m } :=
  ⟨∅, isCapSet_empty, rfl⟩

/-- f₃(0) = 1: the hypercube {0,1,2}^0 has exactly one element. -/
theorem f3_0 : f3 0 = 1 := by
  unfold f3
  apply le_antisymm
  · apply csSup_le ⟨0, f3_nonempty 0⟩
    rintro m ⟨S, _, rfl⟩
    calc S.card ≤ (Finset.univ : Finset (TernaryHypercube 0)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card (TernaryHypercube 0) := by rw [Finset.card_univ]
      _ = 3^0 := hypercube_card 0
      _ = 1 := by norm_num
  · apply le_csSup (f3_bddAbove 0)
    show ∃ S : Finset (TernaryHypercube 0), IsCapSet S ∧ S.card = 1
    exact ⟨{fun _ => 0}, isCapSet_singleton _, by simp⟩

/-- f₃(n) ≤ 3^n: a cap set cannot be larger than the entire hypercube. -/
theorem f3_le_three_pow (n : ℕ) : f3 n ≤ 3^n := by
  unfold f3
  apply csSup_le ⟨0, f3_nonempty n⟩
  rintro m ⟨S, _, rfl⟩
  calc S.card ≤ (Finset.univ : Finset (TernaryHypercube n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card (TernaryHypercube n) := by rw [Finset.card_univ]
    _ = 3^n := hypercube_card n

/-- f₃(n) ≥ 1 for all n: the singleton {0,...,0} is a cap set. -/
theorem f3_ge_one (n : ℕ) : f3 n ≥ 1 := by
  unfold f3
  apply le_csSup (f3_bddAbove n)
  show ∃ S : Finset (TernaryHypercube n), IsCapSet S ∧ S.card = 1
  exact ⟨{fun _ => 0}, isCapSet_singleton _, by simp⟩

/-- f₃(n) ≥ 2 for n ≥ 1: any two distinct points form a cap set, and they exist for n ≥ 1. -/
theorem f3_ge_two (n : ℕ) (hn : n ≥ 1) : f3 n ≥ 2 := by
  unfold f3
  apply le_csSup (f3_bddAbove n)
  show ∃ S : Finset (TernaryHypercube n), IsCapSet S ∧ S.card = 2
  have hdist : (fun _ : Fin n => (0 : ZMod 3)) ≠ (fun _ => 1) := by
    intro h
    have := congr_fun h ⟨0, by omega⟩
    simp at this
  exact ⟨{fun _ => 0, fun _ => 1}, isCapSet_pair _ _ hdist, Finset.card_pair hdist⟩

/-- The union of empty sets is a cap set. -/
theorem isCapSet_union_empty {S : Finset (TernaryHypercube n)} (hS : IsCapSet S) :
    IsCapSet (S ∪ ∅) := by
  simp [hS]

/-- Monotonicity: if n ≤ m, there's a relationship between hypercubes. -/
theorem hypercube_card_mono {n m : ℕ} (h : n ≤ m) :
    Fintype.card (TernaryHypercube n) ≤ Fintype.card (TernaryHypercube m) := by
  simp only [hypercube_card]
  exact Nat.pow_le_pow_right (by omega) h

/-- f₃(n) is always positive. -/
theorem f3_pos (n : ℕ) : 0 < f3 n := by
  have := f3_ge_one n
  omega

/-- f₃(0) = 1 implies the singleton is the only cap set in dimension 0. -/
theorem f3_0_unique (S : Finset (TernaryHypercube 0)) (hS : IsCapSet S) :
    S.card ≤ 1 := by
  have hf := f3_0
  calc S.card
      ≤ f3 0 := by
        unfold f3
        apply le_csSup (f3_bddAbove 0)
        exact ⟨S, hS, rfl⟩
    _ = 1 := hf

/-
## Part IV: Connection to Arithmetic Progressions
-/

/--
**R₃(N):**
The maximum size of a subset of {1,...,N} with no 3-term arithmetic progression.
-/
noncomputable def R3 (N : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ S : Finset ℕ, (∀ x ∈ S, x ≤ N) ∧
    (∀ a d : ℕ, d > 0 → a ∈ S → a + d ∈ S → a + 2*d ∈ S → False) ∧ S.card = m }

/--
**Trivial lower bound:**
f₃(n) ≥ R₃(3^n).

The embedding is: {1,...,3^n} ↪ {0,1,2}^n via ternary representation.
AP-free sets embed to cap sets (lines generalize APs).
-/
/-
## Part V: Known Bounds
-/

/--
**Moser's Lower Bound:**
f₃(n) ≫ 3^n/√n.

More precisely, f₃(n) ≥ c · 3^n/√n for some constant c > 0.
-/
/--
**Moser's construction:**
Taking points with coordinates summing to 0 or 1 (mod 3) gives a large cap set.
-/
def moserSet (n : ℕ) : Finset (TernaryHypercube n) :=
  Finset.univ.filter (fun x => (Finset.univ.sum x) = 0 ∨ (Finset.univ.sum x) = 1)

/-
**Moser set and combinatorial lines:**
The Moser set does NOT avoid all combinatorial lines.
Counterexample: for n ≡ 0 mod 3 (e.g., n=3), the diagonal line (0,...,0),(1,...,1),(2,...,2)
has coordinate sums 0, n, 2n. When 3 | n, all sums ≡ 0, so all are in {0,1} and
the full line lies in moserSet n. The Moser set only avoids lines where |varying| ≢ 0 (mod 3).
(Previous axiom moser_set_is_cap_combinatorial was FALSE and has been removed.)
-/

/-- The Moser set for n=3 is NOT a cap set: the three constant points
    (0,0,0), (1,1,1), (2,2,2) are all in moserSet 3 (sums 0, 0, 0 mod 3)
    and they form a collinear triple (OnLine). -/
theorem moserSet_not_capSet_3 : ¬IsCapSet (moserSet 3) := by
  intro h
  -- The three constant points
  let p0 : TernaryHypercube 3 := fun _ => 0
  let p1 : TernaryHypercube 3 := fun _ => 1
  let p2 : TernaryHypercube 3 := fun _ => 2
  -- They are in the Moser set (coordinate sums are 0, 3≡0, 6≡0 mod 3)
  have h0 : p0 ∈ moserSet 3 := by decide
  have h1 : p1 ∈ moserSet 3 := by decide
  have h2 : p2 ∈ moserSet 3 := by decide
  -- They are distinct
  have hne01 : p0 ≠ p1 := by decide
  have hne12 : p1 ≠ p2 := by decide
  have hne02 : p0 ≠ p2 := by decide
  -- They are collinear: p0 + p2 = 2 * p1 (coordinatewise in ZMod 3)
  have hline : OnLine p0 p1 p2 := by
    intro i; fin_cases i <;> decide
  -- This contradicts the cap set property
  exact h p0 p1 p2 h0 h1 h2 hne01 hne12 hne02 hline

/-
## Part VI: The Main Result - Density Hales-Jewett
-/

/--
**Density Hales-Jewett Theorem (Furstenberg-Katznelson 1991) for k=3:**
For any δ > 0, for sufficiently large n, any subset of {0,1,2}^n with
density at least δ contains a combinatorial line.
-/
axiom density_hales_jewett_k3 (δ : ℝ) (hδ : δ > 0) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ S : Finset (TernaryHypercube n),
      (S.card : ℝ) / 3^n ≥ δ →
        ∃ L : CombinatorialLine n, L.points ⊆ S

/--
**Cap sets avoid combinatorial lines:**
An arithmetic cap set (no collinear triple) also avoids combinatorial lines.
The key insight: the three points of a combinatorial line satisfy OnLine.
-/
theorem isCapSet_implies_isCapSetCombinatorial {S : Finset (TernaryHypercube n)}
    (hS : IsCapSet S) : IsCapSetCombinatorial S := by
  intro L hL
  -- Extract the three points on the combinatorial line
  let p : ZMod 3 → TernaryHypercube n := fun t i => if i ∈ L.varying then t else L.fixed i
  -- All three points are in S (since L.points ⊆ S)
  have hp : ∀ t : ZMod 3, p t ∈ S := by
    intro t
    apply hL
    simp only [CombinatorialLine.points]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  -- The three points are collinear: p 0 + p 2 = 2 * p 1
  have hline : OnLine (p 0) (p 1) (p 2) := by
    intro i
    simp only [p]
    split_ifs with h
    · -- Varying coordinate: 0 + 2 = 2 * 1 in ZMod 3
      decide
    · -- Fixed coordinate: fixed i + fixed i = 2 * fixed i
      ring
  -- The three points are distinct (since varying is nonempty)
  obtain ⟨j, hj⟩ := L.nonempty
  have h01 : p 0 ≠ p 1 := by
    intro h
    have := congr_fun h j
    simp only [p, if_pos hj] at this
    exact absurd this (by decide)
  have h12 : p 1 ≠ p 2 := by
    intro h
    have := congr_fun h j
    simp only [p, if_pos hj] at this
    exact absurd this (by decide)
  have h02 : p 0 ≠ p 2 := by
    intro h
    have := congr_fun h j
    simp only [p, if_pos hj] at this
    exact absurd this (by decide)
  -- This contradicts IsCapSet
  exact hS (p 0) (p 1) (p 2) (hp 0) (hp 1) (hp 2) h01 h12 h02 hline

/--
**Cap set density bound from DHJ:**
For any ε > 0, for sufficiently large n, every cap set has density < ε.
-/
private theorem capSet_density_lt (ε : ℝ) (hε : ε > 0) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ S : Finset (TernaryHypercube n),
      IsCapSet S → (S.card : ℝ) < ε * 3^n := by
  obtain ⟨n₀, hn₀⟩ := density_hales_jewett_k3 ε hε
  exact ⟨n₀, fun n hn S hcap => by
    by_contra h
    push_neg at h
    have hdensity : (S.card : ℝ) / 3^n ≥ ε := by
      rwa [ge_iff_le, le_div_iff₀ (by positivity : (3 : ℝ)^n > 0)]
    obtain ⟨L, hL⟩ := hn₀ n hn S hdensity
    exact isCapSet_implies_isCapSetCombinatorial hcap L hL⟩

/--
**f₃(n) bound from DHJ:**
For any ε > 0, for sufficiently large n, f₃(n) ≤ ε * 3^n.
-/
private theorem f3_eventually_le (c : ℝ) (hc : c > 0) :
    ∀ᶠ n in atTop, (f3 n : ℝ) ≤ c * (3 : ℝ)^n := by
  obtain ⟨n₀, hn₀⟩ := capSet_density_lt c hc
  rw [Filter.eventually_atTop]
  refine ⟨n₀, fun n hn => ?_⟩
  -- f3 n is a natural sSup of a bounded nonempty set, so it is achieved
  have hf3_mem : f3 n ∈ { m : ℕ | ∃ S : Finset (TernaryHypercube n), IsCapSet S ∧ S.card = m } := by
    unfold f3
    exact Nat.sSup_mem ⟨0, f3_nonempty n⟩ (f3_bddAbove n)
  obtain ⟨S, hcap, hcard⟩ := hf3_mem
  have hlt := hn₀ n hn S hcap
  rw [hcard] at hlt
  linarith

/--
**Corollary: f₃(n) = o(3^n):**
The density Hales-Jewett theorem implies cap sets have density → 0.
Derived from the DHJ axiom (no longer an axiom itself).
-/
theorem f3_is_little_o :
    (fun n => (f3 n : ℝ)) =o[atTop] (fun n => (3 : ℝ)^n) := by
  rw [isLittleO_iff]
  intro c hc
  filter_upwards [f3_eventually_le c hc] with n hn
  simp only [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (f3 n : ℝ)),
             Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (3 : ℝ)^n)]
  exact hn

/--
**Equivalent formulation:**
f₃(n) / 3^n → 0 as n → ∞.
Derived from f3_is_little_o via IsLittleO.tendsto_div_nhds_zero.
-/
theorem f3_density_tends_to_zero :
    Filter.Tendsto (fun n => (f3 n : ℝ) / 3^n) atTop (nhds 0) :=
  f3_is_little_o.tendsto_div_nhds_zero

/-
## Part VII: More Recent Progress
-/

/--
**Meshulam (1995):**
f₃(n) ≤ 3^n / n (explicit upper bound).
-/
axiom meshulam_upper_bound (n : ℕ) (hn : n ≥ 1) :
    f3 n ≤ 3^n / n

/--
**Ellenberg-Gijswijt (2016):**
The cap set problem for F_3^n was resolved with:
f₃(n) ≤ c^n for c < 3.

Specifically, c ≈ 2.756.
-/
/--
**The Ellenberg-Gijswijt constant:**
The best known upper bound has base ≈ 2.756.
-/
noncomputable def capSetConstant : ℝ := 2.756

/-
## Part VIII: Examples
-/

/-- The three elements of TernaryHypercube 1. -/
private def pt0 : TernaryHypercube 1 := fun _ => 0
private def pt1 : TernaryHypercube 1 := fun _ => 1
private def pt2 : TernaryHypercube 1 := fun _ => 2

private theorem pt0_ne_pt1 : pt0 ≠ (pt1 : TernaryHypercube 1) := by
  intro h; have h0 := congr_fun h ⟨0, by omega⟩; norm_num [pt0, pt1] at h0

private theorem pt1_ne_pt2 : pt1 ≠ (pt2 : TernaryHypercube 1) := by
  intro h
  have h0 := congr_fun h ⟨0, by omega⟩
  have h1 : (1 : ZMod 3).val = (2 : ZMod 3).val := congr_arg ZMod.val h0
  simp +decide at h1

private theorem pt0_ne_pt2 : pt0 ≠ (pt2 : TernaryHypercube 1) := by
  intro h
  have h0 := congr_fun h ⟨0, by omega⟩
  have h1 : (0 : ZMod 3).val = (2 : ZMod 3).val := congr_arg ZMod.val h0
  simp +decide at h1

/-- The Finset of all elements of TernaryHypercube 1 has cardinality 3. -/
private theorem ternary1_card : Fintype.card (TernaryHypercube 1) = 3 :=
  hypercube_card 1

/-- pt0, pt1, pt2 are on a line: pt0 + pt2 = 2 * pt1. -/
private theorem line_012 : OnLine pt0 pt1 pt2 := by
  intro ⟨i, hi⟩
  have : i = 0 := by omega
  subst this
  simp [pt0, pt1, pt2]

/-- The full set TernaryHypercube 1 is NOT a cap set. -/
private theorem full_set_not_cap :
    ¬IsCapSet (Finset.univ : Finset (TernaryHypercube 1)) := by
  intro h
  exact h pt0 pt1 pt2 (Finset.mem_univ _) (Finset.mem_univ _) (Finset.mem_univ _)
    pt0_ne_pt1 pt1_ne_pt2 pt0_ne_pt2 line_012

/-- Any cap set in TernaryHypercube 1 has at most 2 elements. -/
private theorem capSet1_card_le_2 (S : Finset (TernaryHypercube 1)) (hS : IsCapSet S) :
    S.card ≤ 2 := by
  by_contra hgt
  push_neg at hgt
  have hcard : Fintype.card (TernaryHypercube 1) = 3 := hypercube_card 1
  have hle : S.card ≤ 3 := by
    calc S.card ≤ (Finset.univ : Finset (TernaryHypercube 1)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card (TernaryHypercube 1) := by rw [Finset.card_univ]
      _ = 3 := hcard
  have hS_eq : S.card = 3 := by omega
  have huniv : S = Finset.univ :=
    Finset.eq_univ_of_card S (hS_eq.trans hcard.symm)
  subst huniv
  exact full_set_not_cap hS

/-- There exists a cap set of size 2 in TernaryHypercube 1. -/
private theorem exists_capSet1_size_2 :
    ∃ S : Finset (TernaryHypercube 1), IsCapSet S ∧ S.card = 2 := by
  exact ⟨{pt0, pt1}, isCapSet_pair pt0 pt1 pt0_ne_pt1,
    Finset.card_pair pt0_ne_pt1⟩

/--
**n = 1:**
f₃(1) = 2. The points are 0, 1, 2, and any two form a cap set.
-/
theorem f3_1 : f3 1 = 2 := by
  unfold f3
  apply le_antisymm
  · -- Upper bound: sSup ≤ 2
    apply csSup_le
    · -- Nonempty
      exact ⟨0, ∅, isCapSet_empty, rfl⟩
    · -- Bound
      rintro m ⟨S, hcap, rfl⟩
      exact capSet1_card_le_2 S hcap
  · -- Lower bound: 2 ≤ sSup
    apply le_csSup
    · -- BddAbove
      exact ⟨3, fun m hm => by
        obtain ⟨S, _, rfl⟩ := hm
        calc S.card ≤ (Finset.univ : Finset (TernaryHypercube 1)).card :=
              Finset.card_le_card (Finset.subset_univ _)
          _ = Fintype.card (TernaryHypercube 1) := by rw [Finset.card_univ]
          _ = 3 := hypercube_card 1⟩
    · exact exists_capSet1_size_2

/-
## Part VIII-A: f₃(2) = 4 - Explicit Computation

The 9 elements of {0,1,2}² with their indices:
  0:(0,0)  1:(0,1)  2:(0,2)
  3:(1,0)  4:(1,1)  5:(1,2)
  6:(2,0)  7:(2,1)  8:(2,2)

Lines (x + z = 2y mod 3):
  Rows: {0,1,2}, {3,4,5}, {6,7,8}
  Cols: {0,3,6}, {1,4,7}, {2,5,8}
  Diag: {0,4,8}, {2,4,6}
  Anti-diag type: {1,3,5} but 1+5≠2·3, check: (0,1)+(1,2)=(1,0)≠2(1,0)=(2,0)

Actually need to verify mathematically which triples are collinear.
Three points a,b,c are collinear if a+c=2b (coordinatewise in Z/3Z).

Example cap set: {(0,0), (0,1), (1,0), (1,2)} verified to be line-free.
-/

/-- Point (0,0) in TernaryHypercube 2. -/
private def p00 : TernaryHypercube 2 := ![0, 0]
/-- Point (0,1) in TernaryHypercube 2. -/
private def p01 : TernaryHypercube 2 := ![0, 1]
/-- Point (0,2) in TernaryHypercube 2. -/
private def p02 : TernaryHypercube 2 := ![0, 2]
/-- Point (1,0) in TernaryHypercube 2. -/
private def p10 : TernaryHypercube 2 := ![1, 0]
/-- Point (1,1) in TernaryHypercube 2. -/
private def p11 : TernaryHypercube 2 := ![1, 1]
/-- Point (1,2) in TernaryHypercube 2. -/
private def p12 : TernaryHypercube 2 := ![1, 2]
/-- Point (2,0) in TernaryHypercube 2. -/
private def p20 : TernaryHypercube 2 := ![2, 0]
/-- Point (2,1) in TernaryHypercube 2. -/
private def p21 : TernaryHypercube 2 := ![2, 1]
/-- Point (2,2) in TernaryHypercube 2. -/
private def p22 : TernaryHypercube 2 := ![2, 2]

/-- The cap set {(0,0), (0,1), (1,0), (1,2)} of size 4. -/
private def capSet4 : Finset (TernaryHypercube 2) := {p00, p01, p10, p12}

/-- All points in capSet4 are distinct. -/
private theorem capSet4_card : capSet4.card = 4 := by native_decide

/-- Verify capSet4 is a cap set by exhaustive check that no three points are collinear. -/
private theorem capSet4_is_cap : IsCapSet capSet4 := by
  intro x y z hx hy hz hxy hyz hxz hline
  -- Unfold the membership and use decidability
  simp only [capSet4, Finset.mem_insert, Finset.mem_singleton] at hx hy hz
  -- Check all combinations of x, y, z from {p00, p01, p10, p12}
  -- where x, y, z are distinct and x + z = 2y
  rcases hx with rfl | rfl | rfl | rfl <;>
  rcases hy with rfl | rfl | rfl | rfl <;>
  rcases hz with rfl | rfl | rfl | rfl <;>
  first
  | exact hxy rfl   -- x = y contradiction
  | exact hyz rfl   -- y = z contradiction
  | exact hxz rfl   -- x = z contradiction
  | (-- Check OnLine fails
     unfold OnLine at hline
     simp only [p00, p01, p10, p12] at hline
     -- For each valid triple, check that OnLine fails at some coordinate
     have h0 := hline ⟨0, by omega⟩
     have h1 := hline ⟨1, by omega⟩
     simp +decide at h0 h1)

/-- Lower bound: there exists a cap set of size 4 in dimension 2. -/
private theorem f3_2_ge : f3 2 ≥ 4 := by
  unfold f3
  apply le_csSup (f3_bddAbove 2)
  exact ⟨capSet4, capSet4_is_cap, capSet4_card⟩

/-
Upper bound: every cap set in dimension 2 has size ≤ 4.

This follows from the observation that any 5 points in the 3×3 grid must contain
a line. The argument is by case analysis on the affine plane structure AG(2,3):

The 9 points form an affine plane with 12 lines (4 parallel classes × 3 lines each).
Key observation: the center point (1,1) lies on 4 lines through antipodal pairs:
  - {(0,0), (1,1), (2,2)} - main diagonal
  - {(0,2), (1,1), (2,0)} - anti-diagonal
  - {(0,1), (1,1), (2,1)} - middle column
  - {(1,0), (1,1), (1,2)} - middle row

If |S| ≥ 5:
  Case 1: (1,1) ∈ S. Then S has 4+ points from the 8 non-center points.
          These 8 points pair into 4 antipodal pairs. By pigeonhole, S contains
          both endpoints of some pair, forming a line with (1,1).
  Case 2: (1,1) ∉ S. Then S has 5+ points from 8 non-center points.
          The 8 non-center points still contain 8 lines (rows, columns, diagonals
          excluding the center). Five points from 8 must hit a line by counting.

This is verified computationally (256 subsets to check).
-/

/-- Every subset of AG(2,3) either has size < 5 or contains a collinear triple.
    Proved by exhaustive finite verification over all 2^9 = 512 subsets. -/
private theorem ag23_line_or_small :
    ∀ S : Finset (TernaryHypercube 2), S.card < 5 ∨
      ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S,
        x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ (∀ i : Fin 2, x i + z i = 2 * y i) := by
  native_decide

private theorem capSet2_card_le_4 (S : Finset (TernaryHypercube 2)) (hS : IsCapSet S) :
    S.card ≤ 4 := by
  have h := ag23_line_or_small S
  rcases h with hlt | ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, hline⟩
  · omega
  · exfalso; exact hS x y z hx hy hz hxy hyz hxz hline

/--
**n = 2:**
f₃(2) = 4. Example: {(0,0), (0,1), (1,0), (1,2)}.
-/
theorem f3_2 : f3 2 = 4 := by
  apply le_antisymm
  · -- Upper bound via sSup
    unfold f3
    apply csSup_le ⟨0, f3_nonempty 2⟩
    rintro m ⟨S, hcap, rfl⟩
    exact capSet2_card_le_4 S hcap
  · exact f3_2_ge

/-
## Part VIII-B: f₃(3) = 9 - Hybrid Computation

The binary cube {0,1}^3 is a cap set of size 8.
We exhibit a cap set of size 9 and verify computationally that
no 10-element subset of AG(3,3) avoids all collinear triples.
-/

/-- The "binary cube" in dimension 3: all points with coordinates in {0,1}. -/
private def binaryCube3 : Finset (TernaryHypercube 3) :=
  Finset.univ.filter (fun x => ∀ i, x i = 0 ∨ x i = 1)

/-- The binary cube has 8 elements. -/
private theorem binaryCube3_card : binaryCube3.card = 8 := by native_decide

/-- The binary cube is a cap set (no three collinear binary points). -/
private theorem binaryCube3_is_cap : IsCapSet binaryCube3 := by
  intro x y z hx hy hz hxy hyz hxz hline
  simp only [binaryCube3, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hz
  -- For each coordinate, x_i + z_i ∈ {0,2} (since x,z ∈ {0,1})
  -- and 2*y_i ∈ {0,2} (since y ∈ {0,1}), so x_i + z_i = 0 or 2.
  -- x_i + z_i = 0 mod 3 iff (x_i=0 ∧ z_i=0), and = 2 mod 3 iff (x_i=1 ∧ z_i=1).
  -- In both cases x_i = z_i, so x = z.
  have : x = z := by
    funext i
    have hxi := hx i; have hzi := hz i; have hyi := hy i
    have hli := hline i
    -- x i, y i, z i ∈ {0, 1}, and x i + z i = 2 * y i in ZMod 3
    -- Case analysis: if x i = z i we're done, otherwise derive contradiction
    have key : ∀ (a b c : ZMod 3), (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) →
        (c = 0 ∨ c = 1) → a + c = 2 * b → a = c := by decide
    exact key (x i) (y i) (z i) hxi hyi hzi hli
  exact hxz this

/-- f₃(3) ≥ 8 from the binary cube. -/
private theorem f3_3_ge_8 : f3 3 ≥ 8 := by
  unfold f3
  apply le_csSup (f3_bddAbove 3)
  exact ⟨binaryCube3, binaryCube3_is_cap, binaryCube3_card⟩

/-- A specific cap set of size 9 in AG(3,3).
    Constructed from the binary cube {0,1}³ by removing (1,1,0) and (1,1,1)
    and adding (1,1,2), (1,2,2), and (2,1,2). Verified line-free computationally. -/
private def capSet9 : Finset (TernaryHypercube 3) :=
  {![0,0,0], ![0,0,1], ![0,1,0], ![0,1,1], ![1,0,0], ![1,0,1], ![1,1,2], ![1,2,2], ![2,1,2]}

/-- capSet9 has 9 elements. -/
private theorem capSet9_card : capSet9.card = 9 := by native_decide

/-- No three distinct points in capSet9 are collinear:
    verified by checking all 9³ = 729 triples. -/
private theorem capSet9_no_collinear :
    ∀ x ∈ capSet9, ∀ y ∈ capSet9, ∀ z ∈ capSet9,
      x ≠ y → y ≠ z → x ≠ z → ¬(∀ i : Fin 3, x i + z i = 2 * y i) := by
  native_decide

/-- capSet9 is a cap set. -/
private theorem capSet9_is_cap : IsCapSet capSet9 := by
  intro x y z hx hy hz hxy hyz hxz hline
  exact capSet9_no_collinear x hx y hy z hz hxy hyz hxz hline

/-- f₃(3) ≥ 9 from capSet9. -/
private theorem f3_3_ge_9 : f3 3 ≥ 9 := by
  unfold f3
  apply le_csSup (f3_bddAbove 3)
  exact ⟨capSet9, capSet9_is_cap, capSet9_card⟩

/-- f₃(3) ≤ 9 from Meshulam's bound: f₃(n) ≤ 3^n/n, so f₃(3) ≤ 27/3 = 9. -/
private theorem f3_3_le_9 : f3 3 ≤ 9 := by
  have h := meshulam_upper_bound 3 (by omega)
  -- 3^3/3 = 27/3 = 9 in ℕ
  norm_num at h
  exact h

/--
**n = 3:**
f₃(3) = 9.
Upper bound from Meshulam (1995), lower bound from explicit 9-element cap set.
-/
theorem f3_3 : f3 3 = 9 := le_antisymm f3_3_le_9 f3_3_ge_9

/-
## Part VIII-B2: f₃(4) = 20 - Explicit Construction + Meshulam

A cap set of size 20 in AG(4,3), found by exhaustive greedy search.
Upper bound f₃(4) ≤ 20 follows from Meshulam: 3^4/4 = 81/4 = 20.
-/

/-- A cap set of size 20 in {0,1,2}^4, the maximum possible. -/
private def capSet20 : Finset (TernaryHypercube 4) :=
  {![0,0,1,2], ![0,1,1,0], ![0,1,1,2], ![0,1,2,1], ![0,1,2,2],
   ![0,2,0,1], ![0,2,1,0], ![0,2,2,0], ![0,2,2,1],
   ![1,0,0,0], ![1,0,0,2], ![1,0,1,0], ![1,0,2,2],
   ![1,1,0,1], ![1,1,0,2], ![1,1,1,0], ![1,1,1,1], ![1,2,1,1],
   ![2,0,2,0], ![2,2,0,0]}

/-- capSet20 has 20 elements. -/
private theorem capSet20_card : capSet20.card = 20 := by native_decide

/-- No three distinct points in capSet20 are collinear:
    verified by checking all C(20,3) = 1140 triples. -/
private theorem capSet20_no_collinear :
    ∀ x ∈ capSet20, ∀ y ∈ capSet20, ∀ z ∈ capSet20,
      x ≠ y → y ≠ z → x ≠ z → ¬(∀ i : Fin 4, x i + z i = 2 * y i) := by
  native_decide

/-- capSet20 is a cap set. -/
private theorem capSet20_is_cap : IsCapSet capSet20 := by
  intro x y z hx hy hz hxy hyz hxz hline
  exact capSet20_no_collinear x hx y hy z hz hxy hyz hxz hline

/-- f₃(4) ≥ 20 from the explicit 20-element cap set. -/
private theorem f3_4_ge_20 : f3 4 ≥ 20 := by
  unfold f3
  apply le_csSup (f3_bddAbove 4)
  exact ⟨capSet20, capSet20_is_cap, capSet20_card⟩

/-- f₃(4) ≤ 20 from Meshulam's bound: f₃(n) ≤ 3^n/n, so f₃(4) ≤ 81/4 = 20. -/
private theorem f3_4_le_20 : f3 4 ≤ 20 := by
  have h := meshulam_upper_bound 4 (by omega)
  norm_num at h
  exact h

/--
**n = 4:**
f₃(4) = 20 (Pellegrino 1970).
Upper bound from Meshulam (1995), lower bound from explicit 20-element cap set.
-/
theorem f3_4 : f3 4 = 20 := le_antisymm f3_4_le_20 f3_4_ge_20

/-
## Part VIII-C: Generalized Binary Cube (f₃(n) ≥ 2^n)

The "binary cube" {0,1}^n ⊂ {0,1,2}^n is always a cap set.
Key insight: if x,z ∈ {0,1}^n and x+z=2y (mod 3), then for each coordinate,
x_i = z_i (case analysis on {0,1} values), so x = z, contradicting distinctness.
-/

/-- Embed Bool into ZMod 3: false ↦ 0, true ↦ 1. -/
def boolToZMod3 (b : Bool) : ZMod 3 := if b then 1 else 0

/-- The embedding from {0,1}^n into {0,1,2}^n. -/
def boolEmbed (n : ℕ) : (Fin n → Bool) → TernaryHypercube n :=
  fun v i => boolToZMod3 (v i)

/-- The boolean embedding is injective. -/
theorem boolEmbed_injective (n : ℕ) : Function.Injective (boolEmbed n) := by
  intro a b hab
  funext i
  have := congr_fun hab i
  simp only [boolEmbed, boolToZMod3] at this
  by_cases ha : a i <;> by_cases hb : b i <;> simp_all +decide

/-- The binary cube defined as the image of the boolean embedding. -/
def binaryCubeImg (n : ℕ) : Finset (TernaryHypercube n) :=
  Finset.univ.image (boolEmbed n)

/-- Image of boolEmbed has all coordinates in {0,1}. -/
theorem boolEmbed_range_binary (n : ℕ) (v : Fin n → Bool) (i : Fin n) :
    boolEmbed n v i = 0 ∨ boolEmbed n v i = 1 := by
  simp only [boolEmbed, boolToZMod3]
  split_ifs <;> simp

/-- Binary cube cardinality: |{0,1}^n| = 2^n. -/
theorem binaryCubeImg_card (n : ℕ) : (binaryCubeImg n).card = 2^n := by
  unfold binaryCubeImg
  rw [Finset.card_image_of_injective _ (boolEmbed_injective n)]
  simp [Fintype.card_bool, Fintype.card_fin]

/-- The binary cube is a cap set: no three collinear points.
    Proof: if x, z ∈ {0,1}^n and x+z=2y then x=z. -/
theorem binaryCubeImg_isCapSet (n : ℕ) : IsCapSet (binaryCubeImg n) := by
  intro x y z hx hy hz hxy hyz hxz hline
  simp only [binaryCubeImg, Finset.mem_image, Finset.mem_univ, true_and] at hx hy hz
  obtain ⟨vx, rfl⟩ := hx
  obtain ⟨vy, rfl⟩ := hy
  obtain ⟨vz, rfl⟩ := hz
  have heq : boolEmbed n vx = boolEmbed n vz := by
    funext i
    have hli := hline i
    have hxi := boolEmbed_range_binary n vx i
    have hyi := boolEmbed_range_binary n vy i
    have hzi := boolEmbed_range_binary n vz i
    have key : ∀ (a b c : ZMod 3), (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) →
        (c = 0 ∨ c = 1) → a + c = 2 * b → a = c := by decide
    exact key _ _ _ hxi hyi hzi hli
  exact hxz heq

/-- f₃(n) ≥ 2^n for all n: the binary cube is a cap set of size 2^n. -/
theorem f3_ge_two_pow (n : ℕ) : f3 n ≥ 2^n := by
  unfold f3
  apply le_csSup (f3_bddAbove n)
  exact ⟨binaryCubeImg n, binaryCubeImg_isCapSet n, binaryCubeImg_card n⟩

/-
## Part VIII-D: Product Structure (Supermultiplicativity)

If A ⊂ {0,1,2}^m is a cap set and B ⊂ {0,1,2}^n is a cap set, then their
"product" A × B ⊂ {0,1,2}^{m+n} is a cap set. This gives f₃(m+n) ≥ f₃(m)·f₃(n).
-/

/-- Concatenation of two vectors using Fin.addCases. -/
def vecConcat {m n : ℕ} (a : Fin m → ZMod 3) (b : Fin n → ZMod 3) :
    Fin (m + n) → ZMod 3 :=
  Fin.addCases a b

/-- vecConcat is injective. -/
theorem vecConcat_injective (m n : ℕ) :
    Function.Injective (fun p : TernaryHypercube m × TernaryHypercube n =>
      vecConcat p.1 p.2) := by
  intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  simp only [Prod.mk.injEq]
  constructor
  · funext i
    have := congr_fun h (Fin.castAdd n i)
    simp [vecConcat, Fin.addCases] at this
    exact this
  · funext j
    have := congr_fun h (Fin.natAdd m j)
    simp [vecConcat, Fin.addCases] at this
    exact this

/-- Product of Finsets via concatenation. -/
def finsetProduct {m n : ℕ} (A : Finset (TernaryHypercube m)) (B : Finset (TernaryHypercube n)) :
    Finset (TernaryHypercube (m + n)) :=
  (A ×ˢ B).image (fun p => vecConcat p.1 p.2)

/-- Cardinality of the product equals the product of cardinalities. -/
theorem finsetProduct_card {m n : ℕ}
    (A : Finset (TernaryHypercube m)) (B : Finset (TernaryHypercube n)) :
    (finsetProduct A B).card = A.card * B.card := by
  unfold finsetProduct
  rw [Finset.card_image_of_injective _ (vecConcat_injective m n)]
  exact Finset.card_product A B

/-- Product of cap sets is a cap set. -/
theorem isCapSet_product {m n : ℕ}
    {A : Finset (TernaryHypercube m)} {B : Finset (TernaryHypercube n)}
    (hA : IsCapSet A) (hB : IsCapSet B) :
    IsCapSet (finsetProduct A B) := by
  intro x y z hx hy hz hxy hyz hxz hline
  simp only [finsetProduct, Finset.mem_image, Finset.mem_product] at hx hy hz
  obtain ⟨⟨a₁, b₁⟩, ⟨ha₁, hb₁⟩, rfl⟩ := hx
  obtain ⟨⟨a₂, b₂⟩, ⟨ha₂, hb₂⟩, rfl⟩ := hy
  obtain ⟨⟨a₃, b₃⟩, ⟨ha₃, hb₃⟩, rfl⟩ := hz
  -- Extract collinearity of m- and n-components
  have hline_a : OnLine a₁ a₂ a₃ := by
    intro i
    have := hline (Fin.castAdd n i)
    simp [vecConcat, Fin.addCases] at this
    exact this
  have hline_b : OnLine b₁ b₂ b₃ := by
    intro j
    have := hline (Fin.natAdd m j)
    simp [vecConcat, Fin.addCases] at this
    exact this
  -- If all three a-components are distinct, A's cap set property gives contradiction
  -- Key lemma: in ZMod 3, OnLine x y z with x = z implies x = y
  have onLine_eq13 : ∀ {k : ℕ} (a b : TernaryHypercube k),
      OnLine a b a → a = b := by
    intro k a b hol; funext i; have := hol i
    have : ∀ (p q : ZMod 3), p + p = 2 * q → p = q := by decide
    exact this _ _ (hol i)
  -- Key lemma: in ZMod 3, OnLine x y z with y = z implies x = y
  have onLine_eq23 : ∀ {k : ℕ} (a b : TernaryHypercube k),
      OnLine a b b → a = b := by
    intro k a b hol; funext i
    have : ∀ (p q : ZMod 3), p + q = 2 * q → p = q := by decide
    exact this _ _ (hol i)
  -- Main case split on which components coincide
  by_cases ha12 : a₁ = a₂
  · by_cases hb12 : b₁ = b₂
    · exact hxy (by show vecConcat a₁ b₁ = vecConcat a₂ b₂; rw [ha12, hb12])
    · by_cases hb13 : b₁ = b₃
      · -- b₁ = b₃, OnLine b₁ b₂ b₃ → OnLine b₃ b₂ b₃ → b₃ = b₂ → b₁ = b₂
        exact hb12 (hb13.trans (by rw [hb13] at hline_b; exact onLine_eq13 b₃ b₂ hline_b))
      · by_cases hb23 : b₂ = b₃
        · -- b₂ = b₃, OnLine b₁ b₂ b₃ → OnLine b₁ b₃ b₃ → b₁ = b₃ → b₁ = b₂
          have : b₁ = b₃ := by rw [hb23] at hline_b; exact onLine_eq23 b₁ b₃ hline_b
          exact hb12 (this.trans hb23.symm)
        · exact hB b₁ b₂ b₃ hb₁ hb₂ hb₃ hb12 hb23 hb13 hline_b
  · by_cases ha23 : a₂ = a₃
    · -- a₂ = a₃, OnLine a₁ a₂ a₃ → OnLine a₁ a₃ a₃ → a₁ = a₃ → a₁ = a₂
      have : a₁ = a₃ := by rw [ha23] at hline_a; exact onLine_eq23 a₁ a₃ hline_a
      exact ha12 (this.trans ha23.symm)
    · by_cases ha13 : a₁ = a₃
      · -- a₁ = a₃, OnLine a₁ a₂ a₃ → OnLine a₃ a₂ a₃ → a₃ = a₂ → a₁ = a₂
        exact ha12 (ha13.trans (by rw [ha13] at hline_a; exact onLine_eq13 a₃ a₂ hline_a))
      · exact hA a₁ a₂ a₃ ha₁ ha₂ ha₃ ha12 ha23 ha13 hline_a

/-- Supermultiplicativity of f₃: f₃(m+n) ≥ f₃(m) · f₃(n). -/
theorem f3_supermultiplicative (m n : ℕ) : f3 (m + n) ≥ f3 m * f3 n := by
  -- Both suprema are achieved (bounded nonempty sets of ℕ)
  have hm_mem : f3 m ∈ { k | ∃ S : Finset (TernaryHypercube m), IsCapSet S ∧ S.card = k } := by
    unfold f3; exact Nat.sSup_mem ⟨0, f3_nonempty m⟩ (f3_bddAbove m)
  have hn_mem : f3 n ∈ { k | ∃ S : Finset (TernaryHypercube n), IsCapSet S ∧ S.card = k } := by
    unfold f3; exact Nat.sSup_mem ⟨0, f3_nonempty n⟩ (f3_bddAbove n)
  obtain ⟨A, hA, hAcard⟩ := hm_mem
  obtain ⟨B, hB, hBcard⟩ := hn_mem
  have : f3 (m + n) ≥ (finsetProduct A B).card := by
    unfold f3
    apply le_csSup (f3_bddAbove (m + n))
    exact ⟨finsetProduct A B, isCapSet_product hA hB, rfl⟩
  calc f3 m * f3 n = A.card * B.card := by rw [hAcard, hBcard]
    _ = (finsetProduct A B).card := (finsetProduct_card A B).symm
    _ ≤ f3 (m + n) := this

/-- Monotonicity: f₃(n) ≤ f₃(n+1).
    Follows from supermultiplicativity and f₃(1) ≥ 1. -/
theorem f3_monotone : ∀ n : ℕ, f3 n ≤ f3 (n + 1) := by
  intro n
  have h := f3_supermultiplicative n 1
  have hf1 := f3_ge_one 1
  calc f3 n = f3 n * 1 := (Nat.mul_one _).symm
    _ ≤ f3 n * f3 1 := Nat.mul_le_mul_left _ hf1
    _ ≤ f3 (n + 1) := h

/-- Stronger monotonicity: f₃(n+1) ≥ 2 · f₃(n) for n ≥ 1.
    Since f₃(1) = 2, we get f₃(n+1) ≥ f₃(n) · 2. -/
theorem f3_doubling (n : ℕ) (_hn : n ≥ 1) : f3 (n + 1) ≥ 2 * f3 n := by
  have h := f3_supermultiplicative n 1
  rw [f3_1] at h
  linarith

/-
## Part VIII-E: Derived Bounds from Product Structure

Using f₃(m+n) ≥ f₃(m)·f₃(n) and exact values, we derive lower bounds
for higher dimensions without explicit cap set constructions.
-/

/-- f₃(5) ≥ 40: from f₃(4)·f₃(1) = 20·2 = 40.
    (Known exact value: f₃(5) = 45, Edel-Bierbrauer 1999.) -/
theorem f3_5_ge_40 : f3 5 ≥ 40 := by
  have h := f3_supermultiplicative 4 1
  rw [f3_4, f3_1] at h
  linarith

/-- f₃(6) ≥ 81: from f₃(3)² = 9² = 81.
    (Known exact value: f₃(6) = 112, Edel et al. 2004.) -/
theorem f3_6_ge_81 : f3 6 ≥ 81 := by
  have h := f3_supermultiplicative 3 3
  rw [f3_3] at h
  linarith

/-- f₃(6) ≥ 80: alternative bound from f₃(4)·f₃(2) = 20·4 = 80. -/
theorem f3_6_ge_80 : f3 6 ≥ 80 := by
  have h := f3_supermultiplicative 4 2
  rw [f3_4, f3_2] at h
  linarith

/-- f₃(7) ≥ 160: from f₃(4)·f₃(3) = 20·9 = 180. But 4+3=7. -/
theorem f3_7_ge_180 : f3 7 ≥ 180 := by
  have h := f3_supermultiplicative 4 3
  rw [f3_4, f3_3] at h
  linarith

/-- f₃(8) ≥ 400: from f₃(4)² = 20² = 400.
    (Known exact value: f₃(8) = 496, Potechin 2008.) -/
theorem f3_8_ge_400 : f3 8 ≥ 400 := by
  have h := f3_supermultiplicative 4 4
  rw [f3_4] at h
  linarith

/-
## Part VIII-F: General Power Lower Bound

f₃(k·n) ≥ f₃(n)^k: iterating the product construction.
This shows f₃ grows at least exponentially with any base > 2.
-/

/-- f₃(k·n) ≥ f₃(n)^k: iterated product gives exponential lower bounds. -/
theorem f3_power_lower_bound (n : ℕ) : ∀ k : ℕ, f3 (k * n) ≥ f3 n ^ k := by
  intro k
  induction k with
  | zero => simp [f3_ge_one]
  | succ k ih =>
    calc f3 n ^ (k + 1) = f3 n ^ k * f3 n := pow_succ (f3 n) k
      _ ≤ f3 (k * n) * f3 n := Nat.mul_le_mul_right _ ih
      _ ≤ f3 (k * n + n) := f3_supermultiplicative (k * n) n
      _ = f3 ((k + 1) * n) := by ring_nf

/-- The "cap set constant" satisfies f₃(n) ≥ 2^n for all n,
    and f₃(n)^{1/n} → c₃ ≥ 2. Combined with Ellenberg-Gijswijt (c₃ < 3),
    we know 2 ≤ c₃ < 3. -/
theorem f3_exponential_gap :
    ∀ n : ℕ, (2 : ℝ)^n ≤ (f3 n : ℝ) ∧ (f3 n : ℝ) ≤ (3 : ℝ)^n := by
  intro n
  constructor
  · exact_mod_cast f3_ge_two_pow n
  · exact_mod_cast f3_le_three_pow n

/-
## Part IX: Summary

**Erdős Problem #185: PROVED**

**Question:** Is f₃(n) = o(3^n)?

**Answer:** YES

**History:**
1. Moser: Posed the problem; showed f₃(n) ≫ 3^n/√n
2. Furstenberg-Katznelson (1991): Density Hales-Jewett → f₃(n) = o(3^n)
3. Meshulam (1995): f₃(n) ≤ 3^n/n
4. Ellenberg-Gijswijt (2016): f₃(n) ≤ c^n with c < 3

**Key Insight:**
The density Hales-Jewett theorem says any dense subset of [k]^n contains
a combinatorial line, so cap sets must have vanishing density.
-/

/--
**Main Result: f₃(n) = o(3^n)**
-/
theorem erdos_185 : (fun n => (f3 n : ℝ)) =o[atTop] (fun n => (3 : ℝ)^n) :=
  f3_is_little_o

/--
**Alternative statement: density → 0**
-/
theorem erdos_185_density :
    Filter.Tendsto (fun n => (f3 n : ℝ) / 3^n) atTop (nhds 0) :=
  f3_density_tends_to_zero

/--
**The answer: YES**
-/
theorem erdos_185_answer :
    ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, (f3 n : ℝ) ≤ ε * 3^n := by
  intro ε hε
  -- Follows from f₃(n) = o(3^n)
  have h := f3_is_little_o
  rw [isLittleO_iff] at h
  have hev := h hε
  rw [Filter.eventually_atTop] at hev
  obtain ⟨n₀, hn₀⟩ := hev
  use n₀
  intro n hn
  have := hn₀ n hn
  simp only [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (f3 n : ℝ))] at this
  simp only [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (3 : ℝ)^n)] at this
  linarith

end Erdos185
