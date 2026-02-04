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
axiom f3_geq_R3 (n : ℕ) : f3 n ≥ R3 (3^n)

/-
## Part V: Known Bounds
-/

/--
**Moser's Lower Bound:**
f₃(n) ≫ 3^n/√n.

More precisely, f₃(n) ≥ c · 3^n/√n for some constant c > 0.
-/
axiom moser_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f3 n : ℝ) ≥ c * 3^n / Real.sqrt n

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
**Corollary: f₃(n) = o(3^n):**
The density Hales-Jewett theorem implies cap sets have density → 0.
-/
axiom f3_is_little_o :
    (fun n => (f3 n : ℝ)) =o[atTop] (fun n => (3 : ℝ)^n)

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
axiom ellenberg_gijswijt_2016 :
    ∃ c : ℝ, c < 3 ∧ c > 2.7 ∧ ∀ n : ℕ, (f3 n : ℝ) ≤ c^n

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

/--
**n = 2:**
f₃(2) = 4. Example: {(0,0), (0,1), (1,0), (1,2)}.
-/
axiom f3_2 : f3 2 = 4

/--
**n = 3:**
f₃(3) = 9.
-/
axiom f3_3 : f3 3 = 9

/--
**n = 4:**
f₃(4) = 20.
-/
axiom f3_4 : f3 4 = 20

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
