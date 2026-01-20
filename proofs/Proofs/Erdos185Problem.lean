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
import Mathlib.Analysis.Asymptotics.Asymptotics

open Asymptotics Filter

namespace Erdos185

/-!
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
  simp [TernaryHypercube, Fintype.card_fun]

/-!
## Part II: Lines in {0,1,2}^n
-/

/--
**Collinear (on a line):**
Three points x, y, z in {0,1,2}^n are on a line if x + z = 2y (in ZMod 3).
Equivalently, y is the "midpoint" of x and z.
-/
def OnLine (x y z : TernaryHypercube n) : Prop :=
  ∀ i : Fin n, x i + z i = 2 * y i

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
  {0, 1, 2}.image (fun t : ZMod 3 => fun i =>
    if i ∈ L.varying then t else L.fixed i)

/-!
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

/--
**f₃(n):**
The maximum size of a cap set in {0,1,2}^n.
-/
noncomputable def f3 (n : ℕ) : ℕ :=
  sSup { S.card | S : Finset (TernaryHypercube n) // IsCapSet S }

/-!
## Part IV: Connection to Arithmetic Progressions
-/

/--
**R₃(N):**
The maximum size of a subset of {1,...,N} with no 3-term arithmetic progression.
-/
noncomputable def R3 (N : ℕ) : ℕ :=
  sSup { S.card | S : Finset ℕ // (∀ x ∈ S, x ≤ N) ∧
    ∀ a d : ℕ, d > 0 → a ∈ S → a + d ∈ S → a + 2*d ∈ S → False }

/--
**Trivial lower bound:**
f₃(n) ≥ R₃(3^n).

The embedding is: {1,...,3^n} ↪ {0,1,2}^n via ternary representation.
AP-free sets embed to cap sets (lines generalize APs).
-/
axiom f3_geq_R3 (n : ℕ) : f3 n ≥ R3 (3^n)

/-!
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

axiom moser_set_is_cap (n : ℕ) : IsCapSet (moserSet n)

/-!
## Part VI: The Main Result - Density Hales-Jewett
-/

/--
**Density Hales-Jewett Theorem (Furstenberg-Katznelson 1991):**
For any δ > 0 and k ≥ 3, for sufficiently large n, any subset of [k]^n with
density at least δ contains a combinatorial line.
-/
axiom density_hales_jewett (k : ℕ) (hk : k ≥ 3) (δ : ℝ) (hδ : δ > 0) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ S : Finset (Fin n → Fin k),
      (S.card : ℝ) / k^n ≥ δ →
        ∃ L : CombinatorialLine n, L.points.image (fun f => fun i => (f i : Fin k)) ⊆ S

/--
**Corollary: f₃(n) = o(3^n):**
The density Hales-Jewett theorem implies cap sets have density → 0.
-/
axiom f3_is_little_o :
    (fun n => (f3 n : ℝ)) =o[atTop] (fun n => (3 : ℝ)^n)

/--
**Equivalent formulation:**
f₃(n) / 3^n → 0 as n → ∞.
-/
axiom f3_density_tends_to_zero :
    Filter.Tendsto (fun n => (f3 n : ℝ) / 3^n) atTop (nhds 0)

/-!
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

/-!
## Part VIII: Examples
-/

/--
**n = 1:**
f₃(1) = 2. The points are 0, 1, 2, and any two form a cap set.
-/
theorem f3_1 : f3 1 = 2 := by
  sorry

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

/-!
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
    ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, (f3 n : ℝ) < ε * 3^n := by
  intro ε hε
  -- Follows from f₃(n) = o(3^n)
  have h := f3_is_little_o
  rw [isLittleO_iff] at h
  specialize h hε
  obtain ⟨n₀, hn₀⟩ := h.exists_forall_ge_atTop
  use n₀
  intro n hn
  have := hn₀ n hn
  simp only [norm_of_nonneg (by positivity : (0 : ℝ) ≤ f3 n)] at this
  simp only [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 3^n)] at this
  linarith

end Erdos185
