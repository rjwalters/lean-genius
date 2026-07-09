/-
Erdős Problem #1090: Monochromatic Collinear Points

Source: https://erdosproblems.com/1090
Status: SOLVED (affirmative)

Statement:
Let k ≥ 3. Does there exist a finite set A ⊂ ℝ² such that, in any 2-coloring
of A, there exists a line which contains at least k points from A, and all
the points of A on the line have the same color?

Answer: YES for all k ≥ 3.

Known Results:
- k = 3: Graham and Selfridge (cited by Erdős 1975)
- General k: Hunter observed that a generic projection of [k]ⁿ into ℝ²
  has this property, using the Hales-Jewett theorem.

This is a Ramsey-type problem in Euclidean geometry.

References:
- Erdős [Er75f]: "On some problems of elementary and combinatorial geometry" (1975)
- Graham and Selfridge: k = 3 case
- Hales-Jewett theorem for the general case
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Radon
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic

open Set Finset

namespace Erdos1090

/-
## Part I: Basic Definitions
-/

/--
**Point in the Plane:**
A point in ℝ².
-/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/--
**2-Coloring of a Set:**
A function assigning one of two colors to each point.
-/
def TwoColoring (A : Set Point) := A → Bool

/--
**Collinear Points:**
Three or more points lie on a common line.
-/
def Collinear (p q r : Point) : Prop :=
  ∃ t : ℝ, r - p = t • (q - p)

/--
**Points on a Line:**
Given two points p, q defining a line, the set of all points on that line.
-/
def PointsOnLine (p q : Point) (hp : p ≠ q) : Set Point :=
  {r : Point | ∃ t : ℝ, r = p + t • (q - p)}

/--
**Line through Points:**
A line in ℝ² defined by direction and a point.
-/
structure Line where
  point : Point
  direction : Point
  nonzero : direction ≠ 0

/--
**Point on Line Predicate:**
-/
def OnLine (l : Line) (p : Point) : Prop :=
  ∃ t : ℝ, p = l.point + t • l.direction

/-
## Part II: Monochromatic Lines
-/

/--
**Monochromatic Set:**
All points in a subset have the same color.
-/
def IsMonochromatic (S : Set Point) (c : TwoColoring S) : Prop :=
  ∀ p q : S, c p = c q

/--
**k-Collinear Subset:**
A subset of at least k points that all lie on a common line.
-/
def IsKCollinear (S : Finset Point) (k : ℕ) : Prop :=
  S.card ≥ k ∧ ∃ l : Line, ∀ p ∈ S, OnLine l p

/--
**Monochromatic k-Collinear:**
A subset of at least k collinear points, all the same color.
-/
def MonochromaticKCollinear (A : Finset Point) (k : ℕ)
    (c : Point → Bool) : Prop :=
  ∃ S : Finset Point, S ⊆ A ∧ IsKCollinear S k ∧
    ∀ p q : Point, p ∈ S → q ∈ S → c p = c q

/-
## Part III: The Main Property
-/

/--
**Has Ramsey Property for k:**
A finite set A has the Ramsey property for k if every 2-coloring
contains a monochromatic set of k collinear points.
-/
def HasRamseyProperty (A : Finset Point) (k : ℕ) : Prop :=
  ∀ c : Point → Bool, MonochromaticKCollinear A k c

/--
**Erdős #1090 Question:**
For k ≥ 3, does there exist a finite set with the Ramsey property for k?
-/
def Erdos1090Question (k : ℕ) : Prop :=
  k ≥ 3 → ∃ A : Finset Point, HasRamseyProperty A k

/-
## Part III½: Construction via Hales–Jewett (axiom elimination)

The two results that follow (`graham_selfridge` for `k = 3`, and Hunter's
`hunter_observation` for general `k`) were originally *axiomatized*.  They are
now derived as honest theorems from Mathlib's Hales–Jewett theorem
(`Combinatorics.Line.exists_mono_in_high_dimension`) via the following explicit
"generic projection" of the combinatorial cube `[k]^ι` into ℝ²:

* Hales–Jewett supplies a finite index type `ι` such that every 2-coloring of
  `ι → Fin k` contains a monochromatic combinatorial line.
* We embed `ι → Fin k` linearly into ℝ² by `φ p = ∑ j, (p j : ℝ) • v j`, where
  `v j = !₂[1, w j]` has first coordinate `1`.  A combinatorial line through the
  varying-coordinate set `V` maps to the affine line
  `t ↦ φ(l 0) + t • dir`, with direction `dir = ∑_{j ∈ V} v j`.
* The first coordinate of `dir` equals `|V| ≥ 1 > 0`, so `dir ≠ 0`: the image
  points are genuinely collinear and pairwise distinct, giving `k` collinear
  points of a single color.

This eliminates both axioms; the file is `sorry`-free and axiom-free.
-/

/-- **Erdős #1090 — explicit construction.** For every `k ≥ 3` there is a finite
set `A ⊂ ℝ²` with the Ramsey property: any 2-coloring of `A` contains `k`
monochromatic collinear points.  Proved from the Hales–Jewett theorem by a
generic linear projection of the combinatorial cube `[k]^ι` into the plane. -/
theorem erdos1090_construction (k : ℕ) (hk : k ≥ 3) :
    ∃ A : Finset Point, HasRamseyProperty A k := by
  classical
  haveI : NeZero k := ⟨by omega⟩
  -- Hales–Jewett: a finite index type `ι` controlling every 2-coloring of `[k]^ι`.
  obtain ⟨ι, ιfin, hHJ⟩ :=
    Combinatorics.Line.exists_mono_in_high_dimension (Fin k) Bool
  haveI : Fintype ι := ιfin
  -- Real embedding of coordinate values, and the per-coordinate image vectors.
  set emb : Fin k → ℝ := fun a => (a.val : ℝ) with hemb
  set w : ι → ℝ := fun j => ((Fintype.equivFin ι j).val : ℝ) with hw
  set v : ι → Point := fun j => !₂[1, w j] with hv
  -- Linear "generic projection" `φ : [k]^ι → ℝ²`.
  set φ : (ι → Fin k) → Point := fun p => ∑ j, emb (p j) • v j with hφ
  refine ⟨Finset.image φ Finset.univ, ?_⟩
  intro c
  -- Pull the geometric coloring back to a coloring of the combinatorial cube.
  obtain ⟨l, col, hcol⟩ := hHJ (fun p => c (φ p))
  have hcol' : ∀ a : Fin k, c (φ (l a)) = col := fun a => hcol a
  -- Direction of the image line.
  set dir : Point := ∑ j, (if l.idxFun j = none then (1 : ℝ) else 0) • v j with hdir
  -- Per-coordinate affine identity for points of the combinatorial line.
  have key : ∀ (a : Fin k) (j : ι),
      emb (l a j) = emb (l 0 j) + emb a * (if l.idxFun j = none then (1 : ℝ) else 0) := by
    intro a j
    by_cases h : l.idxFun j = none
    · rw [l.apply_none a j h, l.apply_none 0 j h, if_pos h]
      simp [hemb]
    · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h
      simp only [l.apply_some hb, if_neg h]
      simp [hemb]
  -- Image-line affine identity at the level of ℝ²-vectors.
  have hline : ∀ a : Fin k, φ (l a) = φ (l 0) + emb a • dir := by
    intro a
    simp only [hφ, hdir, Finset.smul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [key a j, add_smul, mul_smul]
  -- The direction vector is nonzero: its first coordinate is `|varying| ≥ 1`.
  have hofLp : (WithLp.ofLp dir) (0 : Fin 2)
      = ∑ j, (if l.idxFun j = none then (1 : ℝ) else 0) := by
    simp only [hdir, hv, WithLp.ofLp_sum, WithLp.ofLp_smul,
      Finset.sum_apply, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul, mul_one]
  have hdir_ne : dir ≠ 0 := by
    intro h0
    have hpos : (0 : ℝ) < (WithLp.ofLp dir) (0 : Fin 2) := by
      rw [hofLp]
      obtain ⟨j0, hj0⟩ := l.proper
      calc (0 : ℝ) < 1 := one_pos
        _ = (if l.idxFun j0 = none then (1 : ℝ) else 0) := (if_pos hj0).symm
        _ ≤ ∑ j, (if l.idxFun j = none then (1 : ℝ) else 0) :=
            Finset.single_le_sum
              (f := fun j => if l.idxFun j = none then (1 : ℝ) else 0)
              (fun j _ => by
                show (0 : ℝ) ≤ if l.idxFun j = none then (1 : ℝ) else 0
                split_ifs <;> norm_num)
              (Finset.mem_univ j0)
    rw [h0] at hpos
    simp at hpos
  -- Assemble the monochromatic `k`-collinear subset.
  refine ⟨Finset.image (fun a : Fin k => φ (l a)) Finset.univ, ?_, ?_, ?_⟩
  · -- `S ⊆ A`
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨a, ha⟩ := hx
    exact ⟨l a, ha⟩
  · -- `IsKCollinear S k`
    refine ⟨?_, ?_⟩
    · -- `S.card ≥ k`
      have hinj : Function.Injective (fun a : Fin k => φ (l a)) := by
        intro a a' haa'
        simp only at haa'
        rw [hline a, hline a'] at haa'
        have hsm : emb a • dir = emb a' • dir := add_left_cancel haa'
        have hee : emb a = emb a' := by
          by_contra hne
          have h2 : (emb a - emb a') • dir = 0 := by rw [sub_smul, hsm, sub_self]
          rcases smul_eq_zero.mp h2 with h | h
          · exact hne (sub_eq_zero.mp h)
          · exact hdir_ne h
        have : a.val = a'.val := by
          have := hee; simp only [hemb] at this; exact Nat.cast_injective this
        exact Fin.ext this
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    · -- All points lie on a common geometric line.
      refine ⟨⟨φ (l 0), dir, hdir_ne⟩, ?_⟩
      intro p hp
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
      obtain ⟨a, ha⟩ := hp
      exact ⟨emb a, by rw [← ha, hline a]⟩
  · -- Monochromatic.
    intro p q hp hq
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp hq
    obtain ⟨a, ha⟩ := hp
    obtain ⟨a', ha'⟩ := hq
    rw [← ha, ← ha', hcol' a, hcol' a']

/-- **Erdős #1090 — general finite alphabet.**  The same generic-projection argument
works verbatim for *any* finite color type `C`, not just `Bool`: for every `k ≥ 3` there
is a finite `A ⊂ ℝ²` such that every coloring `c : Point → C` admits `k` monochromatic
collinear points.  The only ingredient that referenced the number of colors was the
Hales–Jewett input `exists_mono_in_high_dimension (Fin k) C`, which holds for any
`[Finite C]`.  Specialising `C := Bool` recovers `erdos1090_construction`; `C := Fin r`
gives the `r`-coloring generalisation `erdos1090_generalized_affirmative`. -/
theorem ramsey_construction_general (C : Type*) [Finite C] (k : ℕ) (hk : k ≥ 3) :
    ∃ A : Finset Point, ∀ c : Point → C,
      ∃ S : Finset Point, S ⊆ A ∧ IsKCollinear S k ∧
        ∀ p q : Point, p ∈ S → q ∈ S → c p = c q := by
  classical
  haveI : NeZero k := ⟨by omega⟩
  -- Hales–Jewett: a finite index type `ι` controlling every `C`-coloring of `[k]^ι`.
  obtain ⟨ι, ιfin, hHJ⟩ :=
    Combinatorics.Line.exists_mono_in_high_dimension (Fin k) C
  haveI : Fintype ι := ιfin
  set emb : Fin k → ℝ := fun a => (a.val : ℝ) with hemb
  set w : ι → ℝ := fun j => ((Fintype.equivFin ι j).val : ℝ) with hw
  set v : ι → Point := fun j => !₂[1, w j] with hv
  set φ : (ι → Fin k) → Point := fun p => ∑ j, emb (p j) • v j with hφ
  refine ⟨Finset.image φ Finset.univ, ?_⟩
  intro c
  obtain ⟨l, col, hcol⟩ := hHJ (fun p => c (φ p))
  have hcol' : ∀ a : Fin k, c (φ (l a)) = col := fun a => hcol a
  set dir : Point := ∑ j, (if l.idxFun j = none then (1 : ℝ) else 0) • v j with hdir
  have key : ∀ (a : Fin k) (j : ι),
      emb (l a j) = emb (l 0 j) + emb a * (if l.idxFun j = none then (1 : ℝ) else 0) := by
    intro a j
    by_cases h : l.idxFun j = none
    · rw [l.apply_none a j h, l.apply_none 0 j h, if_pos h]
      simp [hemb]
    · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h
      simp only [l.apply_some hb, if_neg h]
      simp [hemb]
  have hline : ∀ a : Fin k, φ (l a) = φ (l 0) + emb a • dir := by
    intro a
    simp only [hφ, hdir, Finset.smul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [key a j, add_smul, mul_smul]
  have hofLp : (WithLp.ofLp dir) (0 : Fin 2)
      = ∑ j, (if l.idxFun j = none then (1 : ℝ) else 0) := by
    simp only [hdir, hv, WithLp.ofLp_sum, WithLp.ofLp_smul,
      Finset.sum_apply, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul, mul_one]
  have hdir_ne : dir ≠ 0 := by
    intro h0
    have hpos : (0 : ℝ) < (WithLp.ofLp dir) (0 : Fin 2) := by
      rw [hofLp]
      obtain ⟨j0, hj0⟩ := l.proper
      calc (0 : ℝ) < 1 := one_pos
        _ = (if l.idxFun j0 = none then (1 : ℝ) else 0) := (if_pos hj0).symm
        _ ≤ ∑ j, (if l.idxFun j = none then (1 : ℝ) else 0) :=
            Finset.single_le_sum
              (f := fun j => if l.idxFun j = none then (1 : ℝ) else 0)
              (fun j _ => by
                show (0 : ℝ) ≤ if l.idxFun j = none then (1 : ℝ) else 0
                split_ifs <;> norm_num)
              (Finset.mem_univ j0)
    rw [h0] at hpos
    simp at hpos
  refine ⟨Finset.image (fun a : Fin k => φ (l a)) Finset.univ, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨a, ha⟩ := hx
    exact ⟨l a, ha⟩
  · refine ⟨?_, ?_⟩
    · have hinj : Function.Injective (fun a : Fin k => φ (l a)) := by
        intro a a' haa'
        simp only at haa'
        rw [hline a, hline a'] at haa'
        have hsm : emb a • dir = emb a' • dir := add_left_cancel haa'
        have hee : emb a = emb a' := by
          by_contra hne
          have h2 : (emb a - emb a') • dir = 0 := by rw [sub_smul, hsm, sub_self]
          rcases smul_eq_zero.mp h2 with h | h
          · exact hne (sub_eq_zero.mp h)
          · exact hdir_ne h
        have : a.val = a'.val := by
          have := hee; simp only [hemb] at this; exact Nat.cast_injective this
        exact Fin.ext this
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    · refine ⟨⟨φ (l 0), dir, hdir_ne⟩, ?_⟩
      intro p hp
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
      obtain ⟨a, ha⟩ := hp
      exact ⟨emb a, by rw [← ha, hline a]⟩
  · intro p q hp hq
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp hq
    obtain ⟨a, ha⟩ := hp
    obtain ⟨a', ha'⟩ := hq
    rw [← ha, ← ha', hcol' a, hcol' a']

/-
## Part IV: Graham-Selfridge for k = 3
-/

/--
**Graham-Selfridge Theorem:**
There exists a finite set A ⊂ ℝ² such that any 2-coloring contains
3 monochromatic collinear points.

Formerly an axiom; now the `k = 3` instance of `erdos1090_construction`.
-/
theorem graham_selfridge :
    ∃ A : Finset Point, HasRamseyProperty A 3 :=
  erdos1090_construction 3 (by norm_num)

/--
**Explicit Construction Hint:**
One construction uses a carefully chosen arrangement of points
ensuring that any 2-coloring must have 3 collinear same-color points.
-/
theorem k3_case : Erdos1090Question 3 := by
  intro _
  exact graham_selfridge

/-
## Part V: Hales-Jewett Approach
-/

/--
**Combinatorial Line:**
In [k]ⁿ, a combinatorial line is a sequence where some coordinates
vary from 0 to k-1 while others are fixed.
-/
structure CombinatorialLine (k n : ℕ) where
  /-- Fixed coordinates and their values -/
  fixed : Finset (Fin n)
  fixedValues : Fin n → Fin k
  /-- Varying coordinates -/
  varying : Finset (Fin n)
  /-- Disjoint and covering -/
  disjoint : Disjoint fixed varying
  nonempty_varying : varying.Nonempty

/-
**Hales-Jewett Theorem (Statement):**
For any k and r, there exists n such that any r-coloring of [k]ⁿ
contains a monochromatic combinatorial line.
-/

/-
**Generic Projection:**
A "generic" projection from [k]ⁿ to ℝ² maps combinatorial lines
to geometric lines (for sufficiently general projection).
-/

/--
**Hunter's Observation:**
For sufficiently large n, a generic projection of [k]ⁿ into ℝ²
has the Ramsey property for k, by the Hales-Jewett theorem.

Formerly an axiom; now an honest theorem, see `erdos1090_construction`.
-/
theorem hunter_observation (k : ℕ) (hk : k ≥ 3) :
    ∃ A : Finset Point, HasRamseyProperty A k :=
  erdos1090_construction k hk

/-
## Part VI: Main Result
-/

/--
**Erdős #1090: SOLVED (Affirmative)**
For every k ≥ 3, there exists a finite set A ⊂ ℝ² such that
any 2-coloring of A contains k monochromatic collinear points.
-/
theorem erdos_1090_affirmative : ∀ k ≥ 3, Erdos1090Question k := by
  intro k hk
  intro _
  exact hunter_observation k hk

/-
## Part VII: Special Constructions
-/

/-
**Vertices of Regular n-gon:**
The vertices of a regular n-gon plus its center.
-/

/-
**Grid Points:**
An m × m grid of points.
Axiomatized since it requires embedding ℤ² into the Point type.
-/

/-
**Projective Plane Points:**
Points from a finite projective plane (useful for Ramsey constructions).
Axiomatized since the construction depends on projective geometry over 𝔽_q.
-/

/-
## Part VIII: Lower Bounds on Set Size
-/

/--
**Minimum Set Size:**
What is the minimum |A| such that A has the Ramsey property for k?
Let R(k) denote this minimum.
-/
noncomputable def ramseyNumber (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ A : Finset Point, A.card = n ∧ HasRamseyProperty A k}

/--
**Ramsey Property Forces Size ≥ k:**
Any finite set with the Ramsey property for `k` must contain at least `k`
points. Indeed, applying the property to the constant coloring already yields
a monochromatic `k`-collinear subset `S ⊆ A`, so `k ≤ |S| ≤ |A|`.
-/
theorem hasRamseyProperty_card_ge (A : Finset Point) (k : ℕ)
    (h : HasRamseyProperty A k) : k ≤ A.card := by
  obtain ⟨S, hSA, ⟨hSk, _⟩, _⟩ := h (fun _ => true)
  exact le_trans hSk (Finset.card_le_card hSA)

/--
**Monotonicity in the configuration:**
Enlarging the point set preserves the Ramsey property: if `A ⊆ B` and `A` has the
Ramsey property for `k`, then so does `B`.  For any 2-coloring, a monochromatic
`k`-collinear subset of `A` is *a fortiori* a subset of `B`.  This makes
`ramseyNumber k` a genuine threshold and is the structural basis for "minimum set
size" being well-defined.
-/
theorem hasRamseyProperty_mono {A B : Finset Point} (hAB : A ⊆ B) {k : ℕ}
    (hA : HasRamseyProperty A k) : HasRamseyProperty B k := by
  intro c
  obtain ⟨S, hSA, hScol, hSmono⟩ := hA c
  exact ⟨S, hSA.trans hAB, hScol, hSmono⟩

/--
**Monotonicity in `k` (downward):**
Requiring fewer monochromatic collinear points is easier.  If `A` has the Ramsey
property for `k` and `k' ≤ k`, then `A` has it for `k'`: the same monochromatic
`k`-collinear subset already has `≥ k ≥ k'` points on a common line.
-/
theorem hasRamseyProperty_antitone {A : Finset Point} {k k' : ℕ} (hk : k' ≤ k)
    (hA : HasRamseyProperty A k) : HasRamseyProperty A k' := by
  intro c
  obtain ⟨S, hSA, ⟨hSk, hline⟩, hSmono⟩ := hA c
  exact ⟨S, hSA, ⟨le_trans hk hSk, hline⟩, hSmono⟩

/--
**Trivial Lower Bound:**
R(k) ≥ k since we need at least k points to have k collinear.

For `k ≥ 3` the existence of a witnessing set (`hunter_observation`) makes the
defining set nonempty, so its infimum is attained by some set `A`, and that
set has at least `k` points by `hasRamseyProperty_card_ge`.
-/
theorem ramsey_lower_bound (k : ℕ) (hk : k ≥ 3) : ramseyNumber k ≥ k := by
  unfold ramseyNumber
  have hne : {n : ℕ | ∃ A : Finset Point, A.card = n ∧ HasRamseyProperty A k}.Nonempty := by
    obtain ⟨A, hA⟩ := hunter_observation k hk
    exact ⟨A.card, A, rfl, hA⟩
  obtain ⟨A, hcard, hA⟩ := Nat.sInf_mem hne
  rw [ge_iff_le, ← hcard]
  exact hasRamseyProperty_card_ge A k hA

/--
**Monotonicity of the Ramsey number in `k`:**
The minimal Ramsey-witnessing size grows with the demand: for `3 ≤ k' ≤ k`,
`R(k') ≤ R(k)`.  Requiring *more* monochromatic collinear points cannot make the
threshold smaller.  Concretely the set defining `R(k)` is contained in the one
defining `R(k')` (`hasRamseyProperty_antitone`), and `hunter_observation` makes the
`k`-set nonempty, so its infimum is attained by a set `A` that — having the property
for `k` — *a fortiori* has it for `k'`.  Hence `A.card = R(k)` lies in the
`k'`-defining set and `R(k') = sInf ≤ R(k)`.
-/
theorem ramseyNumber_mono {k k' : ℕ} (hk' : 3 ≤ k') (hkk : k' ≤ k) :
    ramseyNumber k' ≤ ramseyNumber k := by
  have hk : 3 ≤ k := le_trans hk' hkk
  have hne : {n : ℕ | ∃ A : Finset Point, A.card = n ∧ HasRamseyProperty A k}.Nonempty := by
    obtain ⟨A, hA⟩ := hunter_observation k hk
    exact ⟨A.card, A, rfl, hA⟩
  obtain ⟨A, hcard, hA⟩ := Nat.sInf_mem hne
  -- `A` attains `R(k)` and, by downward monotonicity in `k`, also witnesses `k'`.
  refine Nat.sInf_le ⟨A, ?_, hasRamseyProperty_antitone hkk hA⟩
  simpa [ramseyNumber] using hcard

/--
**Upper bound from any witness.**
Any finite set `A` that has the Ramsey property for `k` bounds the Ramsey number
from above: `R(k) ≤ |A|`.  This is the upper-bound companion of
`ramsey_lower_bound` — `A.card` lies in the set whose infimum defines `R(k)`, so
`Nat.sInf_le` applies.  Every explicit construction (e.g. the Hales–Jewett set of
`hunter_observation`) turns into a concrete bound on `R(k)` through this lemma.
-/
theorem ramseyNumber_le_of_hasRamseyProperty {A : Finset Point} {k : ℕ}
    (hA : HasRamseyProperty A k) : ramseyNumber k ≤ A.card :=
  Nat.sInf_le ⟨A, rfl, hA⟩

/--
**The Ramsey number is an attained minimum.**
For `k ≥ 3` the defining set is nonempty (`hunter_observation` supplies a witness),
so the infimum `R(k)` is *realized* by an actual optimal configuration: there is a
finite `A` with `|A| = R(k)` that already has the Ramsey property.  Together with
`ramsey_lower_bound` (`R(k) ≥ k`) this pins `R(k)` down as a genuine minimum rather
than a mere infimum, and exhibits the extremal set attaining it.
-/
theorem exists_hasRamseyProperty_card_eq_ramseyNumber (k : ℕ) (hk : k ≥ 3) :
    ∃ A : Finset Point, A.card = ramseyNumber k ∧ HasRamseyProperty A k := by
  have hne : {n : ℕ | ∃ A : Finset Point, A.card = n ∧ HasRamseyProperty A k}.Nonempty := by
    obtain ⟨A, hA⟩ := hunter_observation k hk
    exact ⟨A.card, A, rfl, hA⟩
  obtain ⟨A, hcard, hA⟩ := Nat.sInf_mem hne
  exact ⟨A, hcard, hA⟩

/-- The plane `ℝ²` is infinite: `t ↦ (t, 0)` (via `EuclideanSpace.single`) injects `ℝ`. -/
instance : Infinite Point :=
  Infinite.of_injective (fun a : ℝ => EuclideanSpace.single (0 : Fin 2) a) (fun a b h => by
    have hb : EuclideanSpace.single (0 : Fin 2) a = EuclideanSpace.single (0 : Fin 2) b := h
    have h0 : (EuclideanSpace.single (0 : Fin 2) a) 0
            = (EuclideanSpace.single (0 : Fin 2) b) 0 := by rw [hb]
    simpa [EuclideanSpace.single_apply] using h0)

/--
**Every size above `R(k)` is realizable.**
For `k ≥ 3` and any `n ≥ R(k)` there is a configuration of *exactly* `n` points with the
Ramsey property.  Take the extremal witness of size `R(k)`
(`exists_hasRamseyProperty_card_eq_ramseyNumber`) and pad it with fresh plane points, one at
a time: the plane is infinite, so a point outside the current set always exists, and enlarging
preserves the Ramsey property (`hasRamseyProperty_mono`).  Thus the property is not a knife-edge
phenomenon at the threshold — it persists for all larger cardinalities.
-/
theorem exists_hasRamseyProperty_card_eq {k : ℕ} (hk : k ≥ 3) {n : ℕ}
    (hn : ramseyNumber k ≤ n) :
    ∃ A : Finset Point, A.card = n ∧ HasRamseyProperty A k := by
  obtain ⟨A, hAcard, hA⟩ := exists_hasRamseyProperty_card_eq_ramseyNumber k hk
  have hAn : A.card ≤ n := hAcard ▸ hn
  clear hAcard hn
  induction n, hAn using Nat.le_induction with
  | base => exact ⟨A, rfl, hA⟩
  | succ m _ ih =>
    obtain ⟨B, hBcard, hB⟩ := ih
    obtain ⟨p, hp⟩ := Infinite.exists_notMem_finset B
    exact ⟨insert p B, by rw [Finset.card_insert_of_notMem hp, hBcard],
      hasRamseyProperty_mono (Finset.subset_insert p B) hB⟩

/--
**Realizable cardinalities are exactly the ray `[R(k), ∞)`.**
For `k ≥ 3`, a finite point set of size `n` with the Ramsey property exists *iff* `R(k) ≤ n`.
The forward direction is `ramseyNumber_le_of_hasRamseyProperty` (any witness bounds the infimum
from above); the reverse is the padding argument `exists_hasRamseyProperty_card_eq`.  This pins
down the realizable-size set completely: it is the full up-set above the threshold, with no gaps.
-/
theorem hasRamseyProperty_realizable_card_iff {k : ℕ} (hk : k ≥ 3) (n : ℕ) :
    (∃ A : Finset Point, A.card = n ∧ HasRamseyProperty A k) ↔ ramseyNumber k ≤ n := by
  constructor
  · rintro ⟨A, hcard, hA⟩
    exact hcard ▸ ramseyNumber_le_of_hasRamseyProperty hA
  · exact exists_hasRamseyProperty_card_eq hk

/-
**R(3) is Small:**
The k = 3 case can be achieved with a small set of points.
-/

/-
## Part IX: Connection to Other Results
-/

open Classical in
/--
**Relation to Sylvester-Gallai:**
The Sylvester-Gallai theorem says: In any finite set of points in ℝ²
not all collinear, there exists a line containing exactly 2 points.

This is a structural constraint on point configurations.
-/
def SylvesterGallai (A : Finset Point)
    (hA : ¬ ∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, Collinear p q r) : Prop :=
  ∃ l : Line, (A.filter (OnLine l)).card = 2

/--
**Relation to Helly's Theorem:**
Helly's theorem (about convex sets) is another classical result
in combinatorial geometry with a similar flavor.
-/
def HellyProperty (d : ℕ) : Prop :=
  ∀ (F : Finset (Set Point)),
    F.card ≥ d + 1 →
    (∀ S ∈ F, Convex ℝ S) →
    (∀ G : Finset (Set Point), G ⊆ F → G.card = d + 1 → (⋂ S ∈ G, S).Nonempty) →
    (⋂ S ∈ F, S).Nonempty

/-- **Helly's theorem in the plane — affirmative.**  `HellyProperty 2` holds for
`Point = ℝ²`: any finite family `F` of at least `3` convex sets in the plane in which
every `3`-element subfamily has a common point has a point common to *all* of `F`.

This is exactly Mathlib's `Convex.helly_theorem_set` specialised to
`Module.finrank ℝ ℝ² = 2`, so the placeholder threshold `d + 1 = 3` is the classical
planar Helly number.  Note the ambient space is fixed to the plane, so `d = 2`
(`= finrank ℝ Point`) is the *only* honest instance of the abstract `HellyProperty d`
defined above: for `d < 2` pairwise/triple intersection is too weak to force a common
point, and for `d > 2` the `(d+1)`-wise hypothesis is not what Helly consumes. -/
theorem helly_planar : HellyProperty 2 := by
  intro F hcard hconv hinter
  have hfr : Module.finrank ℝ Point = 2 := by simp [Point]
  -- Bridge the entry's `⋂ S ∈ F, S` notation to Mathlib's `⋂₀ (F : Set _)`.
  have hbF : (⋂ S ∈ F, S) = ⋂₀ (F : Set (Set Point)) := by ext x; simp
  rw [hbF]
  refine Convex.helly_theorem_set (𝕜 := ℝ) ?_ hconv ?_
  · -- `finrank + 1 ≤ #F` is exactly the `F.card ≥ 2 + 1` hypothesis.
    rw [hfr]; exact hcard
  · -- Every `(finrank + 1) = 3`-subfamily meets, from the entry-shaped `hinter`.
    intro G hG hGcard
    have hbG : (⋂₀ (G : Set (Set Point))) = ⋂ S ∈ G, S := by ext x; simp
    rw [hbG]
    exact hinter G hG (by rw [hfr] at hGcard; exact hGcard)

/-
## Part X: Generalizations
-/

/--
**r-Coloring Version:**
For r colors instead of 2, does the same hold?
-/
def Erdos1090Generalized (k r : ℕ) : Prop :=
  k ≥ 3 → r ≥ 2 →
  ∃ A : Finset Point, ∀ c : Point → Fin r,
    ∃ S : Finset Point, S ⊆ A ∧ IsKCollinear S k ∧
      ∀ p ∈ S, ∀ q ∈ S, c p = c q

/-- **Erdős #1090 — `r`-coloring generalisation, affirmative.**  The `r`-color version
`Erdos1090Generalized k r` holds for every `k` and `r`: for `k ≥ 3` there is a finite
`A ⊂ ℝ²` such that *every* `r`-coloring of `A` contains `k` monochromatic collinear points.
Immediate from `ramsey_construction_general (Fin r)` — the multicolor Hales–Jewett input
needs no extra hypothesis on `r`, so the `r ≥ 2` premise is not even required. -/
theorem erdos1090_generalized_affirmative (k r : ℕ) : Erdos1090Generalized k r := by
  intro hk _
  obtain ⟨A, hA⟩ := ramsey_construction_general (Fin r) k hk
  refine ⟨A, fun c => ?_⟩
  obtain ⟨S, hSA, hScol, hmono⟩ := hA c
  exact ⟨S, hSA, hScol, fun p hp q hq => hmono p q hp hq⟩

/--
**Collinearity in `ℝ^d`.**  A finite set `S ⊆ (Fin d → ℝ)` is collinear when all
of its points lie on one affine line `{p₀ + t • dir | t ∈ ℝ}` with a nonzero
direction `dir`.  This is the genuine higher-dimensional analogue of the planar
`IsKCollinear`: `k` collinear points span an affine line (a `1`-flat), which is a
fortiori contained in a common hyperplane, so it is the *strongest* faithful
reading of "the analogue in `ℝ^d`". -/
def CollinearInDim {d : ℕ} (S : Finset (Fin d → ℝ)) : Prop :=
  ∃ p₀ dir : Fin d → ℝ, dir ≠ 0 ∧ ∀ s ∈ S, ∃ t : ℝ, s = p₀ + t • dir

/--
**Higher Dimensions.**  Does the monochromatic-collinear analogue hold in `ℝ^d`?
For `d ≥ 2` and `k ≥ 3` we ask for a finite `A ⊂ ℝ^d` such that every `2`-coloring
of `A` contains `k` monochromatic points lying on a common affine line.  (Points on
a line lie on a common hyperplane, so this affirms the planes/hyperplanes reading of
the classical question in every dimension.)
-/
def Erdos1090HigherDim (d k : ℕ) : Prop :=
  2 ≤ d → 3 ≤ k →
  ∃ A : Finset (Fin d → ℝ), ∀ c : (Fin d → ℝ) → Bool,
    ∃ S : Finset (Fin d → ℝ), S ⊆ A ∧ k ≤ S.card ∧ CollinearInDim S ∧
      ∀ p ∈ S, ∀ q ∈ S, c p = c q

/-- **Erdős #1090 — higher-dimensional analogue, affirmative.**  For every `d ≥ 2`
and `k ≥ 3` there is a finite `A ⊂ ℝ^d` such that every `2`-coloring of `A` contains
`k` monochromatic collinear points.  Proved by the same Hales–Jewett generic-projection
construction as the planar case, projecting the combinatorial cube `[k]^ι` directly into
`ℝ^d` via `φ p = ∑ j, (p j) • v j` with `v j = e₀ + (w j) • e₁` (first coordinate `1`,
second coordinate `w j`, the rest `0`).  A monochromatic combinatorial line maps to `k`
distinct collinear points of one color; the image direction has first coordinate
`|varying set| ≥ 1 > 0`, hence is nonzero. -/
theorem erdos1090_higherDim_affirmative (d k : ℕ) : Erdos1090HigherDim d k := by
  classical
  intro hd hk
  haveI : NeZero k := ⟨by omega⟩
  -- The first coordinate index, available since `d ≥ 2`; used to witness `dir ≠ 0`.
  set e0 : Fin d := ⟨0, by omega⟩ with he0
  -- Hales–Jewett: a finite index type `ι` controlling every `2`-coloring of `[k]^ι`.
  obtain ⟨ι, ιfin, hHJ⟩ :=
    Combinatorics.Line.exists_mono_in_high_dimension (Fin k) Bool
  haveI : Fintype ι := ιfin
  set emb : Fin k → ℝ := fun a => (a.val : ℝ) with hemb
  set w : ι → ℝ := fun j => ((Fintype.equivFin ι j).val : ℝ) with hw
  -- Per-coordinate image vectors in `ℝ^d`: `v j = (1, w j, 0, …, 0)`.
  set v : ι → (Fin d → ℝ) :=
    fun j i => if (i : ℕ) = 0 then 1 else if (i : ℕ) = 1 then w j else 0 with hv
  -- Linear "generic projection" `φ : [k]^ι → ℝ^d`.
  set φ : (ι → Fin k) → (Fin d → ℝ) := fun p => ∑ j, emb (p j) • v j with hφ
  refine ⟨Finset.image φ Finset.univ, ?_⟩
  intro c
  obtain ⟨l, col, hcol⟩ := hHJ (fun p => c (φ p))
  have hcol' : ∀ a : Fin k, c (φ (l a)) = col := fun a => hcol a
  set dir : (Fin d → ℝ) := ∑ j, (if l.idxFun j = none then (1 : ℝ) else 0) • v j with hdir
  have key : ∀ (a : Fin k) (j : ι),
      emb (l a j) = emb (l 0 j) + emb a * (if l.idxFun j = none then (1 : ℝ) else 0) := by
    intro a j
    by_cases h : l.idxFun j = none
    · rw [l.apply_none a j h, l.apply_none 0 j h, if_pos h]
      simp [hemb]
    · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h
      simp only [l.apply_some hb, if_neg h]
      simp [hemb]
  have hline : ∀ a : Fin k, φ (l a) = φ (l 0) + emb a • dir := by
    intro a
    simp only [hφ, hdir, Finset.smul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [key a j, add_smul, mul_smul]
  -- The image direction is nonzero: its `e0`-coordinate equals `|varying set| ≥ 1`.
  have heval : dir e0 = ∑ j, (if l.idxFun j = none then (1 : ℝ) else 0) := by
    rw [hdir, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Pi.smul_apply, smul_eq_mul]
    have hv0 : v j e0 = 1 := by simp [hv, he0]
    rw [hv0, mul_one]
  have hdir_ne : dir ≠ 0 := by
    intro h0
    have hpos : (0 : ℝ) < dir e0 := by
      rw [heval]
      obtain ⟨j0, hj0⟩ := l.proper
      calc (0 : ℝ) < 1 := one_pos
        _ = (if l.idxFun j0 = none then (1 : ℝ) else 0) := (if_pos hj0).symm
        _ ≤ ∑ j, (if l.idxFun j = none then (1 : ℝ) else 0) :=
            Finset.single_le_sum
              (f := fun j => if l.idxFun j = none then (1 : ℝ) else 0)
              (fun j _ => by
                show (0 : ℝ) ≤ if l.idxFun j = none then (1 : ℝ) else 0
                split_ifs <;> norm_num)
              (Finset.mem_univ j0)
    rw [h0] at hpos
    simp at hpos
  refine ⟨Finset.image (fun a : Fin k => φ (l a)) Finset.univ, ?_, ?_, ?_, ?_⟩
  · -- `S ⊆ A`
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨a, ha⟩ := hx
    exact ⟨l a, ha⟩
  · -- `k ≤ S.card`
    have hinj : Function.Injective (fun a : Fin k => φ (l a)) := by
      intro a a' haa'
      simp only at haa'
      rw [hline a, hline a'] at haa'
      have hsm : emb a • dir = emb a' • dir := add_left_cancel haa'
      have hee : emb a = emb a' := by
        by_contra hne
        have h2 : (emb a - emb a') • dir = 0 := by rw [sub_smul, hsm, sub_self]
        rcases smul_eq_zero.mp h2 with h | h
        · exact hne (sub_eq_zero.mp h)
        · exact hdir_ne h
      have : a.val = a'.val := by
        have := hee; simp only [hemb] at this; exact Nat.cast_injective this
      exact Fin.ext this
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · -- `CollinearInDim S`
    refine ⟨φ (l 0), dir, hdir_ne, ?_⟩
    intro p hp
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨a, ha⟩ := hp
    exact ⟨emb a, by rw [← ha, hline a]⟩
  · -- Monochromatic.
    intro p hp q hq
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp hq
    obtain ⟨a, ha⟩ := hp
    obtain ⟨a', ha'⟩ := hq
    rw [← ha, ← ha', hcol' a, hcol' a']

/-
## Part XI: Main Results Summary
-/

/--
**Erdős Problem #1090: Monochromatic Collinear Points**

Status: SOLVED (Affirmative)

Summary:
1. For k = 3: Graham and Selfridge
2. For all k ≥ 3: Hunter's observation using Hales-Jewett
3. Generic projection of [k]ⁿ to ℝ² has the required property

The answer is YES: For every k ≥ 3, there exists a finite set A ⊂ ℝ²
such that any 2-coloring contains k monochromatic collinear points.
-/
theorem erdos_1090_summary :
    -- k = 3 case (Graham-Selfridge)
    (∃ A : Finset Point, HasRamseyProperty A 3) ∧
    -- General case (Hunter via Hales-Jewett)
    (∀ k ≥ 3, ∃ A : Finset Point, HasRamseyProperty A k) :=
  ⟨graham_selfridge, fun k hk => hunter_observation k hk⟩

/--
The main theorem: Erdős #1090 is solved affirmatively.
-/
theorem erdos_1090 : ∀ k ≥ 3, Erdos1090Question k := erdos_1090_affirmative

end Erdos1090
