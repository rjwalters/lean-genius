/-
  Aristotle target (self-contained): Klein's upper bound for the Happy Ending
  Problem — the single remaining axiom of `Erdos107OQ01`.

  Goal: any five points in general position in the plane contain a convex
  quadrilateral.  All supporting definitions (`InGeneralPosition`,
  `IsConvexNGon`, `HasConvexNGon`, `CardSet`) are inlined here so the file is
  self-contained for automated proof search (no local-project imports).

  Classical proof (Klein 1931), by the size of the convex hull of the 5 points:
    • Hull has 4 or 5 vertices: any 4 hull vertices are in convex position.
    • Hull is a triangle: the remaining 2 points lie strictly inside.  The line
      through those 2 interior points misses all 3 triangle vertices (general
      position), so 2 of the 3 vertices lie on the same side; those 2 vertices
      with the 2 interior points form a convex quadrilateral.

  PROVENANCE: the full proof below was produced by Aristotle (Harmonic) proof
  search — project `a1441c24-c444-4cb6-ba78-9c0357beffcf`, task
  `49f58f23-9f57-46e9-91ed-25937c688b89` — and verified clean by Aristotle
  (no `sorry`/`admit`, no new axioms; `#print axioms klein_upper_bound` lists
  only `propext`, `Classical.choice`, `Quot.sound`).  It was proved against
  Mathlib at Lean toolchain v4.28.0; this repository pins v4.26.0, so a CI build
  on the repo toolchain must confirm the port before the discharge in
  `Erdos107OQ01.lean` is treated as verified.
-/
import Mathlib

namespace KleinUpperAristotle

open Finset

/-- The Euclidean plane. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- A finite set of points is in **general position** if no three of its
    points are collinear. -/
def InGeneralPosition (S : Set E2) : Prop :=
  ∀ p q r : E2, p ∈ S → q ∈ S → r ∈ S →
    p ≠ q → q ≠ r → p ≠ r → ¬Collinear ℝ ({p, q, r} : Set _)

/-- `n` points form a **convex `n`-gon** if each is a vertex of the convex hull
    of the set, i.e. lies outside the hull of the others. -/
def IsConvexNGon (n : ℕ) (S : Finset E2) : Prop :=
  S.card = n ∧ ∀ p ∈ S, p ∉ convexHull ℝ ((S.erase p : Set _))

/-- A point set **contains a convex `n`-gon** if some `n`-point subset is one. -/
def HasConvexNGon (n : ℕ) (S : Finset E2) : Prop :=
  ∃ T ⊆ S, IsConvexNGon n T

/-- The set of `N` such that any `N` points in general position contain a
    convex `n`-gon. -/
def CardSet (n : ℕ) : Set ℕ :=
  { N | ∀ (pts : Finset E2),
    pts.card = N → InGeneralPosition ↑pts → HasConvexNGon n pts }

/-! ### Helper lemmas -/

/-
An extreme point of the convex hull of a finite set is not in the convex
    hull of the remaining points.
-/
lemma extreme_not_in_hull_erase (pts : Finset E2) (p : E2)
    (hp : p ∈ (convexHull ℝ (↑pts : Set E2)).extremePoints ℝ) :
    p ∉ convexHull ℝ ((↑pts : Set E2) \ {p}) := by
  contrapose! hp;
  intro h;
  have h_convex_hull_subset : convexHull ℝ (pts \ {p} : Set E2) ⊆ convexHull ℝ (convexHull ℝ pts \ {p}) := by
    exact convexHull_mono fun x hx => ⟨ subset_convexHull ℝ _ hx.1, hx.2 ⟩;
  convert Convex.mem_extremePoints_iff_mem_diff_convexHull_diff ( convex_convexHull ℝ ( pts : Set E2 ) ) |>.1 h using 1;
  grind

/-
Finite-dimensional Krein–Milman for a finite set: every point of a finite
    set lies in the convex hull of the extreme points of its convex hull.
-/
lemma subset_convexHull_extremePoints (pts : Finset E2) :
    (↑pts : Set E2) ⊆ convexHull ℝ ((convexHull ℝ (↑pts : Set E2)).extremePoints ℝ) := by
  -- Let A = convexHull ℝ ↑pts and E = A.extremePoints ℝ.
  set A : Set E2 := convexHull ℝ (pts : Set E2)
  set E : Set E2 := A.extremePoints ℝ;
  -- A is compact (Set.Finite.isCompact_convexHull on the finite ↑pts) and convex (convex_convexHull).
  have hA_compact : IsCompact A := by
    exact Set.Finite.isCompact_convexHull ( Finset.finite_toSet pts )
  have hA_convex : Convex ℝ A := by
    exact convex_convexHull ℝ _;
  -- By closure_convexHull_extremePoints, closure (convexHull ℝ E) = A.
  have h_closure : closure (convexHull ℝ E) = A := by
    apply_rules [ closure_convexHull_extremePoints ];
  -- Now E ⊆ ↑pts by extremePoints_convexHull_subset, so E is finite, hence convexHull ℝ E is compact (Set.Finite.isCompact_convexHull) and therefore closed, so closure (convexHull ℝ E) = convexHull ℝ E.
  have hE_finite : Set.Finite E := by
    exact Set.Finite.subset ( Finset.finite_toSet pts ) ( extremePoints_convexHull_subset )
  have h_convexHull_E_closed : IsClosed (convexHull ℝ E) := by
    exact hE_finite.isClosed_convexHull
  have h_closure_eq : closure (convexHull ℝ E) = convexHull ℝ E := by
    exact h_convexHull_E_closed.closure_eq;
  exact fun x hx => h_closure_eq ▸ h_closure ▸ subset_convexHull ℝ _ hx

/-
Case A: if four of the points are extreme points of the whole convex hull,
    they form a convex quadrilateral.
-/
lemma hasConvexNGon_of_four_extreme (pts T : Finset E2) (hT : T ⊆ pts)
    (hcard : T.card = 4)
    (hext : ∀ p ∈ T, p ∈ (convexHull ℝ (↑pts : Set E2)).extremePoints ℝ) :
    HasConvexNGon 4 pts := by
  refine' ⟨ T, hT, hcard, _ ⟩;
  exact fun p hp => by simpa [ Finset.coe_erase ] using extreme_not_in_hull_erase pts p ( hext p hp ) |> fun h => Set.notMem_subset ( convexHull_mono <| by aesop_cat ) h;

/-
The signed-area / cross-product test for collinearity in the plane.
-/
lemma cross_eq_zero_iff_collinear (a b w : E2) :
    (b 0 - a 0) * (w 1 - a 1) - (b 1 - a 1) * (w 0 - a 0) = 0 ↔
      Collinear ℝ ({a, b, w} : Set E2) := by
  rw [ collinear_iff_of_mem ] <;> norm_num;
  any_goals tauto;
  constructor <;> intro h;
  · by_cases h_cases : b = a ∨ w = a ∨ b = w;
    · rcases h_cases with ( rfl | rfl | rfl ) <;> norm_num at *;
      · exact ⟨ w - b, 1, by norm_num ⟩;
      · exact ⟨ b - w, 1, by norm_num ⟩;
      · exact ⟨ b - a, 1, by norm_num ⟩;
    · -- Since $b \neq a$ and $w \neq a$, we can solve for $r$ in the equation $b = r • v + a$.
      obtain ⟨r, hr⟩ : ∃ r : ℝ, b = r • (w - a) + a := by
        by_cases h_cases : w 0 = a 0;
        · by_cases h_cases : w 1 = a 1;
          · exact False.elim <| ‹¬ ( b = a ∨ w = a ∨ b = w ) › <| Or.inr <| Or.inl <| by ext i; fin_cases i <;> aesop;
          · use (b 1 - a 1) / (w 1 - a 1);
            ext i; fin_cases i <;> simp_all +decide [ sub_eq_iff_eq_add ] ;
        · use (b 0 - a 0) / (w 0 - a 0);
          ext i; fin_cases i <;> simp_all +decide [ sub_eq_iff_eq_add ] ;
          grind;
      exact ⟨ w - a, ⟨ 0, by norm_num ⟩, ⟨ r, hr ⟩, ⟨ 1, by norm_num ⟩ ⟩;
  · rcases h with ⟨ v, ⟨ r, hr ⟩, ⟨ s, hs ⟩, ⟨ t, ht ⟩ ⟩ ; simp_all +decide [ sub_eq_iff_eq_add ] ; ring;

/-
A linear functional vanishing (relative to its value at `a`) exactly on the
    line through `a` and `b`.
-/
lemma exists_line_functional (a b : E2) :
    ∃ f : E2 →ₗ[ℝ] ℝ, f a = f b ∧
      ∀ w : E2, (f w = f a ↔ Collinear ℝ ({a, b, w} : Set E2)) := by
  refine' ⟨ _, _ ⟩;
  refine' { toFun := fun w => ( b 0 - a 0 ) * w 1 - ( b 1 - a 1 ) * w 0, map_add' := _, map_smul' := _ };
  all_goals norm_num [ mul_add, add_mul, mul_sub, sub_mul ];
  · intros; ring;
  · intros; ring;
  · refine' ⟨ _, _ ⟩;
    · ring;
    · intro w; rw [ ← cross_eq_zero_iff_collinear ] ; ring;
      constructor <;> intro h <;> linarith

/-
Pigeonhole: among three nonzero reals, two share the same sign.
-/
lemma two_same_sign {sx sy sz : ℝ} (hx : sx ≠ 0) (hy : sy ≠ 0) (hz : sz ≠ 0) :
    (0 < sx ∧ 0 < sy) ∨ (0 < sy ∧ 0 < sz) ∨ (0 < sx ∧ 0 < sz) ∨
    (sx < 0 ∧ sy < 0) ∨ (sy < 0 ∧ sz < 0) ∨ (sx < 0 ∧ sz < 0) := by
  grind

/-
If `f a < f p`, `f a < f q`, `f b = f a` and `a ≠ b`, then `a` is not in the
    convex hull of `{p, q, b}` (a separating-functional argument).
-/
lemma not_mem_convexHull_triple_of_functional (f : E2 →ₗ[ℝ] ℝ) (p q b a : E2)
    (hp : f a < f p) (hq : f a < f q) (hb : f b = f a) (hab : a ≠ b) :
    a ∉ convexHull ℝ ({p, q, b} : Set E2) := by
  -- Assume for contradiction that $a \in \text{convexHull} \{p, q, b\}$.
  by_contra h_contra
  obtain ⟨α, β, γ, hαβγ⟩ : ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧ a = α • p + β • q + γ • b := by
    rw [ convexHull_insert ] at h_contra;
    · simp_all +decide [ segment_eq_image ];
      obtain ⟨ i, hi, x, hx, rfl ⟩ := h_contra; exact ⟨ 1 - x, by linarith, x * ( 1 - i ), by nlinarith, x * i, by nlinarith, by ring, by ext ; simpa using by ring ⟩ ;
    · norm_num;
  -- Applying the linear map $f$ to both sides of the equation $a = α • p + β • q + γ • b$, we get $f(a) = α • f(p) + β • f(q) + γ • f(b)$.
  have h_apply_f : f a = α * f p + β * f q + γ * f b := by
    simp +decide [ hαβγ, map_add, map_smul ];
  -- Since $f(p) > f(a)$ and $f(q) > f(a)$, we have $α * (f(p) - f(a)) + β * (f(q) - f(a)) = 0$.
  have h_zero : α * (f p - f a) + β * (f q - f a) = 0 := by
    grind;
  -- Since $f(p) > f(a)$ and $f(q) > f(a)$, we have $α = 0$ and $β = 0$.
  have h_alpha_beta_zero : α = 0 ∧ β = 0 := by
    constructor <;> nlinarith;
  norm_num [ show γ = 1 by linarith ] at * ; aesop ( simp_config := { singlePass := true } ) ;

/-
Collinearity passes to the convex hull.
-/
lemma collinear_convexHull_of_collinear (s : Set E2) (h : Collinear ℝ s) :
    Collinear ℝ (convexHull ℝ s) := by
  -- If $s$ is collinear, then $s$ is contained in some affine subspace of dimension at most 1.
  obtain ⟨A, hA⟩ : ∃ A : AffineSubspace ℝ E2, s ⊆ A ∧ Module.finrank ℝ (A.direction) ≤ 1 := by
    rw [ collinear_iff_exists_forall_eq_smul_vadd ] at h;
    obtain ⟨ p₀, v, h ⟩ := h; use AffineSubspace.mk' p₀ ( Submodule.span ℝ { v } ) ; simp_all +decide [ Set.subset_def ] ;
    exact ⟨ fun x hx => by obtain ⟨ r, rfl ⟩ := h x hx; exact Submodule.mem_span_singleton.mpr ⟨ r, by simp +decide [ add_comm ] ⟩, by rw [ AffineSubspace.direction_mk' ] ; exact finrank_span_le_card _ ⟩;
  refine' collinear_iff_finrank_le_one.mpr _;
  refine' le_trans _ hA.2;
  refine' Submodule.finrank_mono _;
  refine' vectorSpan_mono _ _;
  exact convexHull_min hA.1 ( A.convex )

/-
Five (or more) points in general position are not all collinear.
-/
lemma not_collinear_pts (pts : Finset E2) (h5 : 3 ≤ pts.card)
    (hgen : InGeneralPosition ↑pts) : ¬ Collinear ℝ (↑pts : Set E2) := by
  -- By definition of InGeneralPosition, if pts were collinear, there would exist three distinct points in pts that are collinear, which contradicts hgen.
  by_contra h_collinear
  obtain ⟨p, q, r, hp, hq, hr, h_distinct⟩ : ∃ p q r : E2, p ∈ pts ∧ q ∈ pts ∧ r ∈ pts ∧ p ≠ q ∧ q ≠ r ∧ p ≠ r ∧ Collinear ℝ ({p, q, r} : Set E2) := by
    rcases Finset.two_lt_card.1 h5 with ⟨ p, hp, q, hq, hpq ⟩ ; use p, q ; simp_all +decide;
    obtain ⟨ r, hr, hpq, hpr, hqr ⟩ := hpq; exact ⟨ r, hr, hpq, hqr, hpr, h_collinear.subset <| by aesop_cat ⟩ ;
  exact hgen p q r hp hq hr h_distinct.1 h_distinct.2.1 h_distinct.2.2.1 h_distinct.2.2.2

/-
From two extreme points `p, q` on the same strict side (under `f`) of the
    line through `a, b` (with `f a = f b`), the four points `p, q, a, b` form a
    convex quadrilateral.
-/
lemma hasConvexNGon_of_pair (pts : Finset E2) (f : E2 →ₗ[ℝ] ℝ) (p q a b : E2)
    (hp : p ∈ (convexHull ℝ (↑pts : Set E2)).extremePoints ℝ)
    (hq : q ∈ (convexHull ℝ (↑pts : Set E2)).extremePoints ℝ)
    (ha : a ∈ pts) (hb : b ∈ pts)
    (hpq : p ≠ q) (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b)
    (hab : a ≠ b)
    (hfp : f a < f p) (hfq : f a < f q) (hfab : f b = f a) :
    HasConvexNGon 4 pts := by
  refine' ⟨ { p, q, a, b }, _, _, _ ⟩ <;> simp_all +decide;
  · -- Since $p$ and $q$ are extreme points of the convex hull of $pts$, and the convex hull is just the set of all convex combinations of points in $pts$, $p$ and $q$ must be in $pts$.
    have hp_in_pts : p ∈ pts := by
      have h_extreme_subset : (convexHull ℝ pts : Set E2).extremePoints ℝ ⊆ pts := by
        exact extremePoints_convexHull_subset
      exact h_extreme_subset hp
    have hq_in_pts : q ∈ pts := by
      have := @extremePoints_convexHull_subset;
      exact this hq
    exact Finset.insert_subset_iff.mpr ⟨hp_in_pts, Finset.insert_subset_iff.mpr ⟨hq_in_pts, Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩⟩⟩;
  · refine' ⟨ _, _, _, _ ⟩;
    · -- Since $p$ is an extreme point of the convex hull of $pts$, it cannot be in the convex hull of any subset of $pts$ that does not include $p$.
      have h_extreme : p ∉ convexHull ℝ (↑pts \ {p}) := by
        convert extreme_not_in_hull_erase pts p hp using 1;
      refine' fun h => h_extreme <| convexHull_mono _ h;
      simp_all +decide [ Set.insert_subset_iff ];
      have h_extreme : (convexHull ℝ (pts : Set E2)).extremePoints ℝ ⊆ pts := by
        grind +suggestions
      exact h_extreme hq |> fun h => by aesop;
    · convert extreme_not_in_hull_erase _ _ hq using 1;
      refine' iff_of_false _ _;
      · refine' fun h => _;
        have h_convex_hull_subset : convexHull ℝ ({p, q, a, b} \ {q} : Set E2) ⊆ convexHull ℝ (pts \ {q} : Set E2) := by
          refine' convexHull_mono _;
          simp_all +decide [ Set.subset_def, Set.extremePoints ];
          have h_extreme : (convexHull ℝ (pts : Set E2)).extremePoints ℝ ⊆ pts := by
            exact extremePoints_convexHull_subset;
          exact h_extreme ⟨ hp.1, hp.2 ⟩;
        exact absurd ( h_convex_hull_subset h ) ( by simpa using extreme_not_in_hull_erase pts q hq );
      · convert extreme_not_in_hull_erase pts q hq using 1;
    · convert not_mem_convexHull_triple_of_functional f p q b a hfp hfq hfab hab using 1;
      congr! 2 ; aesop;
    · convert not_mem_convexHull_triple_of_functional f p q a b ( by linarith ) ( by linarith ) ( by linarith ) ( by tauto ) using 1;
      congr! 2 ; aesop

/-
Case B (triangle): three extreme points `x, y, z` together with two further
    points `a, b` of the set contain a convex quadrilateral.
-/
set_option maxHeartbeats 1000000 in
lemma hasConvexNGon_caseB (pts : Finset E2) (hgen : InGeneralPosition ↑pts)
    (x y z a b : E2)
    (hx : x ∈ (convexHull ℝ (↑pts : Set E2)).extremePoints ℝ)
    (hy : y ∈ (convexHull ℝ (↑pts : Set E2)).extremePoints ℝ)
    (hz : z ∈ (convexHull ℝ (↑pts : Set E2)).extremePoints ℝ)
    (ha : a ∈ pts) (hb : b ∈ pts)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hax : a ≠ x) (hay : a ≠ y) (haz : a ≠ z)
    (hbx : b ≠ x) (hby : b ≠ y) (hbz : b ≠ z) (hab : a ≠ b) :
    HasConvexNGon 4 pts := by
  -- By the statement of `hasConvexNGon_of_pair`, we need to find extreme points `p`, `q` on the same side of the line through `a`, `b`, under some linear functional `f`.
  obtain ⟨f, hf⟩ := exists_line_functional a b;
  have hfx : f x ≠ f a ∧ f y ≠ f a ∧ f z ≠ f a := by
    have h_not_collinear : ¬Collinear ℝ ({a, b, x} : Set E2) ∧ ¬Collinear ℝ ({a, b, y} : Set E2) ∧ ¬Collinear ℝ ({a, b, z} : Set E2) := by
      have h_not_collinear : ∀ p ∈ pts, p ≠ a → p ≠ b → ¬Collinear ℝ ({a, b, p} : Set E2) := by
        intro p hp hpa hpb; specialize hgen a b p; simp_all +decide;
        exact hgen ( Ne.symm hpb ) ( Ne.symm hpa );
      have h_extreme_subset : Set.extremePoints ℝ (convexHull ℝ (pts : Set E2)) ⊆ pts := by
        grind +suggestions;
      exact ⟨ h_not_collinear x ( h_extreme_subset hx ) ( by tauto ) ( by tauto ), h_not_collinear y ( h_extreme_subset hy ) ( by tauto ) ( by tauto ), h_not_collinear z ( h_extreme_subset hz ) ( by tauto ) ( by tauto ) ⟩;
    grind;
  -- By two_same_sign, at least two of the three values `f x - f a`, `f y - f a`, `f z - f a` have the same strict sign.
  obtain ⟨p, q, hpq, hpsign⟩ : ∃ p q : E2, p ∈ ({x, y, z} : Finset E2) ∧ q ∈ ({x, y, z} : Finset E2) ∧ p ≠ q ∧ (0 < f p - f a ∧ 0 < f q - f a) ∨ p ∈ ({x, y, z} : Finset E2) ∧ q ∈ ({x, y, z} : Finset E2) ∧ p ≠ q ∧ (f p - f a < 0 ∧ f q - f a < 0) := by
    obtain ⟨p, q, hpq, hpsign⟩ : ∃ p q : E2, p ∈ ({x, y, z} : Finset E2) ∧ q ∈ ({x, y, z} : Finset E2) ∧ p ≠ q ∧ (0 < f p - f a ∧ 0 < f q - f a) ∨ p ∈ ({x, y, z} : Finset E2) ∧ q ∈ ({x, y, z} : Finset E2) ∧ p ≠ q ∧ (f p - f a < 0 ∧ f q - f a < 0) := by
      have := two_same_sign (sub_ne_zero.mpr hfx.left) (sub_ne_zero.mpr hfx.right.left) (sub_ne_zero.mpr hfx.right.right)
      rcases this with ( h | h | h | h | h | h ) <;> [ exact ⟨ x, y, by aesop ⟩ ; exact ⟨ y, z, by aesop ⟩ ; exact ⟨ x, z, by aesop ⟩ ; exact ⟨ x, y, by aesop ⟩ ; exact ⟨ y, z, by aesop ⟩ ; exact ⟨ x, z, by aesop ⟩ ];
    · exact ⟨ p, q, Or.inl ⟨ hpq, hpsign ⟩ ⟩;
    · exact ⟨ p, q, Or.inr ‹_› ⟩;
  · apply hasConvexNGon_of_pair pts f p q a b;
    grind +qlia;
    all_goals aesop;
  · apply hasConvexNGon_of_pair pts (-f) p q a b;
    all_goals norm_num at *;
    all_goals aesop

/-! ### Main theorem -/

/-
**Klein 1931 (upper bound).** Any five points in general position in the
    plane contain a convex quadrilateral: `5 ∈ CardSet 4`.
-/
set_option maxHeartbeats 1000000 in
theorem klein_upper_bound : (5 : ℕ) ∈ CardSet 4 := by
  -- Assume we have 5 points in general position in the plane.
  intro pts hpts hgen
  set E := (convexHull ℝ (pts : Set E2)).extremePoints ℝ with hEdef
  have hEsub : E ⊆ pts := by
    apply_rules [ extremePoints_convexHull_subset ];
  by_cases hEcard : E.ncard ≥ 4;
  · have := Set.exists_subset_card_eq hEcard;
    obtain ⟨ t, ht₁, ht₂ ⟩ := this; have := Set.Finite.exists_finset_coe ( show Set.Finite t from Set.finite_of_ncard_pos ( by linarith ) ) ; obtain ⟨ s, hs ⟩ := this; simp_all +decide;
    exact hasConvexNGon_of_four_extreme pts s ( by aesop_cat ) ( by aesop_cat ) ( by aesop_cat );
  · by_cases hEcard : E.ncard ≤ 2;
    · -- Since $E$ is finite and has at most 2 elements, it must be collinear.
      have hEcollinear : Collinear ℝ E := by
        interval_cases _ : Set.ncard E <;> simp_all +decide [ collinear_iff_exists_forall_eq_smul_vadd ];
        · rw [ @Set.ncard_eq_zero ] at *;
          · aesop;
          · exact Set.Finite.subset ( Finset.finite_toSet pts ) hEsub;
        · rcases ‹_› with ⟨ p, hp ⟩ ; use p, 0; aesop;
        · rw [ Set.ncard_eq_two ] at *;
          rcases ‹_› with ⟨ x, y, hxy, h ⟩ ; use x, y - x; intro p hp; rw [ h ] at hp; rcases hp with ( rfl | rfl ) <;> [ exact ⟨ 0, by norm_num ⟩ ; exact ⟨ 1, by norm_num ⟩ ] ;
      -- Since $E$ is collinear, the convex hull of $E$ is also collinear.
      have hEconvexHullcollinear : Collinear ℝ (convexHull ℝ E) := by
        apply collinear_convexHull_of_collinear; assumption;
      -- Since $pts$ is a subset of the convex hull of $E$, and the convex hull of $E$ is collinear, $pts$ must also be collinear.
      have hpts_collinear : Collinear ℝ (pts : Set E2) := by
        refine' hEconvexHullcollinear.subset _;
        convert subset_convexHull_extremePoints pts using 1;
      exact absurd hpts_collinear ( not_collinear_pts pts ( by linarith ) hgen );
    · -- Since $E$ has exactly 3 elements, let's denote them as $x$, $y$, and $z$.
      obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ : ∃ x y z : E2, x ∈ E ∧ y ∈ E ∧ z ∈ E ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ E = {x, y, z} := by
        interval_cases _ : Set.ncard E;
        rw [ Set.ncard_eq_three ] at *; aesop;
      -- The complement pts \ Ef has card 5 - 3 = 2 (Finset.card_sdiff with Ef ⊆ pts), so by Finset.card_eq_two it is {a,b} with a ≠ b; a,b ∈ pts and a,b ∉ Ef, giving a,b ∉ {x,y,z}, hence all the inequalities a≠x,a≠y,a≠z,b≠x,b≠y,b≠z.
      obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : E2, a ∈ pts ∧ b ∈ pts ∧ a ≠ b ∧ a ∉ E ∧ b ∉ E ∧ a ≠ x ∧ a ≠ y ∧ a ≠ z ∧ b ≠ x ∧ b ≠ y ∧ b ≠ z := by
        have h_compl : (pts \ {x, y, z}).card = 2 := by
          grind;
        obtain ⟨ a, ha, b, hb, hab ⟩ := Finset.one_lt_card.1 ( by linarith ) ; use a, b; aesop;
      apply hasConvexNGon_caseB pts hgen x y z a b hx hy hz ha hb;
      all_goals tauto;

end KleinUpperAristotle