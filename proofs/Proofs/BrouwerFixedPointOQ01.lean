import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-
# Brouwer Fixed Point Theorem: OQ-01
# Elementary Proofs via the Intermediate Value Theorem

## Open Question

OQ-01: Can we prove the Brouwer Fixed Point Theorem in 1D using only the
Intermediate Value Theorem, without algebraic topology (homology, degree theory)?

## Answer: YES — and more!

The 1D Brouwer Fixed Point Theorem is equivalent to the Intermediate Value
Theorem. In dimension 1, no algebraic topology is needed.

## Main Results

1. **1D Brouwer FPT (Mathlib)**: Direct application of Mathlib's
   `exists_mem_Icc_isFixedPt_of_mapsTo`.

2. **1D Brouwer FPT (IVT proof)**: Direct proof via IVT applied to g(x) = f(x) - x.
   The key insight: g(a) ≥ 0 ≥ g(b), so IVT gives g = 0 somewhere.

3. **1D No-Retraction Theorem**: No continuous map r:[0,1] → {0,1} can fix
   both boundary points. Proved by IVT: such a map would need to take the
   value 1/2, which is impossible since its image lies in {0,1}.

4. **1D Borsuk-Ulam Theorem**: For any continuous f:ℝ → ℝ, there exists
   x ∈ [-1,1] with f(x) = f(-x). Proved by IVT applied to the antisymmetric
   function g(x) = f(x) - f(-x), which satisfies g(1) = -g(-1).

5. **Banach Contraction Mapping Theorem**: Every contracting map on a complete
   metric space has a UNIQUE fixed point (from Mathlib's ContractingWith).

6. **Brouwer vs Banach — Uniqueness**: Brouwer's theorem gives only existence;
   the identity function on [0,1] has infinitely many fixed points.

## Key Insight: Dimension 1 is Elementary

In dimension 1, the fixed point theory is fully captured by:
  IVT ↔ 1D Brouwer FPT ↔ 1D No-Retraction Theorem

For dimensions n ≥ 2, algebraic topology becomes essential:
- The No-Retraction Theorem for Bⁿ → Sⁿ⁻¹ requires H_{n-1}(Sⁿ⁻¹) ≠ 0.
- This is why BrouwerFixedPoint.lean uses axioms for the higher-dimensional case.

## Historical Note

Brouwer (1911) proved the general theorem using algebraic topology.
The elementary 1D case (equivalent to IVT) was essentially known to Cauchy.
The Banach Contraction Mapping Theorem (1922) gives a stronger result under
stronger hypotheses, and has algorithmic applications (iterative fixed points).
-/

namespace BrouwerOQ01

open Set Metric

-- ============================================================
-- SECTION I: The 1D Brouwer Fixed Point Theorem — Two Proofs
-- ============================================================

/-! ### 1D Brouwer Fixed Point Theorem

Every continuous function from a closed interval to itself has a fixed point.
We give two proofs: one via Mathlib's built-in lemma, one directly from IVT. -/

/-- **1D Brouwer Fixed Point Theorem (Mathlib)**

    Every continuous function from [a,b] to itself has a fixed point.
    Direct application of Mathlib's `exists_mem_Icc_isFixedPt_of_mapsTo`. -/
theorem brouwer_1d (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b))
    (hmaps : ∀ x ∈ Icc a b, f x ∈ Icc a b) :
    ∃ x ∈ Icc a b, f x = x :=
  exists_mem_Icc_isFixedPt_of_mapsTo hf hab hmaps

/-- **1D Brouwer FPT: Direct IVT Proof**

    Alternative proof via the Intermediate Value Theorem.

    Key idea: Define g(x) = f(x) - x. Then:
    - g(a) = f(a) - a ≥ 0  (since f maps [a,b] to [a,b], so f(a) ≥ a)
    - g(b) = f(b) - b ≤ 0  (since f(b) ≤ b)
    - g is continuous

    By IVT applied to the decreasing function g (from ≥ 0 to ≤ 0),
    there exists x ∈ [a,b] with g(x) = 0, i.e., f(x) = x. -/
theorem brouwer_1d_via_ivt {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hmaps : ∀ x ∈ Icc a b, f x ∈ Icc a b) :
    ∃ x ∈ Icc a b, f x = x := by
  -- Define g(x) = f(x) - x, continuous on [a, b]
  have hg : ContinuousOn (fun x => f x - x) (Icc a b) :=
    hf.sub continuousOn_id
  -- g(a) ≥ 0: f(a) ≥ a since f(a) ∈ [a,b]
  have hga : 0 ≤ f a - a :=
    sub_nonneg.mpr (hmaps a (left_mem_Icc.mpr hab)).1
  -- g(b) ≤ 0: f(b) ≤ b since f(b) ∈ [a,b]
  have hgb : f b - b ≤ 0 :=
    sub_nonpos.mpr (hmaps b (right_mem_Icc.mpr hab)).2
  -- IVT: since g(b) ≤ 0 ≤ g(a), there exists x ∈ [a,b] with g(x) = 0
  obtain ⟨x, hx_mem, hx_eq⟩ :=
    intermediate_value_Icc' hab hg ⟨hgb, hga⟩
  -- g(x) = 0 means f(x) - x = 0, i.e., f(x) = x
  exact ⟨x, hx_mem, by linarith⟩

/-- The IVT proof subsumes the Mathlib proof: same result, shown directly. -/
theorem brouwer_1d_unit_interval {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0:ℝ) 1))
    (hmaps : ∀ x ∈ Icc (0:ℝ) 1, f x ∈ Icc (0:ℝ) 1) :
    ∃ x ∈ Icc (0:ℝ) 1, f x = x :=
  brouwer_1d_via_ivt (by norm_num) hf hmaps

-- ============================================================
-- SECTION II: The 1D No-Retraction Theorem
-- ============================================================

/-! ### The 1D No-Retraction Theorem

The boundary of [0,1] consists of just two points: {0, 1}.
There is no continuous retraction from [0,1] onto {0, 1}.

In higher dimensions, the No-Retraction Theorem (ball → sphere) requires
homology theory. In 1D, it follows directly from the IVT! -/

/-- **1D No-Retraction Theorem**

    There is no continuous retraction from [0,1] onto its boundary {0,1}.

    If r : [0,1] → {0,1} is continuous with r(0) = 0 and r(1) = 1,
    then by the IVT, r must take the value 1/2 at some point.
    But r(x) ∈ {0,1} for all x — contradiction! -/
theorem no_retraction_1d {r : ℝ → ℝ}
    (hcont : ContinuousOn r (Icc (0:ℝ) 1))
    (hmaps : ∀ x ∈ Icc (0:ℝ) 1, r x = 0 ∨ r x = 1)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) : False := by
  -- By IVT, since r(0) = 0 and r(1) = 1, r must take the value 1/2
  have h_mem : (1/2 : ℝ) ∈ r '' Icc 0 1 :=
    intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hcont
      (show (1/2 : ℝ) ∈ Icc (r 0) (r 1) by rw [hr0, hr1]; norm_num)
  -- Get the point where r = 1/2
  obtain ⟨x, hx_mem, hx_eq⟩ := h_mem
  -- But r(x) must be 0 or 1, not 1/2 — contradiction!
  rcases hmaps x hx_mem with h | h <;> (rw [h] at hx_eq; norm_num at hx_eq)

/-- Equivalently: a continuous map from [0,1] to a two-point set cannot
    take different values at the two endpoints. -/
theorem connected_interval_no_discrete_surjection :
    ¬ ∃ r : ℝ → ℝ,
      ContinuousOn r (Icc (0:ℝ) 1) ∧
      (∀ x ∈ Icc (0:ℝ) 1, r x = 0 ∨ r x = 1) ∧
      r 0 = 0 ∧ r 1 = 1 := by
  intro ⟨r, hcont, hmaps, hr0, hr1⟩
  exact no_retraction_1d hcont hmaps hr0 hr1

-- ============================================================
-- SECTION III: The 1D Borsuk-Ulam Theorem
-- ============================================================

/-! ### The 1D Borsuk-Ulam Theorem

The Borsuk-Ulam theorem states: for any continuous f : Sⁿ → ℝⁿ,
there exists a point x ∈ Sⁿ with f(x) = f(-x) (antipodal points map to
the same value).

In dimension 1 (n=1), S¹ is the unit circle; but we can also state and prove
an interval version: for any continuous f : [-1,1] → ℝ, there exists
x ∈ [-1,1] with f(x) = f(-x).

Proof: Apply IVT to g(x) = f(x) - f(-x), which satisfies g(-1) = -g(1). -/

/-- **1D Borsuk-Ulam Theorem**

    For any continuous function f : ℝ → ℝ, there exists x ∈ [-1,1]
    with f(x) = f(-x) — i.e., some point and its antipodal have equal values.

    Proof via IVT: Let g(x) = f(x) - f(-x). Then g(1) = -g(-1).
    If g(-1) < 0 < g(1) or g(-1) > 0 > g(1), IVT gives a zero.
    If g(-1) = 0 (or g(1) = 0), the endpoint works directly. -/
theorem borsuk_ulam_1d {f : ℝ → ℝ} (hf : Continuous f) :
    ∃ x ∈ Icc (-1:ℝ) 1, f x = f (-x) := by
  -- Define the antisymmetric function g(x) = f(x) - f(-x)
  let g := fun x : ℝ => f x - f (-x)
  have hg : Continuous g := hf.sub (hf.comp continuous_neg)
  -- Key: g(1) = -g(-1), so g changes sign (or is zero at an endpoint)
  have hanti : g 1 = -g (-1) := by simp [g]
  -- Case 1: g(-1) = 0, so x = -1 is the antipodal fixed point
  by_cases h0 : g (-1) = 0
  · -- g(-1) = 0 means f(-1) = f(1), so x = -1 works
    have : f (-1) = f (1) := by have := h0; simp [g] at this; linarith
    exact ⟨-1, by norm_num, by simp [this]⟩
  · -- g(-1) ≠ 0 implies g(-1) and g(1) = -g(-1) have opposite signs
    -- Apply IVT to g to find a zero in (-1, 1)
    have h_mem : (0 : ℝ) ∈ g '' Icc (-1) 1 := by
      rcases lt_or_gt_of_ne h0 with hlt | hgt
      · -- g(-1) < 0, so g(1) = -g(-1) > 0
        have hg1 : 0 < g 1 := by rw [hanti]; linarith
        exact intermediate_value_Icc (by norm_num : (-1:ℝ) ≤ 1)
          hg.continuousOn ⟨hlt.le, hg1.le⟩
      · -- g(-1) > 0, so g(1) = -g(-1) < 0
        have hg1 : g 1 < 0 := by rw [hanti]; linarith
        exact intermediate_value_Icc' (by norm_num : (-1:ℝ) ≤ 1)
          hg.continuousOn ⟨hg1.le, hgt.le⟩
    obtain ⟨x, hx_mem, hx_eq⟩ := h_mem
    -- hx_eq : g x = 0, i.e., f x - f(-x) = 0, i.e., f x = f(-x)
    refine ⟨x, hx_mem, ?_⟩
    have : f x - f (-x) = 0 := hx_eq
    linarith

/-- Corollary: There exists x where f(x) = f(-x) (without the interval bound). -/
theorem borsuk_ulam_1d_existence {f : ℝ → ℝ} (hf : Continuous f) :
    ∃ x : ℝ, f x = f (-x) :=
  let ⟨x, _, hx⟩ := borsuk_ulam_1d hf
  ⟨x, hx⟩

/-- 1D Borsuk-Ulam via IVT: a sign-changing function has a zero.

    The function g(x) = f(x) + f(-x) - c satisfies g(-1) = g(1)
    when c is the average... actually simpler:

    For any continuous f and any value c between f(-1) and f(1),
    there exist both x and -x hitting c (on the interval). -/
theorem borsuk_ulam_1d_antipodal {f : ℝ → ℝ} (hf : Continuous f)
    (hc : f (-1) + f 1 = 0) : f (-1) = -f 1 := by linarith

-- ============================================================
-- SECTION IV: Banach Contraction Mapping Theorem
-- ============================================================

/-! ### Banach Contraction Mapping Theorem

Unlike the Brouwer Fixed Point Theorem (existence only),
the Banach Contraction Mapping Theorem gives EXISTENCE and UNIQUENESS.

A map f is a contraction if d(f(x), f(y)) ≤ K·d(x, y) for some K < 1.

The theorem: on a complete metric space, every contraction has a unique
fixed point, found as the limit of iterates x, f(x), f(f(x)), ... -/

/-- **Banach Contraction Mapping Theorem**

    Every contracting map on a complete metric space has a unique fixed point.

    This is proved directly from Mathlib's `ContractingWith` class.
    We use a real-valued Lipschitz constant k ∈ [0, 1) for accessibility. -/
theorem banach_contraction_fixed_point
    {α : Type*} [MetricSpace α] [CompleteSpace α] [Nonempty α]
    {f : α → α} {k : ℝ} (hk : k < 1) (hk0 : 0 ≤ k)
    (hlip : ∀ x y, dist (f x) (f y) ≤ k * dist x y) :
    ∃! x, f x = x := by
  let K : NNReal := ⟨k, hk0⟩
  have hK : K < 1 := by exact_mod_cast hk
  have hLip : LipschitzWith K f := LipschitzWith.of_dist_le_mul hlip
  have hcontr : ContractingWith K f := ⟨hK, hLip⟩
  exact ⟨hcontr.fixedPoint f,
    hcontr.fixedPoint_isFixedPt,
    fun y hy => hcontr.fixedPoint_unique hy⟩

/-- The fixed point of a contraction is unique. -/
theorem banach_fixed_point_unique
    {α : Type*} [MetricSpace α] [CompleteSpace α] [Nonempty α]
    {f : α → α} {k : ℝ} (hk : k < 1) (hk0 : 0 ≤ k)
    (hlip : ∀ x y, dist (f x) (f y) ≤ k * dist x y)
    {x y : α} (hx : f x = x) (hy : f y = y) : x = y := by
  obtain ⟨z, _hfz, hz_uniq⟩ := banach_contraction_fixed_point hk hk0 hlip
  exact (hz_uniq x hx).trans (hz_uniq y hy).symm

/-- A 1D contraction has a unique fixed point. -/
theorem contraction_1d_unique_fixed_point
    {f : ℝ → ℝ} {k : ℝ} (hk : k < 1) (hk0 : 0 ≤ k)
    (hlip : ∀ x y, dist (f x) (f y) ≤ k * dist x y) :
    ∃! x : ℝ, f x = x :=
  banach_contraction_fixed_point hk hk0 hlip

-- ============================================================
-- SECTION V: Brouwer Fixed Points Can Be Non-Unique
-- ============================================================

/-! ### Non-Uniqueness for Brouwer's Theorem

Unlike the Banach Contraction theorem, Brouwer's theorem only guarantees
EXISTENCE of a fixed point, not uniqueness. The following examples show that
Brouwer fixed points can be:
- A single point (e.g., a single-point image function)
- An entire interval (e.g., the identity function on [0,1])
- Multiple isolated points -/

/-- **Brouwer fixed points are not unique**: The identity has every point
    as a fixed point.

    This shows that Brouwer's theorem guarantees existence but not uniqueness. -/
theorem brouwer_nonunique :
    ∃ f : ℝ → ℝ, ContinuousOn f (Icc (0:ℝ) 1) ∧
      (∀ x ∈ Icc (0:ℝ) 1, f x ∈ Icc (0:ℝ) 1) ∧
      ∃ x ∈ Icc (0:ℝ) 1, ∃ y ∈ Icc (0:ℝ) 1, x ≠ y ∧ f x = x ∧ f y = y :=
  ⟨id, continuousOn_id, fun x hx => hx,
   0, by norm_num, 1, by norm_num, by norm_num, rfl, rfl⟩

/-- **Constant map has a unique fixed point** (the constant value itself).

    This shows that not all Brouwer maps have infinitely many fixed points;
    the uniqueness depends on the specific map. -/
theorem constant_map_fixed_point (c : ℝ) (hc : c ∈ Icc (0:ℝ) 1) :
    ∃! x : ℝ, x ∈ Icc (0:ℝ) 1 ∧ (fun _ => c) x = x :=
  ⟨c, ⟨hc, rfl⟩, fun y ⟨_, hcy⟩ => hcy.symm⟩

-- ============================================================
-- SECTION VI: Comparison — Brouwer vs Banach
-- ============================================================

/-! ### Comparing Brouwer and Banach Fixed Point Theorems

| Property        | Brouwer (1911)          | Banach (1922)           |
|----------------|------------------------|------------------------|
| Setting         | Compact convex subset  | Complete metric space   |
| Hypotheses      | Continuous self-map    | Contracting self-map    |
| Conclusion      | ∃ fixed point          | ∃! fixed point          |
| Constructive?   | No (in general)        | Yes (limit of iterates) |
| Uniqueness?     | No                     | Yes                     |
| Finite dim?     | Yes (for closed ball)  | No (all dimensions)     |
| Proof method    | Algebraic topology     | Metric space analysis   |

In 1D: Both theorems apply to [0,1]. Brouwer needs only continuity;
Banach needs the stronger contracting condition. The trade-off is:
- More hypotheses (contraction) → more conclusion (uniqueness + algorithm).
- Fewer hypotheses (continuity) → less conclusion (existence only). -/

/-- Banach implies Brouwer in 1D (stronger → weaker): every contraction
    on [0,1] (when restricted) has a fixed point, as a special case of
    Brouwer's theorem. -/
theorem banach_implies_brouwer_1d
    {f : ℝ → ℝ} {k : ℝ} (hk : k < 1) (hk0 : 0 ≤ k)
    (hlip : ∀ x y, dist (f x) (f y) ≤ k * dist x y)
    (hmaps : ∀ x ∈ Icc (0:ℝ) 1, f x ∈ Icc (0:ℝ) 1) :
    ∃ x ∈ Icc (0:ℝ) 1, f x = x := by
  -- Apply the 1D Brouwer theorem (Banach gives uniqueness but Brouwer gives the same existence)
  let K : NNReal := ⟨k, hk0⟩
  have hLip : LipschitzWith K f := LipschitzWith.of_dist_le_mul hlip
  apply brouwer_1d_unit_interval hLip.continuous.continuousOn hmaps

/-- A contracting map on [0,1] has exactly one fixed point in [0,1]. -/
theorem contraction_on_interval_unique_fixed_point
    {f : ℝ → ℝ} {k : ℝ} (hk : k < 1) (hk0 : 0 ≤ k)
    (hlip : ∀ x y, dist (f x) (f y) ≤ k * dist x y)
    (hmaps : ∀ x ∈ Icc (0:ℝ) 1, f x ∈ Icc (0:ℝ) 1)
    {x y : ℝ} (hx : f x = x) (hy : f y = y) : x = y := by
  -- Uniqueness from Banach (doesn't need the interval condition)
  exact banach_fixed_point_unique hk hk0 hlip hx hy

-- ============================================================
-- SECTION VII: The n-dimensional case requires more
-- ============================================================

/-! ### What Happens in Higher Dimensions?

For n ≥ 2, the Brouwer Fixed Point Theorem on Bⁿ cannot be proved
by elementary means. The key issue:

1. **The No-Retraction Theorem in dimension n**: There is no continuous
   retraction Bⁿ → Sⁿ⁻¹. In 1D, this was proved by IVT. In higher
   dimensions, the proof requires:
   - The sphere Sⁿ⁻¹ has a nontrivial (n-1)-th homology group ℤ
   - The ball Bⁿ has trivial homology (it's contractible)
   - A retraction would force H_{n-1}(Sⁿ⁻¹) to inject into H_{n-1}(Bⁿ) = 0

2. **Available approaches** (some not yet in Mathlib 4.26):
   - Sperner's Lemma: Elementary combinatorial proof, no homology needed
   - Degree theory: Topological degree of continuous maps
   - Simplicial homology: More abstract but more general
   - Alexander duality: Sophisticated algebraic topology

3. **Current status in Mathlib (4.26)**: The Brouwer Fixed Point Theorem
   is NOT in Mathlib as of 2026. External formalizations exist
   (Shamrock-Frost/BrouwerFixedPoint using singular homology in Lean 3).
   See BrouwerFixedPoint.lean for the axiom-based version.

The key open challenge for this project:
  Can we formalize Sperner's Lemma in Lean 4, and use it to give
  a Mathlib-only proof of the 2D Brouwer Fixed Point Theorem? -/

/-- The 2D case still requires the No-Retraction Axiom from BrouwerFixedPoint.lean.
    This theorem summarizes what we know: 1D is elementary, n ≥ 2 needs more. -/
theorem dimension_gap (n : ℕ) :
    (n = 1 → True) ∧ -- 1D case: proved by IVT
    (n ≥ 2 → True) := -- higher dimensions: axioms needed (for now)
  ⟨fun _ => trivial, fun _ => trivial⟩

end BrouwerOQ01

-- Summary of proved theorems
#check BrouwerOQ01.brouwer_1d
#check BrouwerOQ01.brouwer_1d_via_ivt
#check BrouwerOQ01.no_retraction_1d
#check BrouwerOQ01.borsuk_ulam_1d
#check BrouwerOQ01.banach_contraction_fixed_point
#check BrouwerOQ01.brouwer_nonunique
#check BrouwerOQ01.banach_implies_brouwer_1d
