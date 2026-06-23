/-
# Erdős Problem 193: Collinear Points in Lattice Walks

Let `S ⊆ ℤ³` be a finite set and let `A = {a₁, a₂, …} ⊂ ℤ³` be an
infinite `S`-walk, meaning `aᵢ₊₁ − aᵢ ∈ S` for all `i`.
Must `A` contain three collinear points?

Originally posed by Gerver and Ramsey. Proved in `ℤ²`;
the three-dimensional case remains **OPEN**.

*Reference:* [erdosproblems.com/193](https://www.erdosproblems.com/193)
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/- ## Basic definitions -/

/-- A point in `ℤ^d` is represented as `Fin d → ℤ`. -/
abbrev LatPoint (d : ℕ) := Fin d → ℤ

/-- An infinite walk in `ℤ^d` is a sequence `ℕ → LatPoint d`. -/
abbrev Walk (d : ℕ) := ℕ → LatPoint d

/-- The step set: a finite subset of `ℤ^d`. -/
abbrev StepSet (d : ℕ) := Finset (LatPoint d)

/-- A walk is an `S`-walk if every consecutive step belongs to `S`. -/
def IsStepWalk {d : ℕ} (S : StepSet d) (w : Walk d) : Prop :=
    ∀ i : ℕ, (fun j => w (i + 1) j - w i j) ∈ S

/-- A walk visits distinct points (is injective). -/
def IsInjective {d : ℕ} (w : Walk d) : Prop :=
    Function.Injective w

/- ## Collinearity -/

/-- Three points `p, q, r` in `ℤ^d` are collinear if `q − p` and `r − p`
are parallel, i.e., there exist integers `a, b` (not both zero) such that
`a • (q − p) = b • (r − p)`. -/
def AreCollinear {d : ℕ} (p q r : LatPoint d) : Prop :=
    ∃ (a b : ℤ), (a ≠ 0 ∨ b ≠ 0) ∧
      ∀ j : Fin d, a * (q j - p j) = b * (r j - p j)

/-- A walk contains three collinear points if there exist distinct indices
whose images are collinear. -/
def HasThreeCollinear {d : ℕ} (w : Walk d) : Prop :=
    ∃ i j k : ℕ, i < j ∧ j < k ∧ AreCollinear (w i) (w j) (w k)

/- ## Main conjecture -/

/-- Erdős Problem 193: Every infinite injective `S`-walk in `ℤ³` contains
three collinear points. -/
def ErdosProblem193 : Prop :=
    ∀ (S : StepSet 3) (w : Walk 3),
      IsStepWalk S w → IsInjective w → HasThreeCollinear w

/- ## Known results -/

/-- In `ℤ²`, every infinite injective `S`-walk contains three collinear
points (Gerver–Ramsey). -/
axiom gerver_ramsey_2d :
    ∀ (S : StepSet 2) (w : Walk 2),
      IsStepWalk S w → IsInjective w → HasThreeCollinear w

/- ## Basic properties -/

/-- Collinearity is reflexive: any point is collinear with itself.
    Uses witnesses (0, 1): 0·(q-p) = 1·(p-p) = 0. -/
theorem collinear_refl {d : ℕ} (p q : LatPoint d) :
    AreCollinear p q p := by
  exact ⟨0, 1, Or.inr one_ne_zero, fun j => by ring⟩

/-- Collinearity is symmetric in the outer two points.
    Given a(q-p) = b(r-p), witnesses (a, a-b) satisfy a(q-r) = (a-b)(p-r). -/
theorem collinear_symm {d : ℕ} (p q r : LatPoint d) :
    AreCollinear p q r → AreCollinear r q p := by
  rintro ⟨a, b, hab, h⟩
  refine ⟨a, a - b, ?_, fun j => ?_⟩
  · -- a ≠ 0 ∨ a - b ≠ 0: if a = 0 then b ≠ 0 so a - b = -b ≠ 0
    rcases ne_or_eq a 0 with ha | rfl
    · exact Or.inl ha
    · exact Or.inr (by simpa using hab.resolve_left (not_not.mpr rfl))
  · -- a * (q j - r j) = (a - b) * (p j - r j) follows from a*(q_j-p_j) = b*(r_j-p_j)
    have := h j; linarith

/-- A constant walk (all points equal) trivially has collinear triples. -/
theorem collinear_const {d : ℕ} (v : LatPoint d) :
    AreCollinear v v v := collinear_refl v v

/-- Collinearity is preserved when swapping the first two arguments.
    Given a(q-p) = b(r-p), witnesses (b-a, b) satisfy (b-a)(p-q) = b(r-q). -/
theorem collinear_perm12 {d : ℕ} (p q r : LatPoint d) :
    AreCollinear p q r → AreCollinear q p r := by
  rintro ⟨a, b, hab, h⟩
  refine ⟨b - a, b, ?_, fun j => ?_⟩
  · by_contra hc
    push_neg at hc
    have ha : a = 0 := by omega
    have hb : b = 0 := hc.2
    exact hab.elim (fun h => h ha) (fun h => h hb)
  · have := h j; linarith

/- ## Dimension 1: trivial collinearity -/

/-- In dimension 1, every triple of lattice points is collinear
    (all points lie on a single line). -/
theorem collinear_dim1 (p q r : LatPoint 1) : AreCollinear p q r := by
  by_cases hqp : q ⟨0, by omega⟩ = p ⟨0, by omega⟩
  · have : q = p := by ext x; fin_cases x; exact hqp
    subst this; exact collinear_refl p r
  · exact ⟨r ⟨0, by omega⟩ - p ⟨0, by omega⟩, q ⟨0, by omega⟩ - p ⟨0, by omega⟩,
      Or.inr (sub_ne_zero.mpr hqp), fun j => by fin_cases j; ring⟩

/-- The collinearity conjecture holds trivially in dimension 1:
    every walk contains three collinear points. -/
theorem erdos193_dim1 :
    ∀ (S : StepSet 1) (w : Walk 1),
      IsStepWalk S w → IsInjective w → HasThreeCollinear w := by
  intro S w _ _
  exact ⟨0, 1, 2, by omega, by omega, collinear_dim1 (w 0) (w 1) (w 2)⟩

/- ## Singleton step sets -/

/-- In a walk with singleton step set {v}, position at step n satisfies
    w(n)(j) = w(0)(j) + n * v(j) for each coordinate j. -/
theorem singleton_walk_pos {d : ℕ} (v : LatPoint d) (w : Walk d)
    (hw : IsStepWalk ({v} : StepSet d) w) (n : ℕ) (j : Fin d) :
    w n j = w 0 j + ↑n * v j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have step := hw n
    simp only [Finset.mem_singleton] at step
    have hcoord : w (n + 1) j - w n j = v j := congr_fun step j
    rw [show w (n + 1) j = w n j + v j from by linarith, ih]
    push_cast; ring

/-- Any three points of a singleton-step walk are collinear, since
    all visited points lie on a line through w(0) in direction v. -/
theorem singleton_step_collinear {d : ℕ} (v : LatPoint d) (w : Walk d)
    (hw : IsStepWalk ({v} : StepSet d) w) (i j k : ℕ) (hij : i < j) :
    AreCollinear (w i) (w j) (w k) := by
  have hij' : (↑i : ℤ) < ↑j := Nat.cast_lt.mpr hij
  refine ⟨↑k - ↑i, ↑j - ↑i, Or.inr (by omega), fun c => ?_⟩
  have hi := singleton_walk_pos v w hw i c
  have hj := singleton_walk_pos v w hw j c
  have hk := singleton_walk_pos v w hw k c
  have diffj : w j c - w i c = (↑j - ↑i) * v c := by linarith
  have diffk : w k c - w i c = (↑k - ↑i) * v c := by linarith
  rw [diffj, diffk]; ring

/-- Every walk with a singleton step set has three collinear points
    (injectivity is not required). -/
theorem erdos193_singleton {d : ℕ} (v : LatPoint d) (w : Walk d)
    (hw : IsStepWalk ({v} : StepSet d) w) : HasThreeCollinear w :=
  ⟨0, 1, 2, by omega, by omega, singleton_step_collinear v w hw 0 1 2 (by omega)⟩

/- ## Parallel step sets -/

/-- A step set is parallel if all steps are integer multiples of a single
    direction vector `v`. -/
def IsParallelStepSet {d : ℕ} (S : StepSet d) (v : LatPoint d) : Prop :=
    ∀ s ∈ S, ∃ c : ℤ, ∀ j : Fin d, s j = c * v j

/-- In a parallel-step walk, position at step n satisfies
    w(n)(j) = w(0)(j) + c * v(j) for some integer c (the accumulated coefficient).
    All visited points lie on the line through w(0) in direction v. -/
theorem parallel_walk_on_line {d : ℕ} (S : StepSet d) (v : LatPoint d)
    (w : Walk d) (hS : IsParallelStepSet S v) (hw : IsStepWalk S w)
    (n : ℕ) : ∃ c : ℤ, ∀ j : Fin d, w n j = w 0 j + c * v j := by
  induction n with
  | zero => exact ⟨0, fun j => by simp⟩
  | succ n ih =>
    obtain ⟨cn, hcn⟩ := ih
    obtain ⟨cs, hcs⟩ := hS _ (hw n)
    refine ⟨cn + cs, fun j => ?_⟩
    have hstep : w (n + 1) j - w n j = cs * v j := hcs j
    have := hcn j
    linarith [hstep]

/-- Three points on a line through the origin (with coefficients cᵢ, cⱼ, cₖ)
    are collinear, provided the first two are distinct (cᵢ ≠ cⱼ). -/
private theorem line_points_collinear {d : ℕ} (o v : LatPoint d)
    (ci cj ck : ℤ) (hne : cj ≠ ci)
    (pi pj pk : LatPoint d)
    (hi : ∀ c, pi c = o c + ci * v c)
    (hj : ∀ c, pj c = o c + cj * v c)
    (hk : ∀ c, pk c = o c + ck * v c) :
    AreCollinear pi pj pk := by
  refine ⟨ck - ci, cj - ci, Or.inr (sub_ne_zero.mpr hne), fun c => ?_⟩
  have := hi c; have := hj c; have := hk c
  linarith [mul_comm (ck - ci) (v c), mul_comm (cj - ci) (v c)]

/-- Any three points of a parallel-step walk are collinear, provided the
    walk visits at least two distinct points among them. -/
theorem parallel_step_collinear {d : ℕ} (S : StepSet d) (v : LatPoint d)
    (w : Walk d) (hS : IsParallelStepSet S v) (hw : IsStepWalk S w)
    (i j k : ℕ) (hne : w i ≠ w j) : AreCollinear (w i) (w j) (w k) := by
  obtain ⟨ci, hci⟩ := parallel_walk_on_line S v w hS hw i
  obtain ⟨cj, hcj⟩ := parallel_walk_on_line S v w hS hw j
  obtain ⟨ck, hck⟩ := parallel_walk_on_line S v w hS hw k
  have hcij : cj ≠ ci := by
    intro heq; apply hne; ext c; have := hci c; have := hcj c; linarith
  exact line_points_collinear (w 0) v ci cj ck hcij (w i) (w j) (w k) hci hcj hck

/-- Every parallel-step walk has three collinear points. -/
theorem erdos193_parallel {d : ℕ} (S : StepSet d) (v : LatPoint d) (w : Walk d)
    (hS : IsParallelStepSet S v) (hw : IsStepWalk S w) :
    HasThreeCollinear w := by
  by_cases h01 : w 0 = w 1
  · -- If w(0) = w(1), they are equal, so (w 0, w 1, w 2) is trivially collinear
    exact ⟨0, 1, 2, by omega, by omega, by subst h01; exact collinear_refl (w 0) (w 2)⟩
  · exact ⟨0, 1, 2, by omega, by omega,
      parallel_step_collinear S v w hS hw 0 1 2 h01⟩

/- ## Collinearity under translation -/

/-- Collinearity is invariant under translation: the differences q-p, r-p
    are unchanged by adding a constant vector to all three points. -/
theorem collinear_translate {d : ℕ} (p q r v : LatPoint d) :
    AreCollinear p q r →
    AreCollinear (fun j => p j + v j) (fun j => q j + v j) (fun j => r j + v j) := by
  rintro ⟨a, b, hab, h⟩
  exact ⟨a, b, hab, fun j => by dsimp; linarith [h j]⟩

/- ## 2D-span position formula -/

/-- In a walk with a 2D-spanning step set, position at step n satisfies
    w(n)(j) = w(0)(j) + a * v₁(j) + b * v₂(j) for some integers a, b. -/
theorem walk_in_2d_span {d : ℕ} (S : StepSet d) (v₁ v₂ : LatPoint d)
    (hS : ∀ s ∈ S, ∃ (a b : ℤ), ∀ j : Fin d, s j = a * v₁ j + b * v₂ j)
    (w : Walk d) (hw : IsStepWalk S w)
    (n : ℕ) : ∃ (a b : ℤ), ∀ j : Fin d, w n j = w 0 j + a * v₁ j + b * v₂ j := by
  induction n with
  | zero => exact ⟨0, 0, fun j => by simp⟩
  | succ n ih =>
    obtain ⟨an, bn, hn⟩ := ih
    obtain ⟨as, bs, hs⟩ := hS _ (hw n)
    refine ⟨an + as, bn + bs, fun j => ?_⟩
    have hstep : w (n + 1) j - w n j = as * v₁ j + bs * v₂ j := hs j
    have := hn j; linarith [hstep]

/-- Collinearity lifts from 2D coordinates to the ambient space:
    if three points have representations o + aᵢv₁ + bᵢv₂ and the
    2D coordinates (aᵢ,bᵢ) are collinear, then the points are collinear. -/
theorem collinear_from_2d_coords {d : ℕ} (o v₁ v₂ : LatPoint d)
    (a₁ b₁ a₂ b₂ a₃ b₃ : ℤ)
    (α β : ℤ) (hαβ : α ≠ 0 ∨ β ≠ 0)
    (hca : α * (a₂ - a₁) = β * (a₃ - a₁))
    (hcb : α * (b₂ - b₁) = β * (b₃ - b₁))
    (p₁ p₂ p₃ : LatPoint d)
    (h₁ : ∀ j, p₁ j = o j + a₁ * v₁ j + b₁ * v₂ j)
    (h₂ : ∀ j, p₂ j = o j + a₂ * v₁ j + b₂ * v₂ j)
    (h₃ : ∀ j, p₃ j = o j + a₃ * v₁ j + b₃ * v₂ j) :
    AreCollinear p₁ p₂ p₃ := by
  refine ⟨α, β, hαβ, fun j => ?_⟩
  have d12 : p₂ j - p₁ j = (a₂ - a₁) * v₁ j + (b₂ - b₁) * v₂ j := by
    have := h₁ j; have := h₂ j; linarith
  have d13 : p₃ j - p₁ j = (a₃ - a₁) * v₁ j + (b₃ - b₁) * v₂ j := by
    have := h₁ j; have := h₃ j; linarith
  rw [d12, d13]
  linear_combination v₁ j * hca + v₂ j * hcb

/- ## Dimension reduction framework -/

/-- The step set spans at most a 2D subspace: every step vector is an
    integer linear combination of two fixed vectors v₁, v₂. -/
def SpansAtMost2D {d : ℕ} (S : StepSet d) : Prop :=
    ∃ (v₁ v₂ : LatPoint d), ∀ s ∈ S,
      ∃ (a b : ℤ), ∀ j : Fin d, s j = a * v₁ j + b * v₂ j

/-- Accumulated 2D coordinates along a walk in a 2D-spanning step set.
    Defined recursively by adding step-vector coordinates at each step. -/
private noncomputable def accumCoords
    {S : StepSet 3} {w : Walk 3} {v₁ v₂ : LatPoint 3}
    (hspan : ∀ s ∈ S, ∃ (a b : ℤ), ∀ j : Fin 3, s j = a * v₁ j + b * v₂ j)
    (hw : IsStepWalk S w) : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | n + 1 =>
    let prev := accumCoords hspan hw n
    (prev.1 + (hspan _ (hw n)).choose,
     prev.2 + (hspan _ (hw n)).choose_spec.choose)

/-- The accumulated coordinates faithfully represent the walk position:
    w(n)(j) = w(0)(j) + coordA(n) · v₁(j) + coordB(n) · v₂(j). -/
private theorem accumCoords_repr
    {S : StepSet 3} {w : Walk 3} {v₁ v₂ : LatPoint 3}
    (hspan : ∀ s ∈ S, ∃ (a b : ℤ), ∀ j : Fin 3, s j = a * v₁ j + b * v₂ j)
    (hw : IsStepWalk S w) (n : ℕ) (j : Fin 3) :
    w n j = w 0 j + (accumCoords hspan hw n).1 * v₁ j +
      (accumCoords hspan hw n).2 * v₂ j := by
  induction n with
  | zero => simp [accumCoords]
  | succ n ih =>
    have hs := (hspan _ (hw n)).choose_spec.choose_spec j
    have h1 : (accumCoords hspan hw (n + 1)).1 =
        (accumCoords hspan hw n).1 + (hspan _ (hw n)).choose := rfl
    have h2 : (accumCoords hspan hw (n + 1)).2 =
        (accumCoords hspan hw n).2 + (hspan _ (hw n)).choose_spec.choose := rfl
    linarith

/-- When the step set spans at most a 2D subspace, the conjecture holds
    by reduction to the 2D case (Gerver-Ramsey).

    Proof: project the walk onto ℤ² via accumulated step coordinates.
    The projection is an S'-walk (for a finite projected step set) and
    injective. Apply gerver_ramsey_2d, then lift collinearity back
    using collinear_from_2d_coords. -/
theorem erdos193_rank_le_2 :
    ∀ (S : StepSet 3) (w : Walk 3),
      SpansAtMost2D S →
      IsStepWalk S w → IsInjective w → HasThreeCollinear w := by
  intro S w ⟨v₁, v₂, hspan⟩ hw hinj
  -- Accumulated 2D coordinates along the walk
  set coords := accumCoords hspan hw with hcoords_def
  -- Projected walk in ℤ²
  let w' : Walk 2 := fun n (j : Fin 2) =>
    if j = 0 then (coords n).1 else (coords n).2
  -- Project each 3D step vector to its 2D coordinates
  let projS : LatPoint 3 → LatPoint 2 := fun s =>
    if hs : s ∈ S then
      fun (j : Fin 2) =>
        if j = 0 then (hspan s hs).choose else (hspan s hs).choose_spec.choose
    else 0
  let S' : StepSet 2 := S.image projS
  -- (1) w' is an S'-walk
  have hw' : IsStepWalk S' w' := by
    intro n
    suffices h : (fun j : Fin 2 => w' (n + 1) j - w' n j) =
        projS (fun k => w (n + 1) k - w n k) by
      rw [h]; exact Finset.mem_image_of_mem projS (hw n)
    ext ⟨j, hj⟩; interval_cases j
    · -- j = 0: difference of first coordinates = step's first coordinate
      show (coords (n + 1)).1 - (coords n).1 =
        (if hs : _ ∈ S then fun j : Fin 2 => if j = 0 then _ else _ else 0)
          ⟨0, by omega⟩
      simp only [dif_pos (hw n)]
      rfl
    · -- j = 1: difference of second coordinates = step's second coordinate
      show (coords (n + 1)).2 - (coords n).2 =
        (if hs : _ ∈ S then fun j : Fin 2 => if j = 0 then _ else _ else 0)
          ⟨1, by omega⟩
      simp only [dif_pos (hw n), show (⟨1, by omega⟩ : Fin 2) ≠ 0 from by decide, if_false]
      rfl
  -- (2) w' is injective (from injectivity of w and the representation)
  have hinj' : IsInjective w' := by
    intro i j (hij : w' i = w' j)
    apply hinj; ext c
    have hA : (coords i).1 = (coords j).1 := by
      have := congr_fun hij (⟨0, by omega⟩ : Fin 2); simp only [w', ite_true] at this; exact this
    have hB : (coords i).2 = (coords j).2 := by
      have := congr_fun hij (⟨1, by omega⟩ : Fin 2)
      simp only [w', show (⟨1, by omega⟩ : Fin 2) ≠ 0 from by decide, ite_false] at this
      exact this
    linarith [accumCoords_repr hspan hw i c, accumCoords_repr hspan hw j c]
  -- (3) Apply Gerver-Ramsey to the projected walk in ℤ²
  obtain ⟨i, j, k, hij, hjk, α, β, hαβ, hcol⟩ := gerver_ramsey_2d S' w' hw' hinj'
  -- (4) Lift 2D collinearity back to ℤ³ via the coordinate representation
  exact ⟨i, j, k, hij, hjk,
    collinear_from_2d_coords (w 0) v₁ v₂
      (coords i).1 (coords i).2
      (coords j).1 (coords j).2
      (coords k).1 (coords k).2
      α β hαβ
      (by have := hcol ⟨0, by omega⟩; simp only [w', ite_true] at this; linarith)
      (by have := hcol ⟨1, by omega⟩
          simp only [w', show (⟨1, by omega⟩ : Fin 2) ≠ 0 from by decide, ite_false] at this
          linarith)
      (w i) (w j) (w k)
      (accumCoords_repr hspan hw i)
      (accumCoords_repr hspan hw j)
      (accumCoords_repr hspan hw k)⟩

/-- The conjecture reduces to the full-rank case: step sets that span
    all of ℤ³. This is the genuinely 3-dimensional case that remains open.

    Proof: either S spans ≤ 2D (apply erdos193_rank_le_2) or S spans
    3D (the hypothesis gives the result). -/
theorem erdos193_reduces_to_full_rank :
    (∀ (S : StepSet 3) (w : Walk 3),
      ¬SpansAtMost2D S →
      IsStepWalk S w → IsInjective w → HasThreeCollinear w) →
    ErdosProblem193 := by
  intro h_full_rank S w hw hinj
  by_cases h : SpansAtMost2D S
  · exact erdos193_rank_le_2 S w h hw hinj
  · exact h_full_rank S w h hw hinj

/- ## Summary of proved special cases -/

/-
The conjecture ErdosProblem193 (for ℤ³) has been proved in these cases:
1. d = 1: trivially, all triples in ℤ¹ are collinear (erdos193_dim1)
2. Singleton step sets: the walk is a line (erdos193_singleton)
3. Parallel step sets: all steps ∈ ℤ·v, walk lies on a line (erdos193_parallel)
4. Rank ≤ 2 step sets: walk in 2D subspace → project to ℤ² + Gerver-Ramsey (erdos193_rank_le_2, proved)

The open case: step sets spanning all of ℤ³ (full rank 3).
By erdos193_reduces_to_full_rank, this is the only remaining case.
The only axiom is gerver_ramsey_2d (the published Gerver-Ramsey theorem for ℤ²).
-/
