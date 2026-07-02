/-
  Erdős Problem #105, Open Question 01:
  Does the rich-line / obstacle property hold with n-4 obstacles?

  **Background**: For a non-collinear set A of n points and an obstacle set B,
  call B *avoidable* (for A) if some line through ≥2 points of A misses every
  point of B. Erdős & Purdy conjectured every B with |B| = n-3 is avoidable;
  Xichuan (2024) DISPROVED this with explicit counterexamples. Hickerson had
  earlier shown failure already at n-2 obstacles, and Beck / Szemerédi–Trotter
  (1983) proved avoidability whenever |B| ≤ c·n.

  This leaves a single boundary open (parent's `openProblem_n_minus_4`):

      Is every obstacle set of size n-4 avoidable?

  **What this entry contributes** — the *monotone structure* of the problem in
  the number of obstacles, which precisely locates the open boundary:

  1. **Avoidability is antitone** in the obstacle set: removing obstacles can
     only help (`avoidable_antitone`). Dually, **blocking is monotone**: adding
     obstacles can only preserve a fully-blocked configuration (`blocked_monotone`).
     These are axiom-free facts about the definitions.

  2. **Fresh-point padding** (`exists_disjoint_superset`): in the plane one can
     always enlarge a finite obstacle set to any larger cardinality while keeping
     it disjoint from A (the plane is infinite). Axiom-free.

  3. **Upward propagation of Xichuan's disproof** (`xichuan_blocks_at_all_counts`):
     because blocking is monotone and obstacle sets can be padded, the single
     n-3 counterexample forces a blocking configuration at *every* count m ≥ n-3.
     In particular this RE-DERIVES Hickerson's n-2 failure (`hickerson_n_minus_2`)
     as a corollary of the n-3 disproof. (Uses the parent's `xichuan_counterexample`.)

  4. **The open boundary is genuinely below the disproof**
     (`openProblem_n_minus_4_strong`, `n_minus_4_threshold_lower`): monotonicity
     propagates the disproof only *upward* (m ≥ n-3); it says nothing about
     n-4 < n-3. Conversely, IF the n-4 question is answered YES, then by
     antitonicity every count ≤ n-4 is avoidable, so the threshold f(n) ≥ n-4;
     combined with the known upper bound f(n) ≤ n-4 this would pin f(n) = n-4
     exactly. Thus oq-01 is precisely the question "is f(n) = n-4?".

  **Status**: OPEN (the n-4 question itself is unsolved). The structural results
  here are axiom-free; the upward-propagation corollaries use the parent's
  `xichuan_counterexample` axiom (Xichuan 2024, an established result).

  Reference: https://erdosproblems.com/105
  Axiom count: 1 (xichuan_counterexample, inherited from parent; used only in §III)
  Sorry count: 0
-/

import Proofs.Erdos105Problem
import Mathlib

open Erdos105

namespace Erdos105OQ01

-- ════════════════════════════════════════════════════════════════
-- SECTION I: Monotonicity of avoidability / blocking (axiom-free)
-- ════════════════════════════════════════════════════════════════

/-- Avoiding a larger obstacle set implies avoiding any smaller one:
    `unblocked` is antitone in the obstacle set. -/
theorem unblocked_antitone {L : Line} {B B' : Set Point} (hsub : B' ⊆ B)
    (h : L.unblocked B) : L.unblocked B' :=
  fun b hb => h b (hsub hb)

/-- A rich line avoiding `B` also avoids any subset `B' ⊆ B`. -/
theorem richAndUnblocked_antitone {L : Line} {A B B' : Set Point} (hsub : B' ⊆ B)
    (h : L.richAndUnblocked A B) : L.richAndUnblocked A B' :=
  ⟨h.1, unblocked_antitone hsub h.2⟩

/-- **Avoidability is antitone in the obstacle set.**
    If some rich line of `A` avoids `B`, then some rich line avoids every `B' ⊆ B`.
    (Fewer obstacles can only make avoidance easier.) -/
theorem avoidable_antitone {A B B' : Set Point} (hsub : B' ⊆ B)
    (h : ∃ L : Line, L.richAndUnblocked A B) :
    ∃ L : Line, L.richAndUnblocked A B' := by
  obtain ⟨L, hL⟩ := h
  exact ⟨L, richAndUnblocked_antitone hsub hL⟩

/-- **Blocking is monotone in the obstacle set.**
    If every rich line of `A` meets `B` (no rich line avoids `B`), then every rich
    line meets any superset `B' ⊇ B` as well. (More obstacles preserve a block.) -/
theorem blocked_monotone {A B B' : Set Point} (hsub : B ⊆ B')
    (h : ∀ L : Line, L.isRich A → ¬ L.unblocked B) :
    ∀ L : Line, L.isRich A → ¬ L.unblocked B' := by
  intro L hrich hub
  exact h L hrich (unblocked_antitone hsub hub)

-- ════════════════════════════════════════════════════════════════
-- SECTION II: Fresh-point padding in the plane (axiom-free)
-- ════════════════════════════════════════════════════════════════

/-- The plane `ℝ²` is infinite: the map `t ↦ (t, 0)` (via `EuclideanSpace.single`)
    is an injection from `ℝ`. -/
instance : Infinite Point :=
  Infinite.of_injective (fun a : ℝ => EuclideanSpace.single (0 : Fin 2) a) (fun a b h => by
    have hb : EuclideanSpace.single (0 : Fin 2) a = EuclideanSpace.single (0 : Fin 2) b := h
    have h0 : (EuclideanSpace.single (0 : Fin 2) a) 0
            = (EuclideanSpace.single (0 : Fin 2) b) 0 := by rw [hb]
    simpa [EuclideanSpace.single_apply] using h0)

/-- **Padding lemma.** Any finite obstacle set `B` disjoint from `A` can be enlarged
    to a superset of any prescribed (larger) cardinality `m`, still disjoint from `A`.
    Proof: repeatedly insert a fresh plane point outside `A ∪ B'`. -/
theorem exists_disjoint_superset (A B : Finset Point) (hdisj : Disjoint A B)
    (m : ℕ) (hm : B.card ≤ m) :
    ∃ B' : Finset Point, B ⊆ B' ∧ B'.card = m ∧ Disjoint A B' := by
  induction m, hm using Nat.le_induction with
  | base => exact ⟨B, Finset.Subset.refl B, rfl, hdisj⟩
  | succ k hk ih =>
    obtain ⟨B', hsub, hcard, hdisj'⟩ := ih
    obtain ⟨p, hp⟩ := Infinite.exists_notMem_finset (A ∪ B')
    rw [Finset.notMem_union] at hp
    obtain ⟨hpA, hpB'⟩ := hp
    refine ⟨insert p B', Finset.Subset.trans hsub (Finset.subset_insert p B'), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hpB', hcard]
    · rw [Finset.disjoint_insert_right]; exact ⟨hpA, hdisj'⟩

-- ════════════════════════════════════════════════════════════════
-- SECTION III: Upward propagation of Xichuan's disproof
--   (uses the parent axiom `xichuan_counterexample`)
-- ════════════════════════════════════════════════════════════════

/-- `BlocksAll A B`: every rich line of `A` meets the obstacle set `B`
    (no rich line of `A` avoids `B`). This is the "counterexample" predicate. -/
def BlocksAll (A B : Finset Point) : Prop :=
  ∀ L : Line, L.isRich (A : Set Point) → ¬ L.unblocked (B : Set Point)

/-- A blocking configuration extends to every larger obstacle count: pad `B` up to
    size `m` (still disjoint from `A`), and blocking is preserved by monotonicity. -/
theorem blocking_extends (A B : Finset Point) (hdisj : Disjoint A B)
    (hblock : BlocksAll A B) (m : ℕ) (hm : B.card ≤ m) :
    ∃ B' : Finset Point, B'.card = m ∧ Disjoint A B' ∧ BlocksAll A B' := by
  obtain ⟨B', hsub, hcard, hdisj'⟩ := exists_disjoint_superset A B hdisj m hm
  exact ⟨B', hcard, hdisj', blocked_monotone (Finset.coe_subset.mpr hsub) hblock⟩

/-- **Xichuan's n-3 disproof propagates to every count m ≥ n-3.**
    There is a non-collinear `A` with `|A| = n` such that for *every* `m ≥ n-3`
    some obstacle set of size `m` (disjoint from `A`) blocks all rich lines of `A`. -/
theorem xichuan_blocks_at_all_counts :
    ∃ (A : Finset Point) (n : ℕ), n ≥ 4 ∧ A.card = n ∧ NonCollinear (A : Set Point) ∧
      ∀ m : ℕ, n - 3 ≤ m →
        ∃ B : Finset Point, B.card = m ∧ Disjoint A B ∧ BlocksAll A B := by
  obtain ⟨A, B, n, hn, hA, hB, hdisj, hncoll, hblock⟩ := xichuan_counterexample
  refine ⟨A, n, hn, hA, hncoll, fun m hm => ?_⟩
  have hle : B.card ≤ m := by rw [hB]; exact hm
  exact blocking_extends A B hdisj hblock m hle

/-- **Hickerson's n-2 failure, re-derived.**
    The n-2 obstacle case also fails — but here it falls out *for free* as the
    `m = n-2` instance of `xichuan_blocks_at_all_counts`, i.e. as a corollary of
    Xichuan's n-3 disproof together with monotonicity. -/
theorem hickerson_n_minus_2 :
    ∃ (A B : Finset Point) (n : ℕ), n ≥ 4 ∧ A.card = n ∧ B.card = n - 2 ∧
      Disjoint A B ∧ NonCollinear (A : Set Point) ∧ BlocksAll A B := by
  obtain ⟨A, n, hn, hA, hncoll, hext⟩ := xichuan_blocks_at_all_counts
  obtain ⟨B, hcard, hdisj, hblock⟩ := hext (n - 2) (by omega)
  exact ⟨A, B, n, hn, hA, hcard, hdisj, hncoll, hblock⟩

-- ════════════════════════════════════════════════════════════════
-- SECTION IV: The open boundary lies strictly below the disproof
-- ════════════════════════════════════════════════════════════════

/-- **Antitone strengthening of oq-01.** If every obstacle set of size *exactly*
    `n-4` is avoidable (the open question), then so is every obstacle set of size
    `≤ n-4`: pad up to `n-4`, avoid the padded set, then restrict.
    Axiom-free (conditional on the open hypothesis). -/
theorem openProblem_n_minus_4_strong (h : openProblem_n_minus_4) :
    ∀ (A B : Finset Point) (n : ℕ), n ≥ 5 → A.card = n → B.card ≤ n - 4 →
      Disjoint A B → NonCollinear (A : Set Point) →
      ∃ L : Line, L.richAndUnblocked (A : Set Point) (B : Set Point) := by
  intro A B n hn hA hBcard hdisj hncoll
  obtain ⟨B', hsub, hcard, hdisj'⟩ := exists_disjoint_superset A B hdisj (n - 4) hBcard
  obtain ⟨L, hrich, hub⟩ := h A B' n hn hA hcard hdisj' hncoll
  exact ⟨L, hrich, unblocked_antitone (Finset.coe_subset.mpr hsub) hub⟩

/-- `n-4` belongs to the avoidability set defining the parent's `thresholdFunction n`,
    *provided* the open n-4 question holds. -/
theorem n_minus_4_avoidable_set (h : openProblem_n_minus_4) (n : ℕ) (hn : n ≥ 5) :
    (n - 4) ∈ {m : ℕ | ∀ (A B : Finset Point),
      A.card = n → B.card ≤ m → Disjoint A B → NonCollinear (A : Set Point) →
      ∃ L : Line, L.richAndUnblocked (A : Set Point) (B : Set Point)} := by
  intro A B hA hBcard hdisj hncoll
  exact openProblem_n_minus_4_strong h A B n hn hA hBcard hdisj hncoll

/-- **Conditional sharp lower bound** `f(n) ≥ n-4`.
    If the open n-4 question holds (and the avoidability set is bounded above — which
    the Xichuan disproof supplies for each fixed `n`), then the threshold function
    satisfies `f(n) ≥ n-4`. Together with the known upper bound `f(n) ≤ n-4`
    (Xichuan), this would pin `f(n) = n-4` exactly — so oq-01 is precisely the
    question "is f(n) = n-4?". -/
theorem n_minus_4_threshold_lower (h : openProblem_n_minus_4) (n : ℕ) (hn : n ≥ 5)
    (hbdd : BddAbove {m : ℕ | ∀ (A B : Finset Point),
      A.card = n → B.card ≤ m → Disjoint A B → NonCollinear (A : Set Point) →
      ∃ L : Line, L.richAndUnblocked (A : Set Point) (B : Set Point)}) :
    n - 4 ≤ thresholdFunction n := by
  unfold thresholdFunction
  exact le_csSup hbdd (n_minus_4_avoidable_set h n hn)

-- ════════════════════════════════════════════════════════════════
-- SECTION V: Line-through-two-points reduction (axiom-free)
--   The first concrete step toward *discharging* the parent's
--   `xichuan_counterexample` axiom: the blocking clause quantifies over
--   ALL lines `L`, but a rich line is determined (as a point set) by any
--   two distinct `A`-points it passes through. This reduces "∀ rich lines"
--   to the finite family of C(|A|,2) connecting lines — the reduction the
--   parent currently lacks. All of Section V is axiom-free.
-- ════════════════════════════════════════════════════════════════

/-- **A line is determined, as a point set, by any two distinct points on it.**
    If a line `L` passes through distinct points `p ≠ q`, then a third point `r`
    lies on `L` iff it lies on the affine line through `p` and `q`, i.e.
    `r = p + μ·(q - p)` for some scalar `μ`. This is the key uniqueness fact for
    lines over `ℝ²` (the `Line` structure is redundant — base point and a nonzero
    direction up to scaling — but its *containment relation* is rigid). -/
theorem contains_iff_of_contains_two {L : Line} {p q : Point}
    (hp : L.contains p) (hq : L.contains q) (hpq : p ≠ q) :
    ∀ r : Point, L.contains r ↔ ∃ μ : ℝ, r = p + μ • (q - p) := by
  obtain ⟨s, hs⟩ := hp
  obtain ⟨u, hu⟩ := hq
  -- The two parameters differ, else `p = q`.
  have hus : u ≠ s := by
    intro h; apply hpq; rw [hs, hu, h]
  have hc : u - s ≠ 0 := sub_ne_zero.mpr hus
  -- The chord `q - p` is a nonzero multiple of the direction.
  have hqp : q - p = (u - s) • L.direction := by
    rw [hs, hu, sub_smul]; abel
  intro r
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨(t - s) * (u - s)⁻¹, ?_⟩
    rw [hqp, ht, hs, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
    module
  · rintro ⟨μ, hμ⟩
    refine ⟨s + μ * (u - s), ?_⟩
    rw [hμ, hqp, hs, smul_smul]
    module

/-- **Two lines through the same pair of distinct points agree everywhere.**
    Immediate from `contains_iff_of_contains_two`: both containment relations
    reduce to the same affine parametrization by `p` and `q`. -/
theorem contains_congr_of_two {L₁ L₂ : Line} {p q : Point} (hpq : p ≠ q)
    (h1p : L₁.contains p) (h1q : L₁.contains q)
    (h2p : L₂.contains p) (h2q : L₂.contains q) :
    ∀ r : Point, L₁.contains r ↔ L₂.contains r := by
  intro r
  rw [contains_iff_of_contains_two h1p h1q hpq r,
      contains_iff_of_contains_two h2p h2q hpq r]

/-- The canonical `Line` through two distinct points `p ≠ q`, with base point `p`
    and direction `q - p` (nonzero because `p ≠ q`). -/
noncomputable def lineThrough (p q : Point) (h : p ≠ q) : Line where
  basePoint := p
  direction := q - p
  direction_nonzero := sub_ne_zero.mpr (Ne.symm h)

theorem lineThrough_contains_left (p q : Point) (h : p ≠ q) :
    (lineThrough p q h).contains p := by
  refine ⟨0, ?_⟩
  show p = p + (0 : ℝ) • (q - p)
  module

theorem lineThrough_contains_right (p q : Point) (h : p ≠ q) :
    (lineThrough p q h).contains q := by
  refine ⟨1, ?_⟩
  show q = p + (1 : ℝ) • (q - p)
  module

/-- Any line through distinct `p ≠ q` has exactly the same points as the canonical
    `lineThrough p q`. So the whole redundant `Line`-structure quotient collapses to
    one representative per pair of points. -/
theorem contains_eq_lineThrough {L : Line} {p q : Point} (hpq : p ≠ q)
    (hp : L.contains p) (hq : L.contains q) :
    ∀ r : Point, L.contains r ↔ (lineThrough p q hpq).contains r :=
  contains_congr_of_two hpq hp hq (lineThrough_contains_left p q hpq)
    (lineThrough_contains_right p q hpq)

/-- Being unblocked by `B` depends only on a line's point set: two lines through the
    same distinct pair `p ≠ q` are unblocked by exactly the same obstacle sets. -/
theorem unblocked_congr_of_two {L₁ L₂ : Line} {p q : Point} (hpq : p ≠ q)
    (h1p : L₁.contains p) (h1q : L₁.contains q)
    (h2p : L₂.contains p) (h2q : L₂.contains q) (B : Set Point) :
    L₁.unblocked B ↔ L₂.unblocked B := by
  constructor
  · intro h b hb hc
    exact h b hb ((contains_congr_of_two hpq h1p h1q h2p h2q b).mpr hc)
  · intro h b hb hc
    exact h b hb ((contains_congr_of_two hpq h1p h1q h2p h2q b).mp hc)

/-- **Blocking reduces to the connecting lines.**
    Every rich line of `A` meets `B` *iff* every line through two distinct points of
    `A` meets `B`. This replaces the quantifier over ALL lines (as in the parent's
    `xichuan_counterexample`) by a quantifier over the C(|A|,2) connecting lines —
    the concrete reduction a future discharge of the axiom needs. Axiom-free. -/
theorem blocksAll_iff_connecting (A B : Set Point) :
    (∀ L : Line, L.isRich A → ¬ L.unblocked B) ↔
      (∀ (p q : Point) (hpq : p ≠ q), p ∈ A → q ∈ A →
        ¬ (lineThrough p q hpq).unblocked B) := by
  constructor
  · intro h p q hpq hp hq
    exact h (lineThrough p q hpq)
      ⟨p, q, hp, hq, hpq, lineThrough_contains_left p q hpq,
        lineThrough_contains_right p q hpq⟩
  · intro h L hrich hub
    obtain ⟨p, q, hp, hq, hpq, hLp, hLq⟩ := hrich
    exact h p q hpq hp hq
      ((unblocked_congr_of_two hpq hLp hLq (lineThrough_contains_left p q hpq)
        (lineThrough_contains_right p q hpq) B).mp hub)

-- ════════════════════════════════════════════════════════════════
-- SECTION VI: Summary
-- ════════════════════════════════════════════════════════════════

/--
**Summary of Erdős #105, OQ-01.**

The single open boundary "is every obstacle set of size `n-4` avoidable?" is
sandwiched by monotonicity:

* **Upward** — Xichuan's n-3 disproof forces failure at every `m ≥ n-3`; in
  particular the n-2 (Hickerson) failure is a corollary (`hickerson_n_minus_2`).
* **Downward** — a positive answer at `n-4` would, by antitonicity, give
  avoidability at every count `≤ n-4` (`openProblem_n_minus_4_strong`), pinning
  the threshold at `f(n) = n-4`.

Monotonicity therefore localizes the entire remaining uncertainty to the single
value `m = n-4`. -/
theorem erdos_105_oq01_summary :
    (∃ (A B : Finset Point) (n : ℕ), n ≥ 4 ∧ A.card = n ∧ B.card = n - 2 ∧
      Disjoint A B ∧ NonCollinear (A : Set Point) ∧ BlocksAll A B) ∧
    (openProblem_n_minus_4 → ∀ (A B : Finset Point) (n : ℕ),
      n ≥ 5 → A.card = n → B.card ≤ n - 4 → Disjoint A B → NonCollinear (A : Set Point) →
      ∃ L : Line, L.richAndUnblocked (A : Set Point) (B : Set Point)) :=
  ⟨hickerson_n_minus_2, openProblem_n_minus_4_strong⟩

end Erdos105OQ01
