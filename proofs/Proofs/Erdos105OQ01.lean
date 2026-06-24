/-
  Erdős Problem #105, Open Question 01:
  Does the Erdős–Purdy rich-line property hold with `n - 4` obstacles?

  **Background.** Let `A ⊂ ℝ²` be `n` non-collinear points and `B ⊂ ℝ²` a
  disjoint set of "obstacles". Say a line is *rich and unblocked* if it passes
  through ≥ 2 points of `A` and through no point of `B`. Erdős–Purdy (1995)
  conjectured that `n - 3` obstacles can never block every rich line; Xichuan
  (2024) disproved this with explicit counterexamples (`erdos_105_disproved` in
  `Erdos105Problem.lean`). Hickerson had already shown `n - 2` fails, and
  Beck / Szemerédi–Trotter (1983) show `c·n` obstacles always leave a rich line.

  **The open question (OQ-01).** Does the property survive with one *fewer*
  obstacle, i.e. with `n - 4` obstacles? The parent file states this as
  `Erdos105.openProblem_n_minus_4`. It is **OPEN**.

  **What this file does — and does not — do.** It does NOT resolve OQ-01. It
  supplies the axiom-free *structural* fact that makes the question precise: the
  rich-unblocked property is **antitone in the number of obstacles** (more
  obstacles is strictly harder). From this single reduction:

    * A *positive* answer to OQ-01 forces rich lines to survive *every* obstacle
      count `m ≤ n - 4` (`n_minus_4_extends_down`); together with Xichuan's
      `n - 3` failure this would pin the threshold `f(n)` exactly at `n - 4`.
    * A *negative* answer to OQ-01 (some `n - 4` counterexample) would manufacture
      a fresh `n - 3` counterexample (`not_richAvoids_succ_of_not`), i.e. it would
      be strictly stronger than Xichuan's disproof.

  Every theorem below is proved from first principles with **no axioms and no
  sorries** (`#print axioms erdos_105_oq01_summary` reports only the standard
  `propext, Classical.choice, Quot.sound`). The only ingredient beyond the
  geometric definitions is that the plane is infinite, so a finite configuration
  always leaves room for one more obstacle.

  **Self-containedness.** The geometric definitions (`Point`, `Line`, rich /
  unblocked lines, `NonCollinear`, `openProblem_n_minus_4`) are reproduced
  *verbatim* from `Erdos105Problem.lean` so that this file depends only on
  `Mathlib`. They are restated, not re-derived; the mathematical content of
  this entry is entirely the monotonicity reduction in Sections II–IV.

  Reference: https://erdosproblems.com/105
  Status: OPEN (OQ-01 unresolved); this file = verified monotonicity reduction.
  Axiom count: 0   Sorry count: 0
-/

import Mathlib

namespace Erdos105OQ01

-- ════════════════════════════════════════════════════════════════
-- SECTION 0: Geometric framework (reproduced from Erdos105Problem.lean)
-- ════════════════════════════════════════════════════════════════

/-- A point in the plane ℝ². -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- A line in the plane, given by a base point and a nonzero direction. -/
structure Line where
  basePoint : Point
  direction : Point
  direction_nonzero : direction ≠ 0

/-- A point lies on a line if it is `base + t • direction` for some `t`. -/
def Line.contains (L : Line) (p : Point) : Prop :=
  ∃ t : ℝ, p = L.basePoint + t • L.direction

/-- A line is *rich* for `A` if it passes through ≥ 2 distinct points of `A`. -/
def Line.isRich (L : Line) (A : Set Point) : Prop :=
  ∃ p q : Point, p ∈ A ∧ q ∈ A ∧ p ≠ q ∧ L.contains p ∧ L.contains q

/-- A line is *unblocked* by `B` if it contains no point of `B`. -/
def Line.unblocked (L : Line) (B : Set Point) : Prop :=
  ∀ b ∈ B, ¬L.contains b

/-- Rich for `A` and unblocked by `B`. -/
def Line.richAndUnblocked (L : Line) (A B : Set Point) : Prop :=
  L.isRich A ∧ L.unblocked B

/-- `A` is non-collinear if no single line contains all of it. -/
def NonCollinear (A : Set Point) : Prop :=
  ∀ L : Line, ∃ p ∈ A, ¬L.contains p

/-- **OQ-01** (the open problem, exactly as in `Erdos105Problem.lean`): does the
    rich-unblocked property hold with `n - 4` obstacles? -/
def openProblem_n_minus_4 : Prop :=
  ∀ (A B : Finset Point) (n : ℕ),
    n ≥ 5 →
    A.card = n →
    B.card = n - 4 →
    Disjoint A B →
    NonCollinear (A : Set Point) →
    ∃ L : Line, L.richAndUnblocked (A : Set Point) (B : Set Point)

-- ════════════════════════════════════════════════════════════════
-- SECTION I: The plane has room for one more obstacle
-- ════════════════════════════════════════════════════════════════

/-- The plane `ℝ²` is infinite: the constant map `r ↦ (r, r)` injects `ℝ`. -/
private lemma point_infinite : Infinite Point :=
  Infinite.of_injective
    (fun r : ℝ => (WithLp.equiv 2 (Fin 2 → ℝ)).symm (fun _ => r))
    (by
      intro a b hab
      have h : (fun _ : Fin 2 => a) = (fun _ : Fin 2 => b) :=
        (WithLp.equiv 2 (Fin 2 → ℝ)).symm.injective hab
      simpa using congrFun h 0)

/-- Any finite set of points misses some point of the plane: there is always
    room to place one more obstacle disjoint from a finite configuration. -/
lemma exists_point_not_mem (S : Finset Point) : ∃ p : Point, p ∉ S := by
  haveI := point_infinite
  exact Infinite.exists_not_mem_finset S

-- ════════════════════════════════════════════════════════════════
-- SECTION II: The obstacle-count predicate
-- ════════════════════════════════════════════════════════════════

/-- `RichAvoids n m` : for every non-collinear set `A` of size `n` and every
    disjoint obstacle set `B` of size *exactly* `m`, some line through ≥ 2 points
    of `A` avoids all of `B`. This is the per-`(n,m)` form of the Erdős–Purdy
    property; OQ-01 asks whether `RichAvoids n (n-4)` holds for all `n ≥ 5`. -/
def RichAvoids (n m : ℕ) : Prop :=
  ∀ (A B : Finset Point), A.card = n → B.card = m → Disjoint A B →
    NonCollinear (A : Set Point) →
    ∃ L : Line, L.richAndUnblocked (A : Set Point) (B : Set Point)

-- ════════════════════════════════════════════════════════════════
-- SECTION III: Monotonicity in the obstacle count (the reduction)
-- ════════════════════════════════════════════════════════════════

/-- **Single-step monotonicity.** If the property holds against `m + 1`
    obstacles then it holds against `m` obstacles: pad the smaller obstacle set
    with one extra point of the (infinite) plane, solve the harder instance, and
    the rich line returned avoids the original obstacles a fortiori.

    Adding obstacles can only make blocking *easier*, so surviving `m + 1`
    obstacles is the strictly stronger hypothesis. -/
theorem richAvoids_step {n m : ℕ} (h : RichAvoids n (m + 1)) : RichAvoids n m := by
  intro A B hA hB hdisj hncoll
  -- Pick an extra obstacle point outside `A ∪ B`.
  obtain ⟨c, hc⟩ := exists_point_not_mem (A ∪ B)
  rw [Finset.not_mem_union] at hc
  obtain ⟨hcA, hcB⟩ := hc
  -- Pad `B` to size `m + 1`.
  set B' := insert c B with hB'def
  have hB'card : B'.card = m + 1 := by
    rw [hB'def, Finset.card_insert_of_not_mem hcB, hB]
  have hdisj' : Disjoint A B' := by
    rw [hB'def, Finset.disjoint_insert_right]
    exact ⟨hcA, hdisj⟩
  -- Solve the harder (m+1)-obstacle instance.
  obtain ⟨L, hrich, hunb'⟩ := h A B' hA hB'card hdisj' hncoll
  -- The same line avoids the smaller obstacle set `B ⊆ B'`.
  refine ⟨L, hrich, ?_⟩
  intro b hb
  exact hunb' b (by
    rw [hB'def]
    exact Finset.mem_insert_of_mem (Finset.mem_coe.mp hb) |> Finset.mem_coe.mpr)

/-- **Antitone in the obstacle count.** Surviving `m₂` obstacles implies surviving
    any smaller number `m₁ ≤ m₂`. Iterates `richAvoids_step`. -/
theorem richAvoids_antitone {n m₁ m₂ : ℕ} (hle : m₁ ≤ m₂) (h : RichAvoids n m₂) :
    RichAvoids n m₁ := by
  induction m₂, hle using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact ih (richAvoids_step h)

/-- **Upward propagation of failure** (contrapositive of `richAvoids_step`). A
    counterexample at `m` obstacles yields a counterexample at `m + 1` obstacles.
    So if OQ-01 fails (some `n - 4` counterexample), one obtains a fresh `n - 3`
    counterexample — strictly stronger than Xichuan's `n - 3` disproof. -/
theorem not_richAvoids_succ_of_not {n m : ℕ} (h : ¬ RichAvoids n m) :
    ¬ RichAvoids n (m + 1) :=
  fun hh => h (richAvoids_step hh)

-- ════════════════════════════════════════════════════════════════
-- SECTION IV: Locating OQ-01 against Xichuan's disproof
-- ════════════════════════════════════════════════════════════════

/-- OQ-01 is exactly `RichAvoids n (n-4)` for all `n ≥ 5` (a reordering of the
    quantifiers in `openProblem_n_minus_4`). -/
theorem openProblem_n_minus_4_iff :
    openProblem_n_minus_4 ↔ ∀ n : ℕ, 5 ≤ n → RichAvoids n (n - 4) := by
  constructor
  · intro h n hn A B hA hB hd hnc
    exact h A B n hn hA hB hd hnc
  · intro h A B n hn hA hB hd hnc
    exact h n hn A B hA hB hd hnc

/-- **A positive answer to OQ-01 propagates downward.** If the property holds
    with `n - 4` obstacles, it holds with *every* obstacle count `m ≤ n - 4`.

    Combined with Xichuan's `n - 3` failure, a YES to OQ-01 would pin the
    threshold `f(n)` exactly at `n - 4`: rich lines survive all the way up to
    `n - 4`, then fail at `n - 3`. -/
theorem n_minus_4_extends_down (h : openProblem_n_minus_4) {n : ℕ} (hn : 5 ≤ n) :
    ∀ m : ℕ, m ≤ n - 4 → RichAvoids n m := by
  intro m hm
  have hbase : RichAvoids n (n - 4) := (openProblem_n_minus_4_iff.mp h) n hn
  exact richAvoids_antitone hm hbase

-- ════════════════════════════════════════════════════════════════
-- SECTION V: Summary
-- ════════════════════════════════════════════════════════════════

/--
**Summary of Erdős #105, OQ-01.**

The question "does the rich-line property survive `n - 4` obstacles?" is **OPEN**.
This file does not answer it; it makes it precise via one axiom-free reduction:

* `richAvoids_step` / `richAvoids_antitone` — the property is antitone in the
  obstacle count (more obstacles ⇒ strictly harder).
* `openProblem_n_minus_4_iff` — OQ-01 is exactly `∀ n ≥ 5, RichAvoids n (n-4)`.
* `n_minus_4_extends_down` — a YES to OQ-01 forces survival at every `m ≤ n-4`,
  pinning the threshold at `n-4` (given Xichuan's `n-3` failure).
* `not_richAvoids_succ_of_not` — a NO to OQ-01 manufactures a new `n-3`
  counterexample, i.e. would strengthen Xichuan's disproof.

No axioms, no sorries: the reduction itself is fully machine-checked; only the
underlying yes/no question remains open. -/
theorem erdos_105_oq01_summary {n : ℕ} (hn : 5 ≤ n) :
    (∀ {m₁ m₂ : ℕ}, m₁ ≤ m₂ → RichAvoids n m₂ → RichAvoids n m₁) ∧
    (openProblem_n_minus_4 ↔ ∀ k : ℕ, 5 ≤ k → RichAvoids k (k - 4)) ∧
    (openProblem_n_minus_4 → ∀ m : ℕ, m ≤ n - 4 → RichAvoids n m) :=
  ⟨fun hle hh => richAvoids_antitone hle hh,
   openProblem_n_minus_4_iff,
   fun h => n_minus_4_extends_down h hn⟩

end Erdos105OQ01
