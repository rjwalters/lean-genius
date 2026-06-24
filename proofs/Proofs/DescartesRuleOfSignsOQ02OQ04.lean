import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-
# Verified VAS real-root isolation from Budan certificates

This file answers open question #4 of *Budan's Theorem*
(`descartes-rule-of-signs-oq-02`):

> Can we formalize the VAS root isolation algorithm as a verified program that
> uses the proved root isolation certificates to produce certified root
> intervals?

The Vincent–Akritas–Strzeboński (VAS) algorithm isolates the real roots of a
polynomial by recursive bisection guided by Budan–Fourier sign-variation counts.
At an interval `(a, b]` it computes the count `V` at both endpoints and uses two
certificates proved in the parent entry:

* **root-free certificate**: `V a = V b  ⟹  no roots in (a, b]`
  (`no_roots_of_equal_budanCount`);
* **unique-root certificate**: `V a = V b + 1  ⟹  exactly one root in (a, b]`
  (`unique_root_of_budanCount_diff_one`).

When `V a - V b ≥ 2` the interval is bisected and the algorithm recurses on the
two halves.

## What is proved here, and what it depends on

The key mathematical observation is that **the correctness of the VAS procedure
depends only on the certificate properties of the count function, not on the
(axiomatized, analytic) proof of Budan's theorem itself.** We therefore develop
the algorithm *abstractly* over an arbitrary count function `V : ℝ → ℕ` and root
count `N : ℝ → ℝ → ℕ` satisfying:

* `hEq`   : `a < b → V a = V b     → N a b = 0`   (root-free certificate)
* `hOne`  : `a < b → V a = V b + 1 → N a b = 1`   (unique-root certificate)
* `hSplit`: `a < c → c < b → N a b = N a c + N c b` (additivity over a split point)

The parent entry supplies exactly such a triple: `V = budanCount p`,
`N = rootsInInterval p`, with `hEq`/`hOne` being the proved certificates and
`hSplit` being root counting over a partition (`rootsInInterval_split`).

Because we abstract over the interface, **this development is fully axiom-free
and machine-checked**: every `axiom` of Budan's theorem becomes an explicit
hypothesis, so the algorithm's correctness is established unconditionally as a
*reduction* (certificates ⟹ verified isolation).

## Results

Run with a fuel budget `fuel : ℕ` bounding the bisection depth, `vasIsolate`
returns an `IsolationResult` splitting the work into `isolated` intervals (each
certified to contain exactly one root) and `unresolved` intervals (where fuel
ran out before the count gap shrank to `≤ 1`). We prove:

* `vasIsolate_isolated_subset`   — every isolated interval lies inside `(a, b]`;
* `vasIsolate_isolated_one_root` — every isolated interval `(l, r)` has `l < r`
  and `N l r = 1` (exactly one root);
* `vasIsolate_isolated_disjoint` — the isolated intervals are pairwise disjoint;
* `vasIsolate_complete`          — once fully resolved (`unresolved = []`) the
  number of isolated intervals equals `N a b`, i.e. *every* root is isolated;
* `vasIsolate_correct`           — the packaged correctness statement.
-/

namespace VASIsolation

/-- The output of one run of the isolation procedure: a list of intervals each
certified to contain exactly one root, together with a list of intervals that
were left unresolved when the fuel budget was exhausted. -/
structure IsolationResult where
  /-- Intervals each certified to contain exactly one root. -/
  isolated : List (ℝ × ℝ)
  /-- Intervals where the fuel budget ran out before isolation. -/
  unresolved : List (ℝ × ℝ)

section Algorithm

variable (V : ℝ → ℕ) (N : ℝ → ℝ → ℕ)

/-- **The VAS isolation procedure.**

`vasIsolate V fuel a b` isolates the real roots inside the half-open interval
`(a, b]`, using only the sign-variation count `V` at the endpoints to decide each
step (the semantic root count `N` enters only in the correctness proofs):

* `V a = V b`     → no roots, return nothing;
* `V a = V b + 1` → one root, return the interval `(a, b)`;
* otherwise       → bisect at the midpoint and recurse on each half (consuming
  one unit of fuel). When `fuel = 0`, the still-undecided interval is recorded as
  *unresolved* rather than bisected. -/
noncomputable def vasIsolate : ℕ → ℝ → ℝ → IsolationResult
  | 0, a, b =>
      if V a = V b then ⟨[], []⟩
      else if V a = V b + 1 then ⟨[(a, b)], []⟩
      else ⟨[], [(a, b)]⟩
  | fuel + 1, a, b =>
      if V a = V b then ⟨[], []⟩
      else if V a = V b + 1 then ⟨[(a, b)], []⟩
      else
        ⟨(vasIsolate fuel a ((a + b) / 2)).isolated ++
            (vasIsolate fuel ((a + b) / 2) b).isolated,
          (vasIsolate fuel a ((a + b) / 2)).unresolved ++
            (vasIsolate fuel ((a + b) / 2) b).unresolved⟩

end Algorithm

section Correctness

variable {V : ℝ → ℕ} {N : ℝ → ℝ → ℕ}

/-- Midpoint lies strictly between the endpoints. -/
private theorem lt_mid {a b : ℝ} (h : a < b) : a < (a + b) / 2 := by linarith

private theorem mid_lt {a b : ℝ} (h : a < b) : (a + b) / 2 < b := by linarith

/-- **Containment.** Every isolated interval is a subinterval of `(a, b]`:
its endpoints satisfy `a ≤ l` and `r ≤ b`. -/
theorem vasIsolate_isolated_subset :
    ∀ (fuel : ℕ) (a b : ℝ), a < b →
      ∀ q ∈ (vasIsolate V fuel a b).isolated, a ≤ q.1 ∧ q.2 ≤ b := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b hab q hq
    simp only [vasIsolate] at hq
    split_ifs at hq with h1 h2
    · simp at hq
    · simp only [List.mem_singleton] at hq
      subst hq; exact ⟨le_refl _, le_refl _⟩
    · simp at hq
  | succ fuel ih =>
    intro a b hab q hq
    simp only [vasIsolate] at hq
    split_ifs at hq with h1 h2
    · simp at hq
    · simp only [List.mem_singleton] at hq
      subst hq; exact ⟨le_refl _, le_refl _⟩
    · rw [List.mem_append] at hq
      have hac : a < (a + b) / 2 := lt_mid hab
      have hcb : (a + b) / 2 < b := mid_lt hab
      rcases hq with hL | hR
      · obtain ⟨h1', h2'⟩ := ih a ((a + b) / 2) hac q hL
        exact ⟨h1', le_trans h2' (le_of_lt hcb)⟩
      · obtain ⟨h1', h2'⟩ := ih ((a + b) / 2) b hcb q hR
        exact ⟨le_trans (le_of_lt hac) h1', h2'⟩

/-- **Soundness.** Every isolated interval `(l, r)` is nondegenerate (`l < r`)
and contains *exactly one* root (`N l r = 1`). -/
theorem vasIsolate_isolated_one_root
    (hOne : ∀ a b : ℝ, a < b → V a = V b + 1 → N a b = 1) :
    ∀ (fuel : ℕ) (a b : ℝ), a < b →
      ∀ q ∈ (vasIsolate V fuel a b).isolated, q.1 < q.2 ∧ N q.1 q.2 = 1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b hab q hq
    simp only [vasIsolate] at hq
    split_ifs at hq with h1 h2
    · simp at hq
    · simp only [List.mem_singleton] at hq
      subst hq; exact ⟨hab, hOne a b hab h2⟩
    · simp at hq
  | succ fuel ih =>
    intro a b hab q hq
    simp only [vasIsolate] at hq
    split_ifs at hq with h1 h2
    · simp at hq
    · simp only [List.mem_singleton] at hq
      subst hq; exact ⟨hab, hOne a b hab h2⟩
    · rw [List.mem_append] at hq
      have hac : a < (a + b) / 2 := lt_mid hab
      have hcb : (a + b) / 2 < b := mid_lt hab
      rcases hq with hL | hR
      · exact ih a ((a + b) / 2) hac q hL
      · exact ih ((a + b) / 2) b hcb q hR

/-- Disjointness predicate for two half-open intervals `(l, r]`: one ends weakly
before the other begins. -/
def IntDisjoint (q r : ℝ × ℝ) : Prop := q.2 ≤ r.1 ∨ r.2 ≤ q.1

/-- **Disjointness.** The isolated intervals produced by one run are pairwise
disjoint. -/
theorem vasIsolate_isolated_disjoint :
    ∀ (fuel : ℕ) (a b : ℝ), a < b →
      (vasIsolate V fuel a b).isolated.Pairwise IntDisjoint := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b hab
    simp only [vasIsolate]
    split_ifs with h1 h2
    · exact List.Pairwise.nil
    · exact List.pairwise_singleton _ _
    · exact List.Pairwise.nil
  | succ fuel ih =>
    intro a b hab
    simp only [vasIsolate]
    split_ifs with h1 h2
    · exact List.Pairwise.nil
    · exact List.pairwise_singleton _ _
    · have hac : a < (a + b) / 2 := lt_mid hab
      have hcb : (a + b) / 2 < b := mid_lt hab
      rw [List.pairwise_append]
      refine ⟨ih a ((a + b) / 2) hac, ih ((a + b) / 2) b hcb, ?_⟩
      intro x hx y hy
      -- left intervals end ≤ midpoint, right intervals begin ≥ midpoint
      have hxr : x.2 ≤ (a + b) / 2 :=
        (vasIsolate_isolated_subset fuel a ((a + b) / 2) hac x hx).2
      have hyl : (a + b) / 2 ≤ y.1 :=
        (vasIsolate_isolated_subset fuel ((a + b) / 2) b hcb y hy).1
      exact Or.inl (le_trans hxr hyl)

/-- **Completeness.** Once the procedure has fully resolved the interval (no
intervals are left unresolved), the number of isolated intervals equals the
total root count `N a b`. Combined with soundness, this says *every* root has
been isolated into its own certified interval. -/
theorem vasIsolate_complete
    (hEq : ∀ a b : ℝ, a < b → V a = V b → N a b = 0)
    (hOne : ∀ a b : ℝ, a < b → V a = V b + 1 → N a b = 1)
    (hSplit : ∀ a c b : ℝ, a < c → c < b → N a b = N a c + N c b) :
    ∀ (fuel : ℕ) (a b : ℝ), a < b →
      (vasIsolate V fuel a b).unresolved = [] →
      (vasIsolate V fuel a b).isolated.length = N a b := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b hab hres
    simp only [vasIsolate] at hres ⊢
    split_ifs at hres ⊢ with h1 h2
    · simp only [List.length_nil]; exact (hEq a b hab h1).symm
    · simp only [List.length_singleton]; exact (hOne a b hab h2).symm
  | succ fuel ih =>
    intro a b hab hres
    simp only [vasIsolate] at hres ⊢
    split_ifs at hres ⊢ with h1 h2
    · simp only [List.length_nil]; exact (hEq a b hab h1).symm
    · simp only [List.length_singleton]; exact (hOne a b hab h2).symm
    · have hac : a < (a + b) / 2 := lt_mid hab
      have hcb : (a + b) / 2 < b := mid_lt hab
      rw [List.append_eq_nil_iff] at hres
      obtain ⟨hresL, hresR⟩ := hres
      rw [List.length_append,
        ih a ((a + b) / 2) hac hresL,
        ih ((a + b) / 2) b hcb hresR]
      exact (hSplit a ((a + b) / 2) b hac hcb).symm

/-- **Packaged correctness of VAS isolation.**

Given a sign-variation count `V` and root count `N` satisfying the Budan
certificates (`hEq`, `hOne`) and root-count additivity (`hSplit`), if the
procedure fully resolves `(a, b]` within its fuel budget, then it returns a list
of pairwise-disjoint subintervals of `(a, b]`, each containing exactly one root,
and there are exactly `N a b` of them — so every root of the interval is
isolated. -/
theorem vasIsolate_correct
    (hEq : ∀ a b : ℝ, a < b → V a = V b → N a b = 0)
    (hOne : ∀ a b : ℝ, a < b → V a = V b + 1 → N a b = 1)
    (hSplit : ∀ a c b : ℝ, a < c → c < b → N a b = N a c + N c b)
    (fuel : ℕ) (a b : ℝ) (hab : a < b)
    (hres : (vasIsolate V fuel a b).unresolved = []) :
    (∀ q ∈ (vasIsolate V fuel a b).isolated,
        a ≤ q.1 ∧ q.2 ≤ b ∧ q.1 < q.2 ∧ N q.1 q.2 = 1) ∧
      (vasIsolate V fuel a b).isolated.Pairwise IntDisjoint ∧
      (vasIsolate V fuel a b).isolated.length = N a b := by
  refine ⟨?_, vasIsolate_isolated_disjoint fuel a b hab,
    vasIsolate_complete hEq hOne hSplit fuel a b hab hres⟩
  intro q hq
  obtain ⟨hsub1, hsub2⟩ := vasIsolate_isolated_subset fuel a b hab q hq
  obtain ⟨hlt, hroot⟩ := vasIsolate_isolated_one_root hOne fuel a b hab q hq
  exact ⟨hsub1, hsub2, hlt, hroot⟩

end Correctness

/-!
## Worked sanity check

A degenerate but illustrative instance: a count function with no sign variation
anywhere (`V ≡ 0`) and the zero root count. The certificates hold vacuously, and
the procedure isolates nothing. -/

example :
    (vasIsolate (fun _ => 0) 5 0 1).isolated = [] := by
  simp [vasIsolate]

end VASIsolation
