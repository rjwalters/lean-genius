/-
# Constructive Kuhn path-following: bounded termination of the door-pivot walk

Research artifact for `sperner-ndim-oq-06`: *"Formalize the Kuhn path-following
algorithm constructively: given a boundary door on face `d`, follow the unique
opposite door to reach a fully-coloured (FC) simplex in at most `O(N^d)` steps."*

## Background

The constructive proof of Sperner's lemma (Kuhn 1960; Scarf; Cottle–Dantzig) does
not merely *count* fully-coloured simplices modulo 2 — it **walks to one**.  On the
Kuhn (Freudenthal) triangulation of the `d`-cube / simplex with `N` subdivisions,
one considers *doors*: `(d-1)`-faces carrying the full label set `{0,…,d-1}`.  The
pivoting rule is deterministic:

* every simplex that is **not** fully coloured but has a door has **exactly one
  other** door — its *opposite door* — so from a door one steps to a uniquely
  determined next door;
* a **fully-coloured** (FC) simplex is a *terminal* room: entering it, there is no
  opposite door to leave by;
* a **boundary** door (on face `d` of the outer boundary) is a *source*: it has no
  interior predecessor door, so it is where the walk starts.

Because pivoting is *reversible* — the opposite-door relation is symmetric on
interior doors — the successor rule is **injective wherever it does not terminate**,
so starting from a source it traces a simple path that cannot loop back on itself
and therefore must stop at a terminal room (an FC simplex) after visiting each door
at most once, i.e. in at most `#doors = O(N^d)` steps.

## What this file proves

This file isolates and machine-checks the **combinatorial engine** of Kuhn
path-following, fully abstractly, with `0` sorries and `0` axioms.  We model the
pivot rule as a partial successor `f : V → Option V` on a finite type `V` of doors
(`none` = "entered an FC simplex — terminate"), subject to two hypotheses that
capture the geometry:

* `hinj : ∀ ⦃x y⦄, f x = f y → f x ≠ none → x = y` — **reversibility of pivoting**
  away from terminal rooms: a non-terminal door is the opposite door of at most one
  predecessor.  (Full injectivity would be *false*: several distinct terminal doors
  all pivot to `none`.)
* `hsrc : ∀ w, f w ≠ some v₀` — the start door `v₀` is a **source** (no interior
  predecessor), i.e. a boundary door.

This is the constructive companion of the *parity* engine in
`SpernerTuckerPathFollowing.lean`: parity proves an FC simplex *exists*; this file
shows the walk *reaches* one, deterministically and in bounded time.

Main results:

* `PathFollow.reaches_none` — **termination with the `O(N^d)` bound**: iterating the
  pivot from a source reaches `none` (an FC simplex) in at most `Fintype.card V`
  steps.
* `PathFollow.exists_terminal_door` — the last door before termination is a genuine
  *pivot-terminal* door `x` (`f x = none`): its simplex is fully coloured.
* `PathFollow.KuhnPivot` / `PathFollow.KuhnPivot.reaches_terminal` — the same,
  packaged from a symmetric interior-pivot relation `succ`/`pred` (the actual
  geometric input), so `hinj` and `hsrc` are *derived*, not assumed.
-/
import Mathlib

namespace SpernerNDimOQ06.PathFollow

open Function

variable {V : Type*} (f : V → Option V)

/-- One pivot step lifted to `Option V`: from a door `some v` move to `f v`; once
terminal (`none`), stay terminal.  The `n`-fold Kuhn walk from a start door is
`(step f)^[n] (some v₀)`. -/
def step (o : Option V) : Option V := o.bind f

@[simp] theorem step_none : step f none = none := rfl

@[simp] theorem step_some (v : V) : step f (some v) = f v := rfl

/-- The door visited after `n` pivot steps, starting from door `v₀`. -/
def orbit (v₀ : V) (n : ℕ) : Option V := (step f)^[n] (some v₀)

@[simp] theorem orbit_zero (v₀ : V) : orbit f v₀ 0 = some v₀ := rfl

theorem orbit_succ (v₀ : V) (n : ℕ) :
    orbit f v₀ (n + 1) = step f (orbit f v₀ n) := by
  simp only [orbit, Function.iterate_succ_apply']

/-- Once the walk terminates it stays terminated (entering an FC simplex is
absorbing). -/
theorem orbit_none_of_le {v₀ : V} {m n : ℕ} (hmn : m ≤ n)
    (hm : orbit f v₀ m = none) : orbit f v₀ n = none := by
  induction n with
  | zero =>
      obtain rfl : m = 0 := Nat.le_zero.mp hmn
      exact hm
  | succ k ih =>
      rcases hmn.lt_or_eq with h | h
      · rw [orbit_succ, ih (Nat.lt_succ_iff.mp h), step_none]
      · exact h ▸ hm

/-- **Backward-collision lemma.**  Suppose the walk has not terminated within the
first `N` steps, yet two of its doors coincide: `orbit i = orbit (i + d)` with a
positive gap `d`.  Following the equal doors backwards, injectivity-away-from-`none`
forces the *start* door `v₀` to have a predecessor.  Contrapositively, a source door
guarantees the walk is simple. -/
theorem source_pred_of_collision
    (hinj : ∀ ⦃x y : V⦄, f x = f y → f x ≠ none → x = y) {v₀ : V} {N d : ℕ}
    (hd : 1 ≤ d) (hall : ∀ n, n ≤ N → orbit f v₀ n ≠ none) :
    ∀ i, i + d ≤ N → orbit f v₀ i = orbit f v₀ (i + d) → ∃ w, f w = some v₀ := by
  intro i
  induction i with
  | zero =>
      intro hbound hcol
      obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp (hall (d - 1) (by omega))
      have hstep : orbit f v₀ d = f x := by
        have hde : d = (d - 1) + 1 := by omega
        rw [hde, orbit_succ, hx, step_some]
      rw [Nat.zero_add] at hcol
      rw [orbit_zero, hstep] at hcol
      exact ⟨x, hcol.symm⟩
  | succ k ih =>
      intro hbound hcol
      obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp (hall k (by omega))
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp (hall (k + d) (by omega))
      have e1 : orbit f v₀ (k + 1) = f x := by rw [orbit_succ, hx, step_some]
      have e2 : orbit f v₀ (k + 1 + d) = f y := by
        have hkd : k + 1 + d = (k + d) + 1 := by omega
        rw [hkd, orbit_succ, hy, step_some]
      rw [e1, e2] at hcol
      have hfx : f x ≠ none := by rw [← e1]; exact hall (k + 1) (by omega)
      have hxy : x = y := hinj hcol hfx
      exact ih (by omega) (by rw [hx, hy, hxy])

/-- **Constructive Kuhn path-following — termination in `O(N^d)` steps.**  On a
finite door set `V`, if pivoting is reversible away from terminal rooms (`hinj`) and
`v₀` is a source door (`hsrc`), then iterating the pivot from `v₀` reaches `none` —
a fully-coloured simplex — within `Fintype.card V` steps.  (`Fintype.card V` is the
number of doors, which on the `N`-fold Kuhn subdivision of a `d`-simplex is
`O(N^d)`.) -/
theorem reaches_none [Fintype V]
    (hinj : ∀ ⦃x y : V⦄, f x = f y → f x ≠ none → x = y) {v₀ : V}
    (hsrc : ∀ w, f w ≠ some v₀) :
    ∃ n ≤ Fintype.card V, orbit f v₀ n = none := by
  set N := Fintype.card V with hN
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ n, n ≤ N → orbit f v₀ n ≠ none`.  The walk avoids termination for
  -- `N + 1` consecutive steps, so it takes `N + 1` `V`-valued doors in a type of
  -- only `N` doors.  Pigeonhole gives a repeat, hence (backward collision) a
  -- source predecessor, contradicting `hsrc`.
  obtain ⟨i, hi, j, hj, hij, hφ⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (N + 1)) (t := (Finset.univ : Finset V))
      (f := fun n => (orbit f v₀ n).getD v₀)
      (by rw [Finset.card_univ, Finset.card_range, ← hN]; exact Nat.lt_succ_self N)
      (fun a _ => Finset.mem_univ _)
  have hiN : i ≤ N := by have := Finset.mem_range.mp hi; omega
  have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
  obtain ⟨xi, hxi⟩ := Option.ne_none_iff_exists'.mp (hcon i hiN)
  obtain ⟨xj, hxj⟩ := Option.ne_none_iff_exists'.mp (hcon j hjN)
  rw [hxi, hxj, Option.getD_some, Option.getD_some] at hφ
  have hoe : orbit f v₀ i = orbit f v₀ j := by rw [hxi, hxj, hφ]
  rcases Nat.lt_or_ge i j with hlt | hge
  · have hcol : orbit f v₀ i = orbit f v₀ (i + (j - i)) := by
      rw [show i + (j - i) = j by omega]; exact hoe
    obtain ⟨w, hw⟩ :=
      source_pred_of_collision f hinj (d := j - i) (by omega) hcon i (by omega) hcol
    exact hsrc w hw
  · have hgt : j < i := lt_of_le_of_ne hge (Ne.symm hij)
    have hcol : orbit f v₀ j = orbit f v₀ (j + (i - j)) := by
      rw [show j + (i - j) = i by omega]; exact hoe.symm
    obtain ⟨w, hw⟩ :=
      source_pred_of_collision f hinj (d := i - j) (by omega) hcon j (by omega) hcol
    exact hsrc w hw

/-- **The terminal door is a genuine FC door.**  Under the same hypotheses, the last
door `x` reached before the walk enters `none` satisfies `f x = none`: the room on
its far side is fully coloured.  This is the constructive existence statement Kuhn's
algorithm outputs. -/
theorem exists_terminal_door [Fintype V]
    (hinj : ∀ ⦃x y : V⦄, f x = f y → f x ≠ none → x = y) {v₀ : V}
    (hsrc : ∀ w, f w ≠ some v₀) :
    ∃ x : V, f x = none := by
  classical
  obtain ⟨n, _, hn⟩ := reaches_none f hinj hsrc
  have hex : ∃ m, orbit f v₀ m = none := ⟨n, hn⟩
  have hmnone : orbit f v₀ (Nat.find hex) = none := Nat.find_spec hex
  have hmpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · exfalso; rw [h0, orbit_zero] at hmnone; exact Option.some_ne_none _ hmnone
    · exact hpos
  obtain ⟨x, hx⟩ : ∃ x, orbit f v₀ (Nat.find hex - 1) = some x :=
    Option.ne_none_iff_exists'.mp (Nat.find_min hex (by omega))
  have hstep : orbit f v₀ (Nat.find hex) = f x := by
    have hfe : Nat.find hex = (Nat.find hex - 1) + 1 := by omega
    rw [hfe, orbit_succ, hx, step_some]
  rw [hstep] at hmnone
  exact ⟨x, hmnone⟩

/-- Abstract data of a **Kuhn door-pivot rule** on a finite door set `V`.  `succ v`
is the opposite door reached by pivoting out of the room entered through door `v`
(`none` = that room is fully coloured — terminate); `pred` is the reverse pivot, and
`symm` records that pivoting is **reversible** (the interior-door adjacency is
symmetric).  From `symm` alone, both hypotheses of `reaches_none` are derived. -/
structure KuhnPivot (V : Type*) where
  /-- Opposite-door successor: pivot forward out of a room. -/
  succ : V → Option V
  /-- Reverse pivot: the predecessor door. -/
  pred : V → Option V
  /-- Reversibility of pivoting: the interior-door adjacency is symmetric. -/
  symm : ∀ v w, succ v = some w ↔ pred w = some v

namespace KuhnPivot

variable (K : KuhnPivot V)

/-- A **source** door has no interior predecessor (a boundary door). -/
def IsSource (v₀ : V) : Prop := K.pred v₀ = none

/-- A **terminal** door pivots into a fully-coloured room. -/
def IsTerminal (x : V) : Prop := K.succ x = none

/-- Reversibility makes `succ` injective wherever it does not terminate. -/
theorem injOnSome :
    ∀ ⦃x y : V⦄, K.succ x = K.succ y → K.succ x ≠ none → x = y := by
  intro x y hxy hne
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hne
  have hx : K.pred w = some x := (K.symm x w).mp hw
  have hy : K.pred w = some y := (K.symm y w).mp (hxy ▸ hw)
  exact Option.some.inj (hx ▸ hy)

/-- A source door has no `succ`-predecessor. -/
theorem no_pred_source {v₀ : V} (h : K.IsSource v₀) : ∀ w, K.succ w ≠ some v₀ := by
  intro w hw
  have hp : K.pred v₀ = some w := (K.symm w v₀).mp hw
  rw [show K.pred v₀ = none from h] at hp
  exact Option.noConfusion hp

/-- **Kuhn's algorithm terminates.**  From any source door, following opposite doors
reaches a fully-coloured simplex within `Fintype.card V` pivots. -/
theorem reaches_terminal [Fintype V] {v₀ : V} (h : K.IsSource v₀) :
    ∃ n ≤ Fintype.card V, orbit K.succ v₀ n = none :=
  reaches_none K.succ K.injOnSome (K.no_pred_source h)

/-- **Kuhn's algorithm outputs a fully-coloured simplex.**  From any source door,
the walk ends at a genuine terminal door. -/
theorem exists_terminal [Fintype V] {v₀ : V} (h : K.IsSource v₀) :
    ∃ x : V, K.IsTerminal x :=
  exists_terminal_door K.succ K.injOnSome (K.no_pred_source h)

end KuhnPivot

end SpernerNDimOQ06.PathFollow
