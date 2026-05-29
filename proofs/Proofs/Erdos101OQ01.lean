/-
# Erdős Problem #101 — OQ-01: the o(n²) upper bound

This file is the S1 OBSERVE scaffold for OQ-01 of Erdős Problem #101.
The companion `Erdos101Problem.lean` establishes the framework
(`PlanarPointSet`, `collinear`, `NoFiveCollinear`, `fourPointLineCount`)
and the tight elementary bound `fourPointLineCount P ≤ n(n-1)/12`
(`improved_upper_bound`).

## The OPEN question

  For every $\varepsilon > 0$, does there exist $N$ such that
  every planar point set $P$ with $|P| \geq N$ and no five collinear
  satisfies
        fourPointLineCount(P) < ε · |P|²?

Equivalently, the maximum number of lines containing exactly four
points of an $n$-point planar set with no five collinear is $o(n^2)$.

Status: OPEN. $100 Erdős prize. Latest progress:

* Lower bound (Solymosi–Stojaković, 2013):
    n^{2 − O(1/√(log n))} — disproves Erdős's conjectured Θ(n^{3/2}).
* Upper bound (Szemerédi–Trotter applied, trivial double-counting):
    O(n²) — but no o(n²) bound is known.

The gap between these is the precise content of OQ-01.

## What this file contains

* Asymptotic vocabulary `IsLittleOh_n_squared` specialised to ℕ → ℕ.
* The formal Σ₂-style statement of the OQ-01 conjecture,
  `erdos_101_oq_01_conjecture`, recorded as a `sorry`.
* Easy small-case lemmas that the conjecture trivially subsumes,
  proved here unconditionally:
    - `fourPointLineCount_o_n_squared_holds_below_four` — for all
      $|P| < 4$, the count is $0$, vacuously $< \varepsilon \cdot n^2$
      for any $\varepsilon > 0$ and $n \geq 1$.
    - `fourPointLineCount_le_quadratic` — the trivial $O(n^2)$ upper
      bound restated in ℝ, witnessing that the question reduces to
      the quantitative little-oh refinement.
* A `BoundsAtRate` predicate parameterising bounds at rate $f(n)$, used
  to express known results:
    - `bounds_at_rate_quadratic_unconditional` (trivially provable).
    - `bounds_at_rate_quadratic_over_twelve` (improved bound).
    - `bounds_at_rate_quadratic_over_log_log_log` — a representative
      $o(n^2)$ rate, recorded as `sorry` (the open conjecture in
      asymptotic form).
* Documentation of the proof obstructions, the known partial results,
  and the Solymosi–Stojaković lower bound.

Reference: https://erdosproblems.com/101
-/

import Proofs.Erdos101Problem
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Nat.Lattice

namespace Erdos101OQ01

open Classical

/- ## Asymptotic vocabulary -/

/-- A function `f : ℕ → ℕ` is $o(n^2)$ if, for every $\varepsilon > 0$, all
sufficiently large $n$ satisfy `f n < ε · n²` as reals. -/
def IsLittleOh_n_squared (f : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (f n : ℝ) < ε * (n : ℝ)^2

/-- A rate predicate: `BoundsAtRate g` means every no-five-collinear set
satisfies `fourPointLineCount P ≤ g P.points.card` (as reals). -/
def BoundsAtRate (g : ℕ → ℝ) : Prop :=
  ∀ (P : PlanarPointSet), NoFiveCollinear P →
    (fourPointLineCount P : ℝ) ≤ g P.points.card

/- ## The OPEN question, in two equivalent forms -/

/-- **OQ-01, primary form**: the maximum four-point line count over
all no-five-collinear planar point sets of size at most `n` is $o(n^2)$.

Equivalent statement: for every $\varepsilon > 0$ there exists $N$ such
that every no-five-collinear `P` with `|P| ≥ N` satisfies
`fourPointLineCount P < ε · |P|²`.

This statement is **OPEN** ($100 Erdős prize). -/
def erdos_101_oq_01_conjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ (P : PlanarPointSet),
    NoFiveCollinear P → N ≤ P.points.card →
    (fourPointLineCount P : ℝ) < ε * (P.points.card : ℝ)^2

/-- **OQ-01, rate form**: there exists a function `g : ℕ → ℝ` that is
$o(n^2)$ and bounds `fourPointLineCount P` for every no-five-collinear
`P` (taking input size `n = |P|`).

This is the asymptotic statement of OQ-01 expressed as the existence of
an `o(n²)` *witness function*. It is OPEN. -/
def erdos_101_oq_01_rate_form : Prop :=
  ∃ g : ℕ → ℕ, IsLittleOh_n_squared g ∧
    ∀ (P : PlanarPointSet), NoFiveCollinear P →
      fourPointLineCount P ≤ g P.points.card

/-- The main open theorem of OQ-01, stated in primary form.

Proof is open. The two definitions `erdos_101_oq_01_conjecture` and
`erdos_101_oq_01_rate_form` are mutually convertible by the classical
ε-N $\leftrightarrow$ Cauchy-criterion bridge; we record the primary
form and leave the rate form unfolded as a definitional convenience. -/
theorem erdos_101_oq_01 : erdos_101_oq_01_conjecture := by
  sorry

/- ## Easy cases that the conjecture subsumes (proved here unconditionally) -/

/-- For every small point set ($|P| < 4$) the four-point line count is $0$:
there is no 4-element subset of `P.points` at all. Restatement of
`fourPointLineCount_lt_four` for the OQ-01 namespace. -/
theorem fourPointLineCount_zero_of_small (P : PlanarPointSet)
    (h : P.points.card < 4) : fourPointLineCount P = 0 :=
  fourPointLineCount_lt_four P h

/-- **OQ-01 holds vacuously for all `n ≤ 3`**: for every $\varepsilon > 0$
and every no-five-collinear `P` with `|P| ≤ 3`, the count is `0` and
hence strictly less than `ε · |P|²` whenever $|P| \geq 1$ (so the RHS
is positive). -/
theorem fourPointLineCount_o_n_squared_holds_below_four
    (ε : ℝ) (hε : 0 < ε) (P : PlanarPointSet)
    (hP_card : P.points.card ≤ 3) :
    (fourPointLineCount P : ℝ) < ε * (P.points.card : ℝ)^2 := by
  have hlt4 : P.points.card < 4 := by omega
  have h0 : fourPointLineCount P = 0 := fourPointLineCount_lt_four P hlt4
  rw [h0]
  have hpos : 0 < P.points.card := P.size_pos
  have hcard_pos_real : (0 : ℝ) < (P.points.card : ℝ) := by exact_mod_cast hpos
  have hsq_pos : (0 : ℝ) < (P.points.card : ℝ)^2 := pow_pos hcard_pos_real 2
  exact_mod_cast mul_pos hε hsq_pos

/-- **Trivial quadratic upper bound** (real version): `fourPointLineCount
P ≤ n(n-1)/12 ≤ n²/12 ≤ n²` for every no-five-collinear `P`.

Witnesses the $O(n^2)$ regime — the OQ-01 question is whether the
constant `1` in this bound can be tightened to any $\varepsilon > 0$
beyond a threshold. -/
theorem fourPointLineCount_le_quadratic (P : PlanarPointSet)
    (hP : NoFiveCollinear P) :
    (fourPointLineCount P : ℝ) ≤ (P.points.card : ℝ)^2 := by
  have hN : fourPointLineCount P ≤ P.points.card * (P.points.card - 1) / 12 :=
    improved_upper_bound P hP
  have hN' : (fourPointLineCount P : ℝ) ≤
      ((P.points.card * (P.points.card - 1) / 12 : ℕ) : ℝ) := by
    exact_mod_cast hN
  -- The cast: ((n * (n-1) / 12 : ℕ) : ℝ) ≤ n * (n-1) / 12 (real division), but in ℕ.
  -- We bound: n * (n-1) / 12 ≤ n * (n-1) ≤ n * n = n².
  have hbound_nat : P.points.card * (P.points.card - 1) / 12 ≤
      P.points.card * P.points.card := by
    set n := P.points.card
    have : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left n (Nat.sub_le n 1)
    have h1 : n * (n - 1) / 12 ≤ n * (n - 1) := Nat.div_le_self _ 12
    exact h1.trans this
  have hbound_real :
      ((P.points.card * (P.points.card - 1) / 12 : ℕ) : ℝ) ≤
        (P.points.card : ℝ)^2 := by
    have hle : ((P.points.card * (P.points.card - 1) / 12 : ℕ) : ℝ) ≤
        ((P.points.card * P.points.card : ℕ) : ℝ) := by
      exact_mod_cast hbound_nat
    have hsq : ((P.points.card * P.points.card : ℕ) : ℝ) =
        (P.points.card : ℝ)^2 := by push_cast; ring
    linarith
  linarith

/- ## Known bounds expressed via `BoundsAtRate` -/

/-- **Known: quadratic bound (trivial)**. -/
theorem bounds_at_rate_quadratic_unconditional :
    BoundsAtRate (fun n => (n : ℝ)^2) := by
  intro P hP
  exact fourPointLineCount_le_quadratic P hP

/-- **Known: improved quadratic bound** at rate $n^2 / 12$, weakening
`improved_upper_bound`'s $n(n-1)/12$ to avoid the subtraction-in-ℕ
cast subtlety. The $n(n-1)/12$ version follows by the same proof
together with `Nat.cast_pred` once $n \geq 1$; since OQ-01 only cares
about the asymptotic regime $n \to \infty$, the $n^2/12$ rate is
equivalent in the relevant sense. -/
theorem bounds_at_rate_quadratic_over_twelve :
    BoundsAtRate (fun n => (n : ℝ)^2 / 12) := by
  intro P hP
  have hN : fourPointLineCount P ≤ P.points.card * (P.points.card - 1) / 12 :=
    improved_upper_bound P hP
  set n := P.points.card with hn
  -- Bound the ℕ-divided product by `n * n / 12`, which is `n²/12`.
  have hbound_nat :
      n * (n - 1) / 12 ≤ n * n / 12 := by
    apply Nat.div_le_div_right
    exact Nat.mul_le_mul_left n (Nat.sub_le n 1)
  have hcast :
      ((n * n / 12 : ℕ) : ℝ) ≤ (n : ℝ)^2 / 12 := by
    calc ((n * n / 12 : ℕ) : ℝ)
        ≤ ((n * n : ℕ) : ℝ) / 12 := Nat.cast_div_le
      _ = (n : ℝ)^2 / 12 := by push_cast; ring
  calc (fourPointLineCount P : ℝ)
      ≤ ((n * (n - 1) / 12 : ℕ) : ℝ) := by exact_mod_cast hN
    _ ≤ ((n * n / 12 : ℕ) : ℝ) := by exact_mod_cast hbound_nat
    _ ≤ (n : ℝ)^2 / 12 := hcast

/- ## S11 ACT — IsBigO / IsLittleO bridge to Mathlib idiom

The following three artifacts bridge the slug-local asymptotic vocabulary
(`IsLittleOh_n_squared`, `BoundsAtRate`) to Mathlib's standard
`Asymptotics.IsBigO` / `Asymptotics.IsLittleO` predicates on filter
`Filter.atTop`. The bridge enables OQ-01 to be cited and consumed by
downstream gallery work using the canonical Mathlib asymptotic idiom,
without giving up the elementary slug-local forms.

Artifact (i): aggregator `maxFourPointLines n := n*(n-1)/12` and its
`IsBigO atTop (·^2)` certificate, plus the per-`P` `NoFiveCollinear`-gated
corollary (the `NoFiveCollinear` hypothesis is load-bearing: without it,
9 collinear points give `fourPointLineCount = C(9,4) = 126 > 6`).

Artifact (ii): the bridge lemma `IsLittleOh_n_squared ↔ IsLittleO atTop`
with the standard `c := ε/2` lift in the `←` direction.

Artifact (iii): the Mathlib-idiom existential form of OQ-01 and its
equivalence with the existing `erdos_101_oq_01_rate_form`; the main
OPEN theorem is rephrased as `erdos_101_oq_01_isLittleO`.
-/

/-- Aggregator: an `n`-only upper bound on the maximum
`fourPointLineCount` over no-five-collinear sets of size `n`, using the
elementary `improved_upper_bound` surrogate `n*(n-1)/12`. -/
noncomputable def maxFourPointLines (n : ℕ) : ℕ :=
  n * (n - 1) / 12

/-- The aggregator `maxFourPointLines` is `O(n²)` at infinity, in
Mathlib's `Asymptotics.IsBigO` idiom on filter `Filter.atTop`. -/
theorem maxFourPointLines_isBigO_n_squared :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (maxFourPointLines n : ℝ))
      (fun n : ℕ => (n : ℝ)^2) := by
  apply Asymptotics.IsBigO.of_norm_le
  intro n
  -- goal: ‖(maxFourPointLines n : ℝ)‖ ≤ (n : ℝ)^2  (single norm, RHS bare)
  rw [Real.norm_of_nonneg (by positivity)]
  unfold maxFourPointLines
  have hbnd : n * (n - 1) / 12 ≤ n * n :=
    (Nat.div_le_self _ 12).trans (Nat.mul_le_mul_left n (Nat.sub_le n 1))
  have hcast : ((n * (n - 1) / 12 : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) :=
    Nat.cast_le.mpr hbnd
  have hsq : ((n * n : ℕ) : ℝ) = (n : ℝ)^2 := by push_cast; ring
  linarith

/-- Per-`P` corollary: for every no-five-collinear planar point set `P`,
`fourPointLineCount P ≤ maxFourPointLines |P|`. The `NoFiveCollinear`
hypothesis is load-bearing — without it, `P` could place 9 points on a
line, giving `fourPointLineCount P = C(9,4) = 126 > 6 = maxFourPointLines 9`. -/
theorem fourPointLineCount_le_max (P : PlanarPointSet)
    (hP : NoFiveCollinear P) :
    (fourPointLineCount P : ℝ) ≤ (maxFourPointLines P.points.card : ℝ) := by
  have h₁ : fourPointLineCount P ≤
      P.points.card * (P.points.card - 1) / 12 :=
    improved_upper_bound P hP
  exact_mod_cast h₁

/-- Bridge: the slug-local strict-`<` predicate `IsLittleOh_n_squared g`
is equivalent to Mathlib's `Asymptotics.IsLittleO Filter.atTop (↑g) (·^2)`
non-strict form. The `→` direction is direct (`Real.norm_of_nonneg` for
each side); the `←` direction uses the standard `c := ε/2` lift, with an
`n ≥ 1` floor to ensure `(n : ℝ)^2 > 0` for the strict-gap step. -/
lemma isLittleOh_n_squared_iff_isLittleO (g : ℕ → ℕ) :
    IsLittleOh_n_squared g ↔
      Asymptotics.IsLittleO Filter.atTop
        (fun n : ℕ => (g n : ℝ))
        (fun n : ℕ => (n : ℝ)^2) := by
  unfold IsLittleOh_n_squared
  rw [Asymptotics.isLittleO_iff]
  constructor
  · intro hslug c hc
    rw [Filter.eventually_atTop]
    obtain ⟨N, hN⟩ := hslug c hc
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity)]
    linarith
  · intro hmathlib ε hε
    have hhalf : (0 : ℝ) < ε / 2 := by linarith
    have hev := hmathlib hhalf
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N₀, hN₀⟩ := hev
    refine ⟨max N₀ 1, fun n hn => ?_⟩
    have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
    have hn₁ : 1 ≤ n := (le_max_right _ _).trans hn
    have h := hN₀ n hn₀
    rw [Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity)] at h
    have hn_sq_pos : (0 : ℝ) < (n : ℝ)^2 := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn₁
      positivity
    nlinarith

/-- **OQ-01, Mathlib-idiom existential form.** There exists `g : ℕ → ℕ`
that is `o(n²)` (in `Asymptotics.IsLittleO Filter.atTop … (·^2)` sense)
and bounds `fourPointLineCount P` for every no-five-collinear `P`. This
is the Mathlib-idiom twin of `erdos_101_oq_01_rate_form` and is **OPEN**
($100 Erdős prize). -/
def erdos_101_oq_01_isLittleO_form : Prop :=
  ∃ g : ℕ → ℕ,
    Asymptotics.IsLittleO Filter.atTop
      (fun n : ℕ => (g n : ℝ))
      (fun n : ℕ => (n : ℝ)^2) ∧
    BoundsAtRate (fun n : ℕ => (g n : ℝ))

/-- The slug-local `erdos_101_oq_01_rate_form` and the Mathlib-idiom
`erdos_101_oq_01_isLittleO_form` are equivalent, via the bridge lemma
`isLittleOh_n_squared_iff_isLittleO`. -/
theorem erdos_101_oq_01_rate_form_iff_isLittleO :
    erdos_101_oq_01_rate_form ↔ erdos_101_oq_01_isLittleO_form := by
  unfold erdos_101_oq_01_rate_form erdos_101_oq_01_isLittleO_form
  constructor
  · rintro ⟨g, h_olittle, h_bounds⟩
    refine ⟨g, (isLittleOh_n_squared_iff_isLittleO g).mp h_olittle, ?_⟩
    intro P hP
    have hb : (fourPointLineCount P : ℝ) ≤ (g P.points.card : ℝ) := by
      exact_mod_cast h_bounds P hP
    exact hb
  · rintro ⟨g, h_olittle_mathlib, h_bounds⟩
    refine ⟨g, (isLittleOh_n_squared_iff_isLittleO g).mpr h_olittle_mathlib, ?_⟩
    intro P hP
    have hb : (fourPointLineCount P : ℝ) ≤ (g P.points.card : ℝ) := h_bounds P hP
    exact_mod_cast hb

/- ## conjecture ↔ rate_form: collapsing two open sorries into one

OQ-01 is stated here in two open forms — the primary ε-N
`erdos_101_oq_01_conjecture` and the Mathlib-idiom existential
`erdos_101_oq_01_isLittleO_form` — and the file already certifies
`rate_form ↔ isLittleO_form` (`erdos_101_oq_01_rate_form_iff_isLittleO`).
The missing link was `conjecture ↔ rate_form`. We supply it below, which
lets `erdos_101_oq_01_isLittleO` be *derived* from `erdos_101_oq_01`
rather than carried as an independent `sorry`: the file's open content
collapses to the single primary conjecture (plus the deferred
Solymosi–Stojaković construction).

The `conjecture → rate_form` direction needs an explicit `o(n²)` witness.
We use the size-indexed supremum
`maxCountAtSize n := sSup { fourPointLineCount Q | |Q| = n, NoFiveCollinear Q }`,
a genuine natural number because `improved_upper_bound` bounds the
underlying set above by `n(n-1)/12`.
-/

/-- The supremum of `fourPointLineCount` over all no-five-collinear
planar point sets of cardinality `n`. Well-defined in ℕ because
`improved_upper_bound` bounds the underlying set above by `n(n-1)/12`. -/
noncomputable def maxCountAtSize (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ Q : PlanarPointSet,
    Q.points.card = n ∧ NoFiveCollinear Q ∧ fourPointLineCount Q = k}

/-- The set of four-point line counts over no-five-collinear sets of size
`n` is bounded above by `n(n-1)/12` (`improved_upper_bound`). -/
theorem maxCountAtSize_bddAbove (n : ℕ) :
    BddAbove {k : ℕ | ∃ Q : PlanarPointSet,
      Q.points.card = n ∧ NoFiveCollinear Q ∧ fourPointLineCount Q = k} := by
  refine ⟨n * (n - 1) / 12, ?_⟩
  rintro k ⟨Q, hQcard, hQ5, rfl⟩
  rw [← hQcard]
  exact improved_upper_bound Q hQ5

/-- Every no-five-collinear set's four-point line count is at most the
size-indexed supremum `maxCountAtSize |P|`. -/
theorem le_maxCountAtSize (P : PlanarPointSet) (hP : NoFiveCollinear P) :
    fourPointLineCount P ≤ maxCountAtSize P.points.card := by
  unfold maxCountAtSize
  exact le_csSup (maxCountAtSize_bddAbove P.points.card) ⟨P, rfl, hP, rfl⟩

/-- If every no-five-collinear set of size `n` has four-point line count
strictly below a positive real `X`, then so does the supremum
`maxCountAtSize n`. Positivity of `X` covers the empty case (no such set
exists at size `n`), where `maxCountAtSize n = 0`. -/
theorem maxCountAtSize_lt_of_forall {n : ℕ} {X : ℝ} (hX : 0 < X)
    (h : ∀ Q : PlanarPointSet, Q.points.card = n → NoFiveCollinear Q →
      (fourPointLineCount Q : ℝ) < X) :
    (maxCountAtSize n : ℝ) < X := by
  unfold maxCountAtSize
  rcases Set.eq_empty_or_nonempty {k : ℕ | ∃ Q : PlanarPointSet,
      Q.points.card = n ∧ NoFiveCollinear Q ∧ fourPointLineCount Q = k}
      with he | hne
  · rw [he]
    have hz : sSup (∅ : Set ℕ) = 0 := csSup_empty
    rw [hz, Nat.cast_zero]
    exact hX
  · obtain ⟨Q, hQcard, hQ5, hQeq⟩ :=
      Nat.sSup_mem hne (maxCountAtSize_bddAbove n)
    rw [← hQeq]
    exact h Q hQcard hQ5

/-- **OQ-01 primary form ↔ rate form.** The ε-N statement
`erdos_101_oq_01_conjecture` is equivalent to the existence of an
`o(n²)` witness rate bounding every no-five-collinear count
(`erdos_101_oq_01_rate_form`).

`←` is direct from the definitions (the witness's `o(n²)` decay supplies
the threshold `N`). `→` takes the witness `maxCountAtSize`: it bounds
every count (`le_maxCountAtSize`), and it is `o(n²)` because the
conjecture forces every count — hence their supremum — below `ε·n²` for
large `n` (`maxCountAtSize_lt_of_forall`). -/
theorem erdos_101_oq_01_conjecture_iff_rate_form :
    erdos_101_oq_01_conjecture ↔ erdos_101_oq_01_rate_form := by
  unfold erdos_101_oq_01_conjecture erdos_101_oq_01_rate_form
  constructor
  · intro hconj
    refine ⟨maxCountAtSize, ?_, fun P hP => le_maxCountAtSize P hP⟩
    intro ε hε
    obtain ⟨N, hN⟩ := hconj ε hε
    refine ⟨max N 1, fun n hn => ?_⟩
    have hnN : N ≤ n := (le_max_left N 1).trans hn
    have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
    have hX : (0 : ℝ) < ε * (n : ℝ) ^ 2 := by
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      positivity
    refine maxCountAtSize_lt_of_forall hX (fun Q hQcard hQ5 => ?_)
    have hQN : N ≤ Q.points.card := by rw [hQcard]; exact hnN
    have hconjQ := hN Q hQ5 hQN
    rwa [hQcard] at hconjQ
  · rintro ⟨g, hg_olittle, hg_bound⟩ ε hε
    obtain ⟨N, hN⟩ := hg_olittle ε hε
    refine ⟨N, fun P hP hcard => ?_⟩
    have h1 : (fourPointLineCount P : ℝ) ≤ (g P.points.card : ℝ) := by
      exact_mod_cast hg_bound P hP
    have h2 := hN P.points.card hcard
    linarith

/-- **OQ-01, Mathlib-idiom form (OPEN main theorem).** Derived from the
primary form `erdos_101_oq_01` via the equivalence chain
`erdos_101_oq_01_conjecture ↔ erdos_101_oq_01_rate_form ↔
erdos_101_oq_01_isLittleO_form`. This is no longer an independent
`sorry`: it follows from `erdos_101_oq_01` alone, so the file's open
content is the single primary conjecture (plus the deferred
Solymosi–Stojaković construction). Still OPEN ($100 Erdős prize). -/
theorem erdos_101_oq_01_isLittleO : erdos_101_oq_01_isLittleO_form :=
  erdos_101_oq_01_rate_form_iff_isLittleO.mp
    (erdos_101_oq_01_conjecture_iff_rate_form.mp erdos_101_oq_01)

/- ## The OPEN refinement and its consequences

The conjecture would imply (via `bounds_at_rate_*`) that there exists
a witness rate `g : ℕ → ℝ` with `g n = o(n²)` and
`fourPointLineCount P ≤ g n` for every no-five-collinear `P` of size
`n`. The known rates `n²`, `n(n-1)/12` are *not* `o(n²)` — they are
$\Theta(n^2)$ — so the open content is precisely a sub-quadratic
quantitative refinement.

## Solymosi–Stojaković lower bound (existence statement)

For every $C > 0$ there exists $N$ such that for every $n \geq N$
there is a planar point set $P$ with $|P| = n$, no five collinear, and
fourPointLineCount(P) ≥ n^{2 - C / √(log n)}.

In particular, the maximum four-point line count is **not**
$O(n^{3/2})$ — Erdős's original $\Theta(n^{3/2})$ conjecture is
disproved. Any future formalisation of the construction would record
this as a counterexample to the Grünbaum bound. We do not formalise
the explicit construction here; the Lean statement of the lower bound
would be a `theorem` axiomatised against the Solymosi–Stojaković
paper, and we defer it to a follow-up iteration.

## Proof obstructions

* The Szemerédi–Trotter incidence theorem
  $I(P, L) = O(|P|^{2/3} |L|^{2/3} + |P| + |L|)$
  is the sharpest known incidence bound for lines, but applied to
  four-point lines it gives only the $O(n^2)$ regime; the $o(n^2)$
  refinement would require either an incidence improvement specific
  to lines of a fixed multiplicity or a non-incidence argument.
* The trivial double-counting argument (via `improved_upper_bound`)
  is tight at $n(n-1)/12$ — it cannot be improved by pure
  combinatorial counting without using a geometric input.
* Closing the gap is one of the central open problems in
  combinatorial geometry; this scaffold records the formal statement
  and the easy cases that the conjecture subsumes.

## Next iterations

* **S3**: connect `fourPointLineCount_le_quadratic` to a
  `Asymptotics.IsBigO` style statement using `Mathlib.Analysis.
  Asymptotics`; investigate whether the existing `improved_upper_bound`
  can yield a $1 - o(1)$ leading constant via per-point Cauchy–Schwarz
  beyond `fourCollinearThrough_bound`.

## S2 (this iteration): Solymosi–Stojaković lower bound

S2 records the Solymosi–Stojaković (2013) existential lower bound as a
`theorem ... := by sorry` (the construction itself is well beyond
elementary Lean and is deferred to a much later iteration).  The
statement is enough to *refute* Erdős's original $\Theta(n^{3/2})$
conjecture: the lower bound $n^{2 - C / \sqrt{\log n}}$ grows
asymptotically faster than $n^{3/2}$ for any fixed $C > 0$, so the
$\Theta(n^{3/2})$ conjecture is false in the upper-bound direction.

The conjecture sits between the trivial $O(n^2)$ upper bound and the
Solymosi–Stojaković $\Omega(n^{2 - O(1/\sqrt{\log n})})$ lower bound;
OQ-01 asks whether the upper side can be improved to $o(n^2)$.
-/

/- ## S2 ACT: Solymosi–Stojaković 2013 existential lower bound

The following two `theorem ... := by sorry` declarations record:

1. The Solymosi–Stojaković (2013) lower bound on the maximum
   four-point line count, witnessed by an explicit construction over
   finite fields (we do **not** formalise the construction; we record
   only the statement as a deferred proof obligation).
2. The corollary that Erdős's $\Theta(n^{3/2})$ conjecture is refuted
   by the same construction.

Both are recorded as `theorem ... := by sorry` rather than `axiom`
declarations, so the file remains axiom-free (the assumption is a
deferred *proof obligation* rather than a permanent assumption).
-/

/-- **Solymosi–Stojaković 2013 lower bound** (existential statement).

For every $C > 0$, all sufficiently large $n$ admit a no-five-collinear
planar point set of size $n$ with at least
$n^{2 - C / \sqrt{\log n}}$ four-point lines.

Reference: J. Solymosi and M. Stojaković, "Many collinear k-tuples
with no $k+1$ collinear points," *Discrete & Computational Geometry*
50 (2013), 811–820.

The construction uses algebraic geometry over finite fields and is
deferred to a much later iteration.  We record the statement as a
`theorem ... := by sorry` so it can be consumed by other theorems
without introducing a permanent `axiom`. -/
theorem solymosi_stojakovic_lower_bound :
    ∀ C : ℝ, 0 < C → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ P : PlanarPointSet, P.points.card = n ∧ NoFiveCollinear P ∧
        (fourPointLineCount P : ℝ) ≥
          (n : ℝ) ^ (2 - C / Real.sqrt (Real.log n)) := by
  sorry

/-- **Refutation of Erdős's original $\Theta(n^{3/2})$ conjecture.**

Erdős originally conjectured that the maximum number of four-point
lines under no-five-collinear is $\Theta(n^{3/2})$.  The Solymosi–
Stojaković lower bound refutes the upper half of that conjecture: for
every $C > 0$ and sufficiently large $n$, there exists a
no-five-collinear planar point set of size $n$ with strictly more than
$n^{3/2}$ four-point lines, i.e. there is no global $O(n^{3/2})$
upper bound.

This corollary follows from `solymosi_stojakovic_lower_bound` together
with the elementary asymptotic
$2 - C / \sqrt{\log n} > 3/2$ for sufficiently large $n$.

**S3 (this iteration)**: discharge.  Specialise the lower bound to
$C = 1/2$.  For $m \geq 3$, $\log m > 1$ (since $m > e$, using
`Real.exp_one_lt_d9 : \exp 1 < 2.7182818286 < 3`), so
$\sqrt{\log m} > 1$, hence $\tfrac{1/2}{\sqrt{\log m}} < 1/2$ and
$2 - \tfrac{1/2}{\sqrt{\log m}} > 3/2$.  The strict monotonicity of
`Real.rpow` in its exponent (for base $> 1$) then yields
$m^{2 - 1/(2\sqrt{\log m})} > m^{3/2}$, which contradicts the
hypothesised $m^{3/2}$ upper bound on the four-point line count of
the Solymosi–Stojaković witness set. -/
theorem erdos_three_halves_conjecture_refuted :
    ¬ (∃ N : ℕ, ∀ (P : PlanarPointSet), NoFiveCollinear P → N ≤ P.points.card →
        (fourPointLineCount P : ℝ) ≤ (P.points.card : ℝ) ^ (3 / 2 : ℝ)) := by
  rintro ⟨N₀, hN₀⟩
  -- Apply the Solymosi–Stojaković lower bound with `C = 1/2`.
  obtain ⟨N₁, hN₁⟩ :=
    solymosi_stojakovic_lower_bound (1 / 2 : ℝ) (by norm_num)
  -- Pick a single $m$ that simultaneously beats `N₀`, `N₁`, and `3`.
  set m : ℕ := max N₀ (max N₁ 3) with hm_def
  have hm_N₀ : N₀ ≤ m := le_max_left _ _
  have hm_N₁ : N₁ ≤ m :=
    (le_max_left N₁ 3).trans (le_max_right _ _)
  have hm_three : (3 : ℕ) ≤ m :=
    (le_max_right N₁ 3).trans (le_max_right _ _)
  -- Solymosi–Stojaković witness at size `m`.
  obtain ⟨P, hcard, hP_no5, hP_lb⟩ := hN₁ m hm_N₁
  -- Hypothesised $m^{3/2}$ upper bound applied to the same `P`.
  have hP_card_ge : N₀ ≤ P.points.card := hcard.symm ▸ hm_N₀
  have hP_ub : (fourPointLineCount P : ℝ) ≤
      (P.points.card : ℝ) ^ (3 / 2 : ℝ) :=
    hN₀ P hP_no5 hP_card_ge
  -- Real coercions for `m`.
  have hm_real_ge_three : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_three
  have hm_gt_one : (1 : ℝ) < (m : ℝ) := by linarith
  -- `Real.log m > 1` since `m ≥ 3 > exp 1`.
  have h_exp_lt_three : Real.exp 1 < (3 : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  have h_exp_lt_m : Real.exp 1 < (m : ℝ) := by linarith
  have hlog_gt_one : (1 : ℝ) < Real.log (m : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos 1) h_exp_lt_m
    rwa [Real.log_exp] at h
  -- `Real.sqrt (Real.log m) > 1`.
  have hsqrt_gt_one : (1 : ℝ) < Real.sqrt (Real.log (m : ℝ)) := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hlog_gt_one
    rwa [Real.sqrt_one] at h
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (Real.log (m : ℝ)) := by linarith
  -- `(1/2) / sqrt (log m) < 1/2` and hence `2 - … > 3/2`.
  have h_frac_lt_half :
      (1 / 2 : ℝ) / Real.sqrt (Real.log (m : ℝ)) < 1 / 2 := by
    rw [div_lt_iff₀ hsqrt_pos]
    nlinarith [hsqrt_gt_one]
  have h_exp_gt :
      (3 / 2 : ℝ) < 2 - (1 / 2 : ℝ) / Real.sqrt (Real.log (m : ℝ)) := by
    linarith
  -- Strict monotonicity of `Real.rpow` in the exponent (base `> 1`).
  have h_rpow_lt :
      (m : ℝ) ^ (3 / 2 : ℝ) <
        (m : ℝ) ^ (2 - (1 / 2 : ℝ) / Real.sqrt (Real.log (m : ℝ))) :=
    Real.rpow_lt_rpow_of_exponent_lt hm_gt_one h_exp_gt
  -- Rewrite the hypothesised upper bound in terms of `m`.
  have hP_ub_m : (fourPointLineCount P : ℝ) ≤ (m : ℝ) ^ (3 / 2 : ℝ) := by
    rw [hcard] at hP_ub; exact hP_ub
  -- The Solymosi–Stojaković lower bound is already phrased in `m`.
  -- Chain: `m^(2-1/2/sqrt log m) ≤ count ≤ m^(3/2)` but
  -- `m^(3/2) < m^(2-1/2/sqrt log m)` — contradiction.
  linarith [hP_lb, hP_ub_m, h_rpow_lt]

/-! ## S4 ACT: constructive refutation

The S3 negated-existence refutation `erdos_three_halves_conjecture_refuted`
proves *no global $O(n^{3/2})$ upper bound exists*. The constructive form
below provides, for every threshold `N`, an explicit no-five-collinear
witness `P` with `|P| ≥ N` and `|P|^{3/2} < fourPointLineCount(P)`.

The two forms are mutually derivable, but the positive form is more
useful downstream: it directly produces witnesses rather than refuting
a hypothetical bound. Both forms depend on the same axiom-free
deferred theorem `solymosi_stojakovic_lower_bound` (still sorry).

The proof reuses the S3 chain verbatim through the `Real.rpow_lt_rpow_of_exponent_lt`
step; the only structural change is the final assembly — instead of
deriving a contradiction from a hypothetical upper bound, we deliver
the witness directly.

Sorry count: unchanged (still 2: `erdos_101_oq_01` and
`solymosi_stojakovic_lower_bound`). Axiom count: unchanged (still 0).
Theorem count: +1 (`erdos_three_halves_conjecture_refuted_constructive`). -/

/-- **Constructive refutation of Erdős's $\Theta(n^{3/2})$ conjecture.**

For every threshold `N`, there exists a no-five-collinear planar point
set `P` with `|P| ≥ N` and *strictly more* than $|P|^{3/2}$ four-point
lines. This is the positive form of the S3 negated-existence
refutation `erdos_three_halves_conjecture_refuted`.

The proof specializes `solymosi_stojakovic_lower_bound` to `C = 1/2`
and uses the same `m ≥ 3 ⟹ log m > 1 ⟹ sqrt(log m) > 1 ⟹
(1/2)/sqrt(log m) < 1/2 ⟹ 2 - (1/2)/sqrt(log m) > 3/2` chain as S3,
then applies the strict monotonicity of `Real.rpow` in the exponent
for base `> 1`.

Sorry-free; axiom-free; depends only on the S2-recorded
`solymosi_stojakovic_lower_bound` (which itself remains a deferred
proof obligation, `theorem ... := by sorry`). -/
theorem erdos_three_halves_conjecture_refuted_constructive :
    ∀ N : ℕ, ∃ P : PlanarPointSet, NoFiveCollinear P ∧ N ≤ P.points.card ∧
      (P.points.card : ℝ) ^ (3 / 2 : ℝ) < (fourPointLineCount P : ℝ) := by
  intro N
  -- Apply the Solymosi–Stojaković lower bound with `C = 1/2`.
  obtain ⟨N₁, hN₁⟩ :=
    solymosi_stojakovic_lower_bound (1 / 2 : ℝ) (by norm_num)
  -- Pick a single `m` that simultaneously beats `N`, `N₁`, and `3`.
  set m : ℕ := max N (max N₁ 3) with hm_def
  have hm_N : N ≤ m := le_max_left _ _
  have hm_N₁ : N₁ ≤ m :=
    (le_max_left N₁ 3).trans (le_max_right _ _)
  have hm_three : (3 : ℕ) ≤ m :=
    (le_max_right N₁ 3).trans (le_max_right _ _)
  -- Solymosi–Stojaković witness at size `m`.
  obtain ⟨P, hcard, hP_no5, hP_lb⟩ := hN₁ m hm_N₁
  refine ⟨P, hP_no5, hcard.symm ▸ hm_N, ?_⟩
  -- Real coercions for `m`.
  have hm_real_ge_three : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_three
  have hm_gt_one : (1 : ℝ) < (m : ℝ) := by linarith
  -- `Real.log m > 1` since `m ≥ 3 > exp 1`.
  have h_exp_lt_three : Real.exp 1 < (3 : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  have h_exp_lt_m : Real.exp 1 < (m : ℝ) := by linarith
  have hlog_gt_one : (1 : ℝ) < Real.log (m : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos 1) h_exp_lt_m
    rwa [Real.log_exp] at h
  -- `Real.sqrt (Real.log m) > 1`.
  have hsqrt_gt_one : (1 : ℝ) < Real.sqrt (Real.log (m : ℝ)) := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hlog_gt_one
    rwa [Real.sqrt_one] at h
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (Real.log (m : ℝ)) := by linarith
  -- `(1/2) / sqrt (log m) < 1/2` and hence `2 - … > 3/2`.
  have h_frac_lt_half :
      (1 / 2 : ℝ) / Real.sqrt (Real.log (m : ℝ)) < 1 / 2 := by
    rw [div_lt_iff₀ hsqrt_pos]
    nlinarith [hsqrt_gt_one]
  have h_exp_gt :
      (3 / 2 : ℝ) < 2 - (1 / 2 : ℝ) / Real.sqrt (Real.log (m : ℝ)) := by
    linarith
  -- Strict monotonicity of `Real.rpow` in the exponent (base `> 1`).
  have h_rpow_lt :
      (m : ℝ) ^ (3 / 2 : ℝ) <
        (m : ℝ) ^ (2 - (1 / 2 : ℝ) / Real.sqrt (Real.log (m : ℝ))) :=
    Real.rpow_lt_rpow_of_exponent_lt hm_gt_one h_exp_gt
  -- Goal: `(P.points.card : ℝ) ^ (3/2) < (fourPointLineCount P : ℝ)`.
  -- Rewrite `P.points.card` as `m` and chain through `h_rpow_lt` + `hP_lb`.
  rw [hcard]
  linarith [hP_lb, h_rpow_lt]

end Erdos101OQ01
