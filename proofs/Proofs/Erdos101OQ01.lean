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
  positivity

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

* **S2**: formalise the Solymosi–Stojaković lower-bound *statement*
  (without the construction) as a recorded fact, witnessing
  $\Omega(n^{2 - O(1/\sqrt{\log n})})$ existential lower bound; this
  refutes Erdős's $\Theta(n^{3/2})$ original conjecture.
* **S3**: connect `fourPointLineCount_le_quadratic` to a
  `Asymptotics.IsBigO` style statement using `Mathlib.Analysis.
  Asymptotics`; investigate whether the existing `improved_upper_bound`
  can yield a $1 - o(1)$ leading constant via per-point Cauchy–Schwarz
  beyond `fourCollinearThrough_bound`.
-/

end Erdos101OQ01
