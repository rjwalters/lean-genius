/-
  Erdős #117 OQ-01 (incomplete-01): the oscillation of the growth rate

  Companion to `Proofs.Erdos117OQ01`, which studies whether the normalized
  logarithmic growth rate `growthRate n = log(h n)/n` of the abelian covering
  number `h(n)` converges (equivalently, whether `h(n)` has a single exponential
  base — Erdős #117 OQ-01).  The parent pins the open question down to the
  cluster values `growthRateLimInf`, `growthRateLimSup` and their difference
  (the *oscillation* `limsup − liminf`), and shows

      converges ⟺ liminf = limsup ⟺ oscillation = 0 ⟺ exponential base exists,

  together with the one-sided window bound
  `oscillation ≤ log c₂ − log c₁` (`growthRate_oscillation_le_window`).

  This file supplies the missing lower side and the negation form, so the
  oscillation is fully trapped and the open question has a clean "is the
  oscillation strictly positive?" phrasing.  All results are proved from the
  parent's API and add **no new axioms** (they inherit only the parent's three
  Pyber-bound assumptions `h`, `h_pos`, `pyber_bounds`).

  ## What this file proves (0 new axioms, 0 sorries)

  * `growthRate_oscillation_nonneg` — `0 ≤ limsup − liminf` (from `limInf_le_limSup`).
  * `oscillation_mem_window` — the oscillation lies in `[0, log c₂ − log c₁]`,
    combining the new lower bound with the parent's upper bound.
  * `exponentialBaseExists_iff_oscillation_zero` — the open question restated:
    a single exponential base exists iff the oscillation vanishes.
  * `not_exponentialBaseExists_iff_oscillation_pos` — the negation: **no** single
    base exists iff the oscillation is strictly positive (`0 < limsup − liminf`),
    the crispest form of "does the limit fail to exist?".

  Parent: Erdos117OQ01.lean
-/

import Mathlib
import Proofs.Erdos117OQ01

open Real Filter

namespace Erdos117OQ01Incomplete01

open Erdos117OQ01

/-- **The oscillation is nonnegative.**  `0 ≤ growthRateLimSup − growthRateLimInf`:
the limsup of a sequence always dominates its liminf (`limInf_le_limSup`).  The lower
companion of `growthRate_oscillation_le_window`, so the oscillation of the growth rate is
trapped in `[0, log c₂ − log c₁]`. -/
theorem growthRate_oscillation_nonneg :
    0 ≤ growthRateLimSup - growthRateLimInf :=
  sub_nonneg.mpr limInf_le_limSup

/-- **The oscillation lies in Pyber's log-window.**  Combining the new lower bound
`growthRate_oscillation_nonneg` with the parent's upper bound
`growthRate_oscillation_le_window`, the oscillation `limsup − liminf` of the growth rate
is trapped in `[0, log c₂ − log c₁]` for Pyber's constants `1 < c₁ < c₂`.  Even without
knowing whether the limit exists, the amount by which the growth rate can oscillate is
bounded by the fixed log-width of Pyber's exponential window. -/
theorem oscillation_mem_window :
    ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ c₁ < c₂ ∧
      0 ≤ growthRateLimSup - growthRateLimInf ∧
      growthRateLimSup - growthRateLimInf ≤ Real.log c₂ - Real.log c₁ := by
  obtain ⟨c₁, c₂, h1, h12, hle⟩ := growthRate_oscillation_le_window
  exact ⟨c₁, c₂, h1, h12, growthRate_oscillation_nonneg, hle⟩

/-- **The open question ⟺ zero oscillation.**  Chaining
`exponentialBaseExists_iff_converges` with `converges_iff_oscillation_zero`:
`h(n)` has a single exponential base iff the oscillation `limsup − liminf` of the growth
rate is exactly `0`.  The oscillation form of `exponentialBaseExists_iff_limInfEqLimSup`. -/
theorem exponentialBaseExists_iff_oscillation_zero :
    exponentialBaseExists ↔ growthRateLimSup - growthRateLimInf = 0 :=
  exponentialBaseExists_iff_converges.trans converges_iff_oscillation_zero

/-- **The negation of the open question ⟺ strictly positive oscillation.**  No single
exponential base exists iff the oscillation is strictly positive: since the oscillation is
nonnegative (`growthRate_oscillation_nonneg`), failing to vanish means being `> 0`.  This
is the crispest form of "the limit `lim log h(n)/n` fails to exist" — it is exactly the
statement that the growth rate genuinely oscillates within Pyber's window. -/
theorem not_exponentialBaseExists_iff_oscillation_pos :
    ¬ exponentialBaseExists ↔ 0 < growthRateLimSup - growthRateLimInf := by
  rw [exponentialBaseExists_iff_oscillation_zero]
  exact ⟨fun h => lt_of_le_of_ne growthRate_oscillation_nonneg (Ne.symm h), fun h => h.ne'⟩

/-- **Both endpoints of the oscillation lie in Pyber's window individually.**  The parent's
`limInfLimSup_window` bounds `growthRateLimInf` from *below* by `log c₁` and `growthRateLimSup`
from *above* by `log c₂`.  Chaining with `limInf_le_limSup` closes the gap: *each* of the
liminf and the limsup lies in the full closed window `[log c₁, log c₂]`.  This is the
individual-endpoint companion of `oscillation_mem_window` (which traps only their *difference*),
and in particular shows both are genuine finite reals confined to Pyber's exponential window,
whether or not the growth rate converges. -/
theorem limInf_limSup_mem_window :
    ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ c₁ < c₂ ∧
      growthRateLimInf ∈ Set.Icc (Real.log c₁) (Real.log c₂) ∧
      growthRateLimSup ∈ Set.Icc (Real.log c₁) (Real.log c₂) := by
  obtain ⟨c₁, c₂, hc1, hc12, hlo, hhi⟩ := limInfLimSup_window
  have hle := limInf_le_limSup
  exact ⟨c₁, c₂, hc1, hc12, ⟨hlo, hle.trans hhi⟩, ⟨hlo.trans hle, hhi⟩⟩

/-! ### A sufficient condition that resolves the open question: submultiplicativity

The results above only *characterise* the open question (as "is the oscillation
positive?").  This section supplies the first *sufficient condition* that answers it,
lifting the parent's Fekete result `submultiplicative_implies_convergence` into the
oscillation / exponential-base language of this file: if the covering number `h` is
submultiplicative (`h(m+n) ≤ h(m)·h(n)`), the oscillation vanishes, a single exponential
base exists, and the open question is resolved *yes*.  Contrapositively, a genuinely
oscillating growth rate (no exponential base) forces `h` to violate submultiplicativity —
a concrete necessary condition on any counterexample to Erdős #117 OQ-01. -/

/-- **Submultiplicativity ⟹ zero oscillation.**  If `h(m+n) ≤ h(m)·h(n)` for all `m, n`,
then the oscillation `limsup − liminf` of the growth rate is exactly `0`.  Fekete's lemma
(`submultiplicative_implies_convergence`) gives convergence, and
`converges_iff_oscillation_zero` turns that into vanishing oscillation. -/
theorem submultiplicative_implies_oscillation_zero
    (hsub : ∀ m n : ℕ, h (m + n) ≤ h m * h n) :
    growthRateLimSup - growthRateLimInf = 0 :=
  converges_iff_oscillation_zero.mp (submultiplicative_implies_convergence hsub)

/-- **Submultiplicativity ⟹ a single exponential base exists.**  The exponential-base form
of `submultiplicative_implies_oscillation_zero`: a submultiplicative covering number `h` has
a well-defined exponential base, so Erdős #117 OQ-01 is answered *yes* under this hypothesis.
Fekete convergence (`submultiplicative_implies_convergence`) transported through
`exponentialBaseExists_iff_converges`. -/
theorem submultiplicative_implies_exponentialBaseExists
    (hsub : ∀ m n : ℕ, h (m + n) ≤ h m * h n) :
    exponentialBaseExists :=
  exponentialBaseExists_iff_converges.mpr (submultiplicative_implies_convergence hsub)

/-- **A counterexample must break submultiplicativity.**  The contrapositive: if no single
exponential base exists (the growth rate genuinely oscillates), then `h` is *not*
submultiplicative — there exist `m, n` with `h(m+n) > h(m)·h(n)`.  A concrete necessary
condition on any counterexample to Erdős #117 OQ-01. -/
theorem not_exponentialBaseExists_implies_not_submultiplicative
    (hno : ¬ exponentialBaseExists) :
    ¬ (∀ m n : ℕ, h (m + n) ≤ h m * h n) :=
  fun hsub => hno (submultiplicative_implies_exponentialBaseExists hsub)

/-! ### The dual sufficient condition: supermultiplicativity

The parent proves `submultiplicative_implies_convergence` via Fekete's lemma
applied to the *subadditive* sequence `log(h n)` (Mathlib's
`Subadditive.tendsto_lim`).  Mathlib has no `Superadditive` API, so the dual
condition — `h(m)·h(n) ≤ h(m+n)` (**supermultiplicativity**) — is not covered.
We supply it here by applying `Subadditive.tendsto_lim` to the *negated*
sequence `g n = −log(h n)`, which is subadditive exactly when `log(h n)` is
superadditive.  The boundedness hypothesis Fekete needs (`g n / n` bounded
below) is furnished by Pyber's **upper** bound `growthRate n ≤ log c₂`
(`growthRate_upper_bound`), the mirror of the lower bound used in the
submultiplicative proof.

Consequently *either* one-sided multiplicative inequality resolves Erdős #117
OQ-01 in the affirmative, and — the sharpened capstone — a genuine
counterexample (no exponential base) must violate **both** at once. -/

/-- **Supermultiplicativity ⟹ convergence** (the Fekete dual).  If
`h(m)·h(n) ≤ h(m+n)` for all `m, n`, the growth rate converges.  Proof: the
sequence `g n = −log(h n)` is subadditive (superadditivity of `log h`), and
`g n / n = −growthRate n ≥ −log c₂` is bounded below by Pyber's upper bound, so
Mathlib's `Subadditive.tendsto_lim` gives `g n / n → g.lim`; negating,
`growthRate n → −g.lim`.  The mirror image of the parent's
`submultiplicative_implies_convergence`. -/
theorem supermultiplicative_implies_convergence
    (hsup : ∀ m n : ℕ, h m * h n ≤ h (m + n)) :
    growthRateConverges := by
  -- `g = -log h` is subadditive; Fekete gives `g n / n → g.lim`, so `growthRate → -g.lim`.
  let g : ℕ → ℝ := fun n => - Real.log (h n : ℝ)
  -- `h 0 ≤ 1`: from `hsup 0 0`, `h 0 * h 0 ≤ h 0`.
  have h0_le : h 0 ≤ 1 := by
    have hh := hsup 0 0
    rw [Nat.add_zero] at hh
    rcases Nat.eq_zero_or_pos (h 0) with h0z | h0p
    · omega
    · exact Nat.le_of_mul_le_mul_left (by rwa [Nat.mul_one]) h0p
  -- Hence `log(h 0) = 0` (whether `h 0 = 0` or `1`).
  have hlog0 : Real.log (h 0 : ℝ) = 0 := by
    have : h 0 = 0 ∨ h 0 = 1 := by omega
    rcases this with h0 | h0 <;> rw [h0] <;> simp
  have h_pos_ge1 : ∀ n : ℕ, 1 ≤ n → (0 : ℝ) < (h n : ℝ) := fun n hn => by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (h_pos n hn)
  -- `log h` is superadditive (for all `m, n`, using `log(h 0) = 0` for the boundary).
  have hlog_super : ∀ m n : ℕ,
      Real.log (h m : ℝ) + Real.log (h n : ℝ) ≤ Real.log (h (m + n) : ℝ) := by
    intro m n
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hlog0]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hlog0]
    have hm' := h_pos_ge1 m hm
    have hn' := h_pos_ge1 n hn
    rw [← Real.log_mul (ne_of_gt hm') (ne_of_gt hn')]
    exact Real.log_le_log (mul_pos hm' hn') (by exact_mod_cast hsup m n)
  -- Therefore `g` is subadditive.
  have hg_sub : Subadditive g := fun m n => by
    show - Real.log (h (m + n) : ℝ) ≤ - Real.log (h m : ℝ) + - Real.log (h n : ℝ)
    linarith [hlog_super m n]
  -- `g n / n` is bounded below: `= -growthRate n ≥ -log c₂` for `n ≥ 1`, `= 0` for `n = 0`.
  have hbdd : BddBelow (Set.range fun n : ℕ => g n / n) := by
    obtain ⟨U, hU⟩ := growthRate_upper_bound
    refine ⟨min (-U) 0, ?_⟩
    rintro x ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · show min (-U) 0 ≤ g 0 / ((0 : ℕ) : ℝ)
      simp only [Nat.cast_zero, div_zero]
      exact min_le_right _ _
    · have hgn : g n / n = - growthRate n := by
        show (- Real.log (h n : ℝ)) / (n : ℝ) = - growthRate n
        unfold growthRate
        rw [if_neg (show n ≠ 0 from by omega), neg_div]
      show min (-U) 0 ≤ g n / (n : ℝ)
      rw [hgn]
      have hgr : growthRate n ≤ U := hU n hpos
      calc min (-U) 0 ≤ -U := min_le_left _ _
        _ ≤ - growthRate n := by linarith
  -- Fekete on `g`, then negate to recover `growthRate`.
  refine ⟨- hg_sub.lim, ?_⟩
  have hneg := (hg_sub.tendsto_lim hbdd).neg
  apply hneg.congr'
  apply Filter.eventually_atTop.mpr
  refine ⟨1, fun n hn => ?_⟩
  show -((- Real.log (h n : ℝ)) / (n : ℝ)) = growthRate n
  unfold growthRate
  rw [if_neg (show n ≠ 0 from by omega), neg_div, neg_neg]

/-- **Supermultiplicativity ⟹ zero oscillation.**  The oscillation form of
`supermultiplicative_implies_convergence`, dual to
`submultiplicative_implies_oscillation_zero`. -/
theorem supermultiplicative_implies_oscillation_zero
    (hsup : ∀ m n : ℕ, h m * h n ≤ h (m + n)) :
    growthRateLimSup - growthRateLimInf = 0 :=
  converges_iff_oscillation_zero.mp (supermultiplicative_implies_convergence hsup)

/-- **Supermultiplicativity ⟹ a single exponential base exists.**  The
exponential-base form: a supermultiplicative covering number `h` answers Erdős
#117 OQ-01 *yes*, dual to `submultiplicative_implies_exponentialBaseExists`. -/
theorem supermultiplicative_implies_exponentialBaseExists
    (hsup : ∀ m n : ℕ, h m * h n ≤ h (m + n)) :
    exponentialBaseExists :=
  exponentialBaseExists_iff_converges.mpr (supermultiplicative_implies_convergence hsup)

/-- **A counterexample must break supermultiplicativity too.**  The
contrapositive dual of `not_exponentialBaseExists_implies_not_submultiplicative`:
if no single exponential base exists then `h` is not supermultiplicative either. -/
theorem not_exponentialBaseExists_implies_not_supermultiplicative
    (hno : ¬ exponentialBaseExists) :
    ¬ (∀ m n : ℕ, h m * h n ≤ h (m + n)) :=
  fun hsup => hno (supermultiplicative_implies_exponentialBaseExists hsup)

/-- **A counterexample must break BOTH one-sided multiplicative laws.**  The
sharpened structural constraint on any counterexample to Erdős #117 OQ-01:
since *either* submultiplicativity (`h(m+n) ≤ h(m)·h(n)`) *or*
supermultiplicativity (`h(m)·h(n) ≤ h(m+n)`) alone would force convergence, a
genuinely oscillating covering number must violate **both** — its values can be
neither globally sub- nor globally super-multiplicative. -/
theorem not_exponentialBaseExists_implies_not_multiplicative
    (hno : ¬ exponentialBaseExists) :
    ¬ (∀ m n : ℕ, h (m + n) ≤ h m * h n) ∧ ¬ (∀ m n : ℕ, h m * h n ≤ h (m + n)) :=
  ⟨not_exponentialBaseExists_implies_not_submultiplicative hno,
   not_exponentialBaseExists_implies_not_supermultiplicative hno⟩

/-- **Every subsequential limit of the growth rate lies in Pyber's window.**  If a subsequence
`k ↦ growthRate (φ k)` (indexed by any strictly monotone `φ : ℕ → ℕ`) converges to a value `x`,
then `x` lies in the fixed band `[log c₁, log c₂]`.  This is strictly stronger than the
liminf/limsup confinement `limInf_limSup_mem_window`, which pins down only the two *extreme*
cluster values: here the *entire* set of subsequential limits — every accumulation point of the
growth rate, whether or not the sequence converges — is trapped inside Pyber's exponential
window.  In particular the growth rate can neither escape upward toward an unbounded exponential
base nor collapse downward below `c₁`, no matter along which subsequence one looks.

Proof: the pointwise window `growthRate_window` gives `log c₁ ≤ growthRate n ≤ log c₂` for all
`n ≥ 1`; a strictly monotone `φ` tends to `atTop`, so `φ k ≥ 1` eventually, hence the
subsequence is eventually inside the band, and passing to the limit (`ge_of_tendsto` /
`le_of_tendsto`, using that `[log c₁, log c₂]` is closed) confines `x`. -/
theorem growthRate_subseq_limit_mem_window {φ : ℕ → ℕ} (hφ : StrictMono φ) {x : ℝ}
    (hx : Filter.Tendsto (fun k => growthRate (φ k)) Filter.atTop (nhds x)) :
    ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ c₁ < c₂ ∧ x ∈ Set.Icc (Real.log c₁) (Real.log c₂) := by
  obtain ⟨c₁, c₂, hc1, hc12, hwin⟩ := growthRate_window
  -- A strictly monotone `φ : ℕ → ℕ` diverges, so the subsequence index is eventually `≥ 1`.
  have hev_ge1 : ∀ᶠ k in Filter.atTop, 1 ≤ φ k :=
    hφ.tendsto_atTop.eventually (Filter.eventually_ge_atTop 1)
  have hev1 : ∀ᶠ k in Filter.atTop, Real.log c₁ ≤ growthRate (φ k) := by
    filter_upwards [hev_ge1] with k hk using (hwin (φ k) hk).1
  have hev2 : ∀ᶠ k in Filter.atTop, growthRate (φ k) ≤ Real.log c₂ := by
    filter_upwards [hev_ge1] with k hk using (hwin (φ k) hk).2
  exact ⟨c₁, c₂, hc1, hc12,
    Set.mem_Icc.mpr ⟨ge_of_tendsto hx hev1, le_of_tendsto hx hev2⟩⟩

/-! ### The extreme cluster values are attained

`growthRate_subseq_limit_mem_window` shows every subsequential limit lies *inside* Pyber's
window `[log c₁, log c₂]`.  The converse-flavoured completion below shows the two extreme
cluster values — `growthRateLimInf` and `growthRateLimSup` — are themselves *attained* as
subsequential limits: there are index sequences diverging to `∞` along which the growth rate
converges to each.  So the two abstract `liminf`/`limsup` values are genuine accumulation
points of the growth rate, not merely formal bounds; together with the window confinement
this pins the cluster set of `growthRate` down as a nonempty compact subset of
`[log c₁, log c₂]` with minimum `growthRateLimInf` and maximum `growthRateLimSup`. -/

/-- **The limsup is attained as a subsequential limit.**  There is an index sequence
`x : ℕ → ℕ` diverging to `∞` (`Tendsto x atTop atTop`) along which
`growthRate (x k) → growthRateLimSup`.  Thus the *largest* cluster value of the growth rate is
a genuine accumulation point.  The growth rate is eventually confined to Pyber's window
`[log c₁, log c₂]` (`growthRate_window`), providing the boundedness and coboundedness
`exists_seq_tendsto_limsup` requires. -/
theorem exists_subseq_tendsto_growthRateLimSup :
    ∃ x : ℕ → ℕ, Filter.Tendsto x atTop atTop ∧
      Filter.Tendsto (fun k => growthRate (x k)) atTop (nhds growthRateLimSup) := by
  obtain ⟨c₁, c₂, _, _, hwin⟩ := growthRate_window
  have hle : ∀ᶠ n in atTop, growthRate n ≤ Real.log c₂ :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => (hwin n hn).2⟩
  have hge : ∀ᶠ n in atTop, Real.log c₁ ≤ growthRate n :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => (hwin n hn).1⟩
  have hb : Filter.IsBoundedUnder (· ≤ ·) atTop growthRate := ⟨Real.log c₂, hle⟩
  have hc : Filter.IsCoboundedUnder (· ≤ ·) atTop growthRate :=
    isCoboundedUnder_le_of_eventually_le atTop hge
  obtain ⟨x, hxlim, hxtop⟩ := exists_seq_tendsto_limsup (u := growthRate) (f := atTop) hc hb
  exact ⟨x, hxtop, hxlim⟩

/-- **The liminf is attained as a subsequential limit.**  Dual to
`exists_subseq_tendsto_growthRateLimSup`: an index sequence `x : ℕ → ℕ` diverging to `∞` with
`growthRate (x k) → growthRateLimInf`, so the *smallest* cluster value of the growth rate is
also a genuine accumulation point. -/
theorem exists_subseq_tendsto_growthRateLimInf :
    ∃ x : ℕ → ℕ, Filter.Tendsto x atTop atTop ∧
      Filter.Tendsto (fun k => growthRate (x k)) atTop (nhds growthRateLimInf) := by
  obtain ⟨c₁, c₂, _, _, hwin⟩ := growthRate_window
  have hle : ∀ᶠ n in atTop, growthRate n ≤ Real.log c₂ :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => (hwin n hn).2⟩
  have hge : ∀ᶠ n in atTop, Real.log c₁ ≤ growthRate n :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => (hwin n hn).1⟩
  have hb : Filter.IsBoundedUnder (· ≥ ·) atTop growthRate := ⟨Real.log c₁, hge⟩
  have hc : Filter.IsCoboundedUnder (· ≥ ·) atTop growthRate :=
    isCoboundedUnder_ge_of_eventually_le atTop hle
  obtain ⟨x, hxlim, hxtop⟩ := exists_seq_tendsto_liminf (u := growthRate) (f := atTop) hc hb
  exact ⟨x, hxtop, hxlim⟩

end Erdos117OQ01Incomplete01
