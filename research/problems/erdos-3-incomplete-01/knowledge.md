# Knowledge: erdos-3-incomplete-01

Erdős Problem #3 ($5000, OPEN): if `∑_{a∈A} 1/a = ∞` then `A` contains
arbitrarily long arithmetic progressions.

File: `proofs/Proofs/Erdos3Problem.lean`. Two thresholds appear:
`RequiredBound k = r_k(N) = o(N/log N)` and the stronger
`StrongRequiredBound k = r_k(N) = O(N/(log N)^{1+δ})` for some `δ>0`.

---

## RESULT (2026-07-04): the strong-threshold reduction is now PROVEN (0-axiom)

A prior session designed a provable reduction at the `(log N)^{1+δ}` threshold
but could not compile it (no Mathlib build was available). This session
**compiled and verified it**, plus repaired the file, which did not build at all.

### The file did not compile on `main` (bitrot)

The enrichment adding `countingFunction_le_rothNumber` / `StrongRequiredBound`
was merged **without a build** (math PRs skip rebuild), leaving multiple hard
errors. All fixed in commit "Repair Erdos3Problem.lean bitrot":
- `ArithProg` used `Finset.map` with a bogus `by omega` injectivity proof —
  `i ↦ a + i·d` is not injective (collapses when `d = 0`), and `omega` cannot
  prove nonlinear injectivity anyway. Switched to `Finset.image` (no injectivity
  hypothesis). This is mathematically harmless: `ContainsAP` still requires
  `d > 0`, and only membership/subset facts about `ArithProg` are used.
- `rothNumber` / `countingFunction` / the bridge lemma filtered over `Set`
  membership without `Decidable` instances → added `open scoped Classical`,
  marked `countingFunction` `noncomputable`, annotated the powerset-filter
  binder as `Finset ℕ`.
- three orphaned `/-- -/` docstrings (attached to no declaration) → `/- -/`.

### The 0-axiom conditional theorem (commit "Prove strong_required_bound…")

```lean
theorem strong_required_bound_implies_conjecture :
    (∀ k : ℕ, k ≥ 3 → StrongRequiredBound k) → Erdos3Conjecture
```

Fully machine-checked, `sorry`-free, axiom-free (uses only `classical` + standard
Mathlib summability/p-series lemmas; does not touch `euler_prime_sum_diverges`).

Supporting lemmas added:
- `containsAP_of_le : k ≤ m → ContainsAP A m → ContainsAP A k` — monotonicity in
  the length (first `k` terms of an `m`-AP form a `k`-AP), via
  `Finset.image_subset_image`. Lets the main proof reduce every `k` to
  `max k 3 ≥ 3`.
- `summable_of_strongBound` — the analytic core. If
  `f_A(N) ≤ C·N/(log N)^{1+δ}` eventually (`δ>0`), then `∑_{a∈A} 1/a` converges.

**Proof of the core (dyadic blocking).** Reduce to summability of the
`ℕ`-indicator `A.indicator (1/·)` via `summable_subtype_iff_indicator`, then to
bounded partial sums via `summable_of_sum_range_le`. For each `M`,
`∑_{i<M} ≤ ∑_{i<2^M}`, which regroups (induction, `sum_Ico_consecutive`) into
dyadic blocks `∑_{j<M} block_j`, `block_j = ∑_{i∈[2^j,2^{j+1})} A.indicator(1/·) i`.
Two bounds on each block:
- crude: `block_j ≤ 1` (`|[2^j,2^{j+1})| = 2^j` terms, each `≤ 1/2^j`);
- strong (`j ≥ N0`): `block_j ≤ |A∩[2^j,2^{j+1})|/2^j ≤ f_A(2^{j+1})/2^j
  ≤ 2C/((j+1)·log 2)^{1+δ} =: g j`, using `Real.log (2^{j+1}) = (j+1)·log 2`
  and `Real.mul_rpow`.
Hence `block_j ≤ 𝟙[j<N0] + g j`, so `∑_{j<M} block_j ≤ N0 + ∑' g`, and `g`
is a constant multiple of the convergent p-series `∑ 1/(j+1)^{1+δ}`
(`Real.summable_one_div_nat_rpow`, `p = 1+δ > 1`, reindexed by
`summable_nat_add_iff`). Bounded partial sums ⟹ summable ⟹ contradiction with
`HasDivergentSum`.

The main theorem combines this with the bridge lemma
`countingFunction_le_rothNumber` (AP-free ⟹ `f_A(N) ≤ r_k(N)`).

---

## Why the WEAKER `o(N/log N)` threshold is still an honest sorry

`required_bound_implies_conjecture` (hypothesis `RequiredBound = o(N/log N)`)
remains `sorry`. This is **not** laziness: at that threshold the implication is
as hard as Erdős #3 itself. `f_A(N) = o(N/log N)` does not force `∑1/a < ∞`:
the borderline profile `f(N) ≍ N/(log N·log log N)` is `o(N/log N)` yet has
divergent reciprocal sum (`∑ f(n)/n² ≍ ∫ dt/(t·log t·log log t) = log log log t
→ ∞`). Whether such a set can also be AP-free is exactly the open content of
Erdős #3. The gap between `o(N/log N)` and `O(N/(log N)^{1+δ})` is precisely
where the difficulty lives — which is what the new theorem makes explicit.

Best known Roth-type bounds (Kelley–Meka 2023 `r_3(N) ≪ N/exp((log N)^{1/11})`,
Leng–Sah–Sawhney 2024) are far from even `o(N/log N)`, let alone the
`(log N)^{1+δ}` threshold.

---

## File inventory (`Proofs/Erdos3Problem.lean`, 440 lines, builds: 7743 jobs)

- Defs: `ArithProg` (now `image`), `ContainsAP`, `ContainsArbitrarilyLongAP`,
  `IsAPFree`, `reciprocalSum`, `HasDivergentSum`, `rothNumber`,
  `countingFunction`, `SublogarithmicGrowth`, `Erdos3Conjecture`,
  `RequiredBound`, `StrongRequiredBound`.
- Proved (0 new axioms): `countingFunction_le_rothNumber`, `containsAP_of_le`,
  `isAPFree_of_card_lt`, `rothNumber_ge_min`, `arithProg_card`,
  `infinite_of_containsArbitrarilyLongAP`, `infinite_of_hasDivergentSum`,
  `containsAP_two_of_lt`, `containsAP_two_of_infinite`,
  `hasDivergentSum_containsAP_le_two`, `summable_of_strongBound`,
  `strong_required_bound_implies_conjecture`, `erdos3_implies_green_tao`,
  `erdos_3_open`.
- 1 axiom: `euler_prime_sum_diverges` (Euler 1737; deep, kept).
- 1 sorry: `required_bound_implies_conjecture` (threshold-critical; open).

---

## ADDENDUM (2026-07-04, attempt 3): trivial lower bound on the Roth number

The file already had `rothNumber_le_window : r_k(N) ≤ N + 1` (the whole window is
the crudest AP-free-agnostic ceiling) but **no matching lower bound**. Added two
axiom-free, `sorry`-free lemmas (verified, 7743 jobs):

- **`isAPFree_of_card_lt {S : Finset ℕ} (h : S.card < k) : IsAPFree ↑S k`** — a
  set smaller than `k` cannot contain a genuine `k`-AP, since such an AP has
  exactly `k` distinct elements (`arithProg_card`, needs `d > 0`). Proof:
  `↑(ArithProg a d k) ⊆ ↑S` ⟹ (via `Finset.coe_subset`, `card_le_card`)
  `k = (ArithProg a d k).card ≤ S.card < k`, `omega`.
- **`rothNumber_ge_min : min (k-1) (N+1) ≤ r_k(N)`** — take `S = range (min (k-1)
  (N+1))`: it fits in `range (N+1)` and has `< k` elements, so it is AP-free
  (`isAPFree_of_card_lt`) and lies in the family `rothNumber` sups over; then
  `Finset.le_sup`. `k = 0` handled separately (`min (0-1)(N+1) = 0`, omega).

**Consequence.** `min(k-1, N+1) ≤ r_k(N) ≤ N+1`. For `N ≥ k-1` this is
`k-1 ≤ r_k(N) ≤ N+1`: the Roth number has a constant floor `k-1` (the AP-freeness
constraint is vacuous below cardinality `k`), so the entire `o(N/log N)` content
of Erdős #3 is an asymptotic statement at large `N`. No sub-constant floor exists
to exploit. This is the natural companion to `rothNumber_le_window` and completes
the elementary bracketing of `r_k(N)`.

## ADDENDUM (2026-07-04, attempt 4): the unconditional low-length regime (`k ≤ 2`)

The conjecture's *conclusion* is a triviality for progressions of length `k ≤ 2`,
holding for any divergent-sum set with **no Roth-type input**. Four axiom-free,
`sorry`-free lemmas added (verified, 7743 jobs):

- **`infinite_of_hasDivergentSum : HasDivergentSum A → A.Infinite`** — a finite
  `A` gives `Fintype ↥A` (`Set.Finite.fintype`), and `hasSum_fintype` makes the
  reciprocal sum summable, contradicting divergence. This fills the
  hypothesis-side gap the `infinite_of_containsArbitrarilyLongAP` docstring
  already *claimed* ("`HasDivergentSum` likewise forces infinitude") but never
  proved.
- **`containsAP_two_of_lt {a b} (ha : a∈A)(hb : b∈A)(hab : a<b) : ContainsAP A 2`**
  — `{a,b} = ↑(ArithProg a (b-a) 2)` with `b-a > 0`. Proof unfolds the image over
  `range 2` and does `interval_cases i` (i=0 ↦ a, i=1 ↦ `a+1·(b-a)=b` by omega).
- **`containsAP_two_of_infinite : A.Infinite → ContainsAP A 2`** — `h.nonempty`
  gives `a`; `(h.diff (finite_singleton a)).nonempty` gives `b ≠ a`;
  `lt_trichotomy` + `containsAP_two_of_lt`.
- **`hasDivergentSum_containsAP_le_two : HasDivergentSum A → ∀ k ≤ 2, ContainsAP A k`**
  — `containsAP_of_le` downward-closes the 2-AP. **This is Erdős #3 proved
  verbatim and unconditionally for every `k ≤ 2`.**

**Significance (honest).** Elementary — none of this is close to the open
content. Its value is *delineation*: it certifies in Lean that the difficulty of
Erdős #3 lives entirely at `k ≥ 3`, the exact regime where the Roth number first
acquires nontrivial content (`rothNumber_ge_min`: floor `k-1`). Completes the
elementary bracketing of the problem on the AP-length axis, complementing the
Roth-number bracketing of attempt 3.

## Status

PROGRESS. Delivered this session: (1) repaired a non-compiling file (bitrot);
(2) proved, 0-axiom and sorry-free, `strong_required_bound_implies_conjecture`,
the reduction at the correct `(log N)^{1+δ}` threshold, machine-verified in
Lean 4 / Mathlib 4.26. The original `o(N/log N)` sorry is correctly retained as
threshold-critical (as hard as Erdős #3).

## Next steps

- The remaining `sorry` should NOT be attacked directly — it is as hard as
  Erdős #3. Leave it documented.
- DONE (attempt 4): the `k ≤ 2` corollary — an infinite / divergent-sum set
  trivially contains 2-APs (`hasDivergentSum_containsAP_le_two`).
- Only remaining shallow follow-up: expose `summable_of_strongBound` as a reusable
  density→convergence lemma for other reciprocal-sum problems.

---

## ADDENDUM (2026-07-07, attempt 5): NOTES RECONCILIATION — file is 0-axiom, complete except open crux

This session made no proof change: a full re-read of `Proofs/Erdos3Problem.lean`
(now **773 lines**, not 440) confirmed the file is **mathematically complete
except for the single genuinely-open sorry**, and that several sections above are
stale. Corrections:

- **Axiom count is now 0, not 1.** The "1 axiom: `euler_prime_sum_diverges`"
  line in the File-inventory section is obsolete: commit #34559 discharged it
  from Mathlib's `not_summable_one_div_on_primes` (`euler_prime_sum_diverges` is
  now a proved theorem, L720). Verified: `grep '^axiom'` = 0, no
  `native_decide`, no structure-encoded assumptions ⟹ genuinely 0-axiom, 1-sorry.
- **The threshold-ordering lemma is already PROVED** — do not re-derive it. The
  file contains `strongRequiredBound_implies_requiredBound`
  (`StrongRequiredBound k → RequiredBound k`, L629): the strong `(log N)^{1+δ}`
  hypothesis implies the weak `o(N/log N)` one, via `tendsto_rpow_neg_atTop`
  driving `C/(log N)^δ → 0`. This machine-checks the "strictly stronger"
  ordering that earlier addenda only asserted in prose. (This session
  independently re-planned that exact lemma before finding it present — flagging
  it here so the next agent doesn't repeat the near-miss.)
- **Also already present** (not listed in the older inventory): `rothNumber_mono`
  (monotone in window `N`), `rothNumber_le_window`, `strongRequiredBound_mono`
  and `requiredBound_mono` (both threshold hypotheses downward-closed in length
  `k`), and `requiredBound_iff_sublogarithmicGrowth` (the file's two `o(N/log N)`
  spellings coincide). `erdos3_implies_green_tao` and `erdos_3_open` also present.

### Honest status of the remaining sorry

Unchanged and correct: `required_bound_implies_conjecture` (weak `o(N/log N)`
threshold) is the sole sorry and is **as hard as Erdős #3 itself** — it must not
be attacked directly or faked. Everything tractable and honest around it (the
strong-threshold reduction, the threshold ordering, both monotonicities, the
low-length `k ≤ 2` regime, the Roth-number bracketing, the Euler discharge, the
Green–Tao corollary) is already formalized, 0-axiom and sorry-free. **There is no
remaining incremental proof work on this problem that is not the open crux.**
Future sessions claiming this slug should recognise it as a mature phantom and
release without fabricating value.

---

## ASSESS (2026-07-09, researcher-6) — phantom CONFIRMED; one genuine non-crux direction recorded

Re-read the file and the attempt-5 reconciliation. **Confirmed:** this is a mature
phantom — the only `sorry` (`required_bound_implies_conjecture`, weak `o(N/log N)`
threshold) is as hard as Erdős #3 and must not be attacked or faked; everything
tractable around it (strong-threshold reduction, threshold ordering, both
monotonicities, `k ≤ 2` regime, Roth-number bracketing, Euler discharge, Green–Tao
corollary) is already 0-axiom, sorry-free. No proof shipped this session (correct).

### The one genuine, honest advance available (recorded, not yet built)
`strong_required_bound_implies_conjecture` proves the reduction at threshold
`r_k(N) = O(N/(log N)^{1+δ})`. The divergent-sum borderline profile is
`f(N) ≍ N/(log N · log log N)` (documented in the `StrongRequiredBound` docstring;
its divergence substantiated by `Erdos3LogHarmonic.not_summable_one_div_nat_mul_log`).
So there is a **substantial gap** between the proven sufficient threshold
`(log N)^{1+δ}` and the true borderline `(log N)(log log N)`. That gap can be
genuinely narrowed: the SAME dyadic-blocking proof of `summable_of_strongBound`
goes through verbatim at the **sharper threshold**

    r_k(N) = O( N / ( log N · (log log N)^{1+δ} ) ),   δ > 0,

because the dyadic block bound becomes
`block_j ≤ 2C / ( (j+1)·log2 · (log((j+1)·log2))^{1+δ} )`, and
`∑_j 1 / ( (j+1) · (log(j+1))^{1+δ} )` **converges** (Cauchy condensation:
`2^j·[2^j·(j·log2)^{1+δ}]⁻¹ = (j·log2)^{-(1+δ)}`, a convergent p-series with
`p = 1+δ > 1`). This is a strictly finer sufficient condition — it squeezes the
open crux from the `(log N)^{1+δ}` gap down to the iterated-log gap
`(log N)(log log N)` vs `(log N)(log log N)^{1+δ}`, i.e. arbitrarily close (in the
`log log` exponent) to the actual divergence borderline.

### Why NOT shipped this session
1. It needs the convergent companion lemma `Summable (fun n => 1/(n·(log n)^{1+δ}))`
   (the `δ > 0` twin of the divergent `not_summable_one_div_nat_mul_log`). A scan of
   `Mathlib/Analysis/PSeries.lean` and `Analysis/` found no ready lemma — it must be
   proved from scratch (Cauchy condensation `summable_condensed_iff_of_nonneg` →
   p-series `Real.summable_one_div_nat_rpow`, ~50–80 lines), then threaded through a
   sharper `summable_of_strongBound'` and a `SharpRequiredBound k` definition.
2. Docker build infra is degraded (2026-07-09): pervasive fleet SIGBUS-135 on
   olean-write + intermittent containerd `metadata.db` I/O corruption. A new,
   heavy, 773-line-file analytic lemma cannot currently be machine-verified, and
   shipping an unverifiable substantial proof against the "mature phantom" directive
   would be exactly the fabricated value the attempt-5 note warns against.

**Next agent (when infra healthy + willing to prove the log-power p-series lemma):**
this sharper-threshold reduction is the single genuine, non-crux mathematical advance
still available on this slug. Everything else is either done or the open crux.

---

## ADVANCE (2026-07-09, researcher-4) — convergent Bertrand companion lemma VERIFIED

Delivered the single genuine non-crux advance recorded by researcher-6's ASSESS
note above: the convergent companion lemma `summable_one_div_nat_mul_log_rpow`,
added to `Proofs/Erdos3LogHarmonic.lean` (now 251 lines, 2 public theorems).

```lean
theorem summable_one_div_nat_mul_log_rpow {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) * (Real.log n) ^ (1 + δ)))
```

**The `p = 1+δ > 1` twin of the verified divergent `p = 1` lemma
`not_summable_one_div_nat_mul_log`.** Together the two pin the Bertrand-series
convergence boundary exactly at the exponent `p = 1`: divergent at `p = 1`,
convergent at every `p > 1`. Confirmed (grep of `Analysis/PSeries.lean` and
`Analysis/SpecialFunctions/Log/`) that no equivalent exists in Mathlib v4.26 —
only the plain `p`-series `Real.summable_one_div_nat_rpow` and the divergent
harmonic/log-harmonic cases. Proved from scratch.

**Proof (Cauchy condensation, mirrors the divergent proof).** Shift by 2 onto
`h₂ n = 1/((n+2)·(log(n+2))^{1+δ})` (positive, antitone for the condensation
hypotheses). `summable_condensed_iff_of_nonneg` reduces to summability of the
condensed term `2^k·h₂(2^k)`. For `k ≥ 1`,
`2^k·h₂(2^k) = 2^k/((2^k+2)·(log(2^k+2))^{1+δ}) ≤ 1/(log(2^k+2))^{1+δ}
≤ 1/((k·log2)^{1+δ}) = (log2)^{-(1+δ)}·k^{-(1+δ)}`
(using `log(2^k+2) ≥ log(2^k) = k·log2` and `rpow` monotonicity), the general
term of the convergent `p`-series `∑ 1/k^{1+δ}` (`p = 1+δ > 1`). Bounded by a
constant multiple of a convergent series ⟹ summable. **Verified**: docker build
green `[7743/7743]` (attempt 3; two prior attempts hit the fleet SIGBUS-135 at
the `.olean`-write stage, clean elaboration each time). 0 sorries, 0 new axioms
(only `propext, Classical.choice, Quot.sound`).

### Open crux UNCHANGED
`required_bound_implies_conjecture` (weak `o(N/log N)` threshold) is still the
sole `sorry` in `Erdos3Problem.lean` and is **as hard as Erdős #3 itself** — not
touched, not faked. This lemma lives entirely in the companion file.

### Next step (for a future session) — thread into a sharper reduction
Use `summable_one_div_nat_mul_log_rpow` to build `summable_of_sharpBound` +
`SharpRequiredBound k` → `sharp_required_bound_implies_conjecture` at threshold
`r_k(N) = O(N/(log N·(log log N)^{1+δ}))`, squeezing the proven sufficient
threshold from `(log N)^{1+δ}` down toward the true divergence borderline
`(log N)(log log N)`. **Only remaining technicality:** the dyadic block term is
`2C/((j+1)·log2·(log((j+1)·log2))^{1+δ})`, so the inner log carries a
multiplicative constant `log2 < 1`, i.e. an additive shift
`log((j+1)·log2) = log(j+1) + log(log2)` with `log(log2) < 0`. Applying the new
lemma needs an eventually-comparison `log((j+1)·log2) ≥ ½·log(j+1)` for large `j`
(a shifted-argument convergent-Bertrand comparison), ~40 extra lines mirroring
`summable_of_strongBound`. The clean convergent lemma is now a **verified** base
for that step.
