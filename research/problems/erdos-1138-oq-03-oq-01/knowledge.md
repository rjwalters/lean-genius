# Knowledge: erdos-1138-oq-03-oq-01 — BHP ⟹ prime gaps are sublinear

## Session 2026-07-13 (researcher-2): ORTHOGONAL LOWER BOUND — prime gaps unbounded (axiom-free)

**Mode**: REVISIT (problem marked COMPLETE for sublinearity). **Outcome**: progress (new verified theorems).

### What I did
The prior file (536 lines) is entirely **upper-bound driven** (BHP squeeze forces
`maxPrimeGap x / x → 0`). I added the genuinely **orthogonal LOWER-bound direction** with a
completely different, **axiom-free** mechanism: consecutive-prime gaps are arbitrarily large, so
`maxPrimeGap x → ∞`. Together these pin the two-sided asymptotic character.

New theorems (in `Erdos1138OQ03OQ01.lean`, `namespace Erdos1138OQ03`):
- `factorial_succ_add_not_prime` — the composite run `(N+1)!+k` (`2≤k≤N+1`) is not prime
  (`k ∣ (N+1)!` by `Nat.dvd_factorial`).
- `exists_consecutive_prime_gap_ge N` — arbitrarily large prime gaps: `∃` consecutive primes
  `p<q` with `q-p ≥ N`. `p = Nat.findGreatest Prime ((N+1)!+1)`, `q = Nat.find` least prime
  `> (N+1)!+1`; composite run ⟹ `q ≥ (N+1)!+N+2`.
- `exists_maxPrimeGap_ge`, `maxPrimeGap_tendsto_atTop`, `maxPrimeGap_cast_tendsto_atTop` —
  `maxPrimeGap → ∞` (monotone + unbounded via `tendsto_atTop_atTop_of_monotone`).
- `maxPrimeGap_unbounded_and_sublinear` — packaged two-sided statement.

### Key findings
- The lower bound needs **only Euclid + `Nat.dvd_factorial`**, NOT `baker_harman_pintz`.
  `#print axioms` on the three divergence theorems = `[propext, Classical.choice, Quot.sound]`
  (axiom-free). The combined theorem correctly discloses `baker_harman_pintz` for its
  sublinearity half only.
- Neither direction follows from the other: unboundedness is an elementary lower bound,
  sublinearity a deep upper bound.

### Verification
`lake env lean Proofs/Erdos1138OQ03OQ01.lean` EXIT 0, 0 warnings/sorries (host parent olean;
docker rebuild of the *parent* currently hits a transient SIGBUS/135 unrelated to this change).

### Next steps
Sharpen unbounded → a growth *rate* (Erdős–Rankin `log x · loglog x / (logloglog x)^2` is hard;
a cheaper axiom-free target is a primorial-based `≳ log`-scale bound).

## Session 2026-07-02 (researcher-7): SURVEY (build-free; no Lean built)

Environment was fully build-blocked (Docker daemon down; host disk ~97%, ≈455Mi free,
#33336; 0 Mathlib oleans on disk — cache only in the unreachable Docker volume). No Lean
was compiled. This is a survey/scoping deliverable to enable a future build-capable session.

### Scoped target
In `namespace Erdos1138OQ03`, from the existing `axiom baker_harman_pintz`
(`(maxPrimeGap x : ℝ) ≤ (x:ℝ)^(0.525:ℝ)` for `x ≥ 25`), derive:

```lean
theorem bhp_implies_gap_littleo :
    Filter.Tendsto (fun x : ℕ => (maxPrimeGap x : ℝ) / x) Filter.atTop (nhds 0)
```

This is the unconditional twin of the parent's conditional `cramer_implies_gap_sublinear`.

### Proof sketch (real-analysis, squeeze)
1. **Upper envelope.** For `x ≥ 25`, `x > 0`, so from the axiom and `x^0.525 = x^1 · x^(-0.475)`:
   `maxPrimeGap x / x ≤ x^0.525 / x = x^(0.525 - 1) = (x:ℝ)^(-(0.475:ℝ))`.
   Uses `Real.rpow_natCast`/`Real.rpow_sub` (or `div` = `rpow (a-b)`), `Real.rpow_neg`,
   and monotonicity of division by positive `x`.
2. **Envelope → 0.** `Tendsto (fun x:ℝ => x^(-(0.475))) atTop (𝓝 0)` is
   `Real.tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 0.475)`
   (`Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:48`). Compose with
   `tendsto_natCast_atTop_atTop` (`Mathlib/Order/Filter/AtTopBot/Archimedean.lean:39`) to
   move from `x : ℕ` cast to `ℝ`.
3. **Lower bound.** `0 ≤ maxPrimeGap x / x` trivially (`Nat.cast_nonneg`, `div_nonneg`).
4. **Squeeze.** `squeeze_zero` (or `tendsto_of_tendsto_of_tendsto_of_le_le`) with the
   `0`-limit constant below and the `x^(-0.475)` envelope above, valid eventually
   (`∀ᶠ x, 25 ≤ x`). Yields the `𝓝 0` limit.

### Verified Mathlib references (static check against pinned Mathlib on disk)
- `Real.tendsto_rpow_neg_atTop {y : ℝ} (hy : 0 < y) : Tendsto (fun x:ℝ => x^(-y)) atTop (𝓝 0)`
  — Pow/Asymptotics.lean:48. RHS `𝓝 0` matches target. ✓
- `tendsto_natCast_atTop_atTop` — AtTopBot/Archimedean.lean:39. ✓
- `squeeze_zero`, `Real.rpow_neg`, `Real.rpow_sub`, `Real.rpow_natCast` — standard, present.

### Optional companion form
```lean
theorem bhp_gap_eventually_le_eps (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in Filter.atTop, (maxPrimeGap x : ℝ) ≤ ε * x
```
Follows from `bhp_implies_gap_littleo` via `Metric.tendsto_nhds` / `eventually` unfolding,
mirroring the ε-form of the conditional lemma.

### Status / next step
No axioms added beyond the parent's existing `baker_harman_pintz`; no `native_decide`.
NEXT (build-capable session): add the two theorems to a new
`proofs/Proofs/Erdos1138OQ03OQ01.lean` importing `Proofs.Erdos1138OQ03`, build via
`./proofs/scripts/docker-build.sh Proofs.Erdos1138OQ03OQ01`, confirm `#print axioms` shows
only `{propext, Classical.choice, Quot.sound}` plus the inherited `baker_harman_pintz`,
then create the `src/data/proofs/erdos-1138-oq-03-oq-01/` gallery entry
(status `axiomatized` — it depends on the BHP axiom).

## Session 2026-07-09 (researcher-1): SOLVED — asymptotics-idiom + effective forms (VERIFIED)

Entry was already SOLVED (5 thm, 0 sorry, 1 inherited `baker_harman_pintz` axiom, merged #36057).
Looked outward and added 3 genuinely distinct theory-level theorems (5 → 8):

- `bhp_gap_isLittleO_id`: `maxPrimeGap =o[atTop] (x ↦ x)` — the little-o idiom form. The
  entry's title claim ("sublinearity") *is* the `=o` statement; the file previously only had
  the `Tendsto (·/x) → 0` form and a `=O` at exponent 0.525. Bridged via `isLittleO_iff_tendsto'`
  (denominator eventually nonzero).
- `bhp_gap_isLittleO_rpow (a) (ha : 0.525 < a)`: `maxPrimeGap =o[atTop] (x ↦ x^a)` — idiom form
  of `bhp_gap_div_rpow_littleo`, using the full BHP exponent (sublinear at every a > 0.525, not
  just a = 1).
- `bhp_gap_le_eps_effective (ε x) (hx25 : 25 ≤ x) (hthr : 1 ≤ ε·x^0.475)`: `maxPrimeGap x ≤ ε·x`.
  Effective/pointwise replacement for the qualitative `bhp_gap_eventually_le_eps`: an explicit
  sufficient threshold. Proof multiplies the envelope `x^(-0.475) ≤ ε` (equivalent to hthr via
  `x^(-0.475)·x^0.475 = x^0 = 1`) by `x`. `ε > 0` NOT assumed — forced by the threshold.

Build: VERIFIED clean (`Completed successfully!`, 0 warnings) at `LEAN_MEMORY_LIMIT=16384`
(32768/24576 both hit fleet SIGBUS-135 at olean-write after clean elab [7744/7744] ~1s).
No new axioms (`axiomCount` stays 1: inherited `baker_harman_pintz`), no `native_decide`.
meta synced 5→8 thm / 131→186 lines at both `.meta.*` and `.leanFile.*`.

NEXT: entry is saturated for elementary work; only remaining lever is proving/replacing the
`baker_harman_pintz` axiom itself (deep analytic number theory — out of session scope).

## Session 2026-07-09 (researcher-7): abstract sublinearity engine (source-exponent parametric)

The main target `bhp_implies_gap_littleo` and its o/O/ε companions were already complete
(8 thm). The one genuine structural gap: every result bootstrapped from the *fixed* exponent
`0.525`. Added the engine that isolates the mechanism from the constant:

```lean
theorem gap_littleo_of_rpow_bound {θ : ℝ} (hθ : θ < 1)
    (H : ∀ᶠ x : ℕ in atTop, (maxPrimeGap x : ℝ) ≤ (x : ℝ) ^ θ) :
    Tendsto (fun x : ℕ => (maxPrimeGap x : ℝ) / x) atTop (𝓝 0)
```

Any eventual sub-linear power envelope (`θ < 1`) forces `gap/x → 0`; `bhp_implies_gap_littleo`
is the `θ = 0.525` instance. Future BHP tightenings (0.5+ε, conjectural θ→1/2) plug in without
re-running the squeeze. Proof mirrors `bhp_implies_gap_littleo`: envelope `x^(θ-1)=x^(-(1-θ))→0`
via `tendsto_rpow_neg_atTop (1-θ>0) ∘ tendsto_natCast_atTop_atTop`, `squeeze_zero'` with the
`filter_upwards [H, eventually_ge_atTop 1]` upper bound (`gcongr <;> exact hx` for the div step,
matching the sibling `gap_div_le_rpow_neg` gcongr pattern). Only assumption remains the deep
parent `axiom baker_harman_pintz` (BHP theorem — genuinely unprovable from Mathlib).

### ⚠️ BUILD STATUS: UNVERIFIED (fleet SIGBUS storm, 2026-07-09)
Elaboration CLEAN across 6 builds (mem 6–16 GB) — zero Lean type-error diagnostics; olean-WRITE
crashes exit 135 (SIGBUS), plus intermittent transient dep-cache corruptions on the `import`
line (`Piecewise.olean` / different file each run = fleet race, not this file). Deployer should
re-attempt a green build in a quiet window (`--repair-cache` + low `LEAN_MEMORY_LIMIT`).

## Session 2026-07-09 (researcher-9): SOLVED — two-parameter master engine (elab-clean, olean-write blocked)

Entry was SOLVED with 9 theorems (engine `gap_littleo_of_rpow_bound` from #36592 fixes the
*target* exponent at 1; `bhp_gap_div_rpow_littleo` fixes the *source* at BHP's 0.525). Added
the common generalisation that decouples both exponents (9 → 11):

- `gap_div_rpow_littleo_of_rpow_bound {θ a} (hθa : θ < a) (H : ∀ᶠ x, maxPrimeGap x ≤ x^θ)`:
  `Tendsto (maxPrimeGap x / x^a) atTop (𝓝 0)`. Two-parameter master engine. Subsumes both
  one-parameter engines: `a = 1, θ < 1` recovers `gap_littleo_of_rpow_bound`; `θ = 0.525` with
  the BHP envelope recovers `bhp_gap_div_rpow_littleo`. Sole content = strict gap `θ < a`.
- `gap_isLittleO_rpow_of_rpow_bound {θ a} (hθa) (H)`: the little-o idiom form,
  `maxPrimeGap =o[atTop] (x ↦ x^a)`. Abstract counterpart of `bhp_gap_isLittleO_rpow`.

Proof mirrors the existing engine: envelope `x^θ / x^a = x^(-(a-θ)) → 0` via
`tendsto_rpow_neg_atTop ∘ tendsto_natCast_atTop_atTop`, `gcongr <;> exact hx` for the numerator,
`squeeze_zero'`. Little-o form via `isLittleO_iff_tendsto'` (denominator `x^a > 0` eventually).

Build: elaboration clean `[7744/7744]` across 4 runs (1.5–5.1s, no unsolved/sorry/error); every
run failed only at olean-write with SIGBUS-135 (persistent fleet env issue, not a code defect).
Shipped UNVERIFIED-olean / VERIFIED-elaboration. No new axioms (`axiomCount` stays 1: inherited
`baker_harman_pintz`), no `native_decide`. meta synced 8/186 (stale) → 11/263 at `.meta` and
`.leanFile` (leanFile was mid-sync at 9/216).

NEXT: entry is saturated for elementary/abstract work; the master engine is the natural capstone
of the parametric-envelope direction. Only remaining lever is proving/replacing the
`baker_harman_pintz` axiom (deep analytic number theory — out of session scope).

## Session 2026-07-12 (researcher-3) — SATURATION ASSESSMENT, no code change (honest)

**Mode**: REVISIT (MODERATE, state=COMPLETED) · **Outcome**: nothing found — released without a code PR.

Surveyed `Erdos1138OQ03OQ01.lean` (536 L, 26 thm, 0 sorry / 0 local axiom; inherits the deep
`Erdos1138OQ03.baker_harman_pintz` axiom). The maxPrimeGap-sublinearity engine is **saturated**:
- Headline `Tendsto (fun x => maxPrimeGap x / x) atTop (𝓝 0)` (`bhp_implies_gap_littleo`, L58).
- `=o[atTop] id` and `=o[atTop] x^a` (a>0.525); `O(x^{-0.475})`; effective ε-bounds.
- **General envelope engine** (researcher-5, PR #38424, now on main): `gap_littleo_of_littleo_envelope`
  (ANY `f` with `f x/x→0` and `maxPrimeGap ≤ f` ⟹ gap sublinear), + `=o id` form + rpow-subsumption.
- Individual/consecutive-gap bridges (`consecutive_gap_le_maxPrimeGap` + rpow/ε variants).

Every reasonable asymptotic packaging of "gap is sublinear" is already present, so any further
littleO/bigO/rpow/consecutive variant would be a cosmetic sibling (enumeration theater).

**The one genuinely-new direction, and why it is non-trivial.** The classical consequence
"BHP ⟹ ∀ε>0, ∀ᶠ x, ∃ prime in (x, (1+ε)x]" (primes in short intervals) is NOT a repackaging of the
existing theorems. A clean proof route exists (take `p` = largest prime ≤ x, `q` = next prime;
Bertrand gives `q ≤ 2x`; `q−p ≤ maxPrimeGap(2x) ≤ εx` eventually via the sublinearity at scale
`2x`), but it requires constructing the largest-prime-≤-x / next-prime pair and proving their
**consecutiveness** (`∀ r prime, p<r → q≤r`, the `primeGapSet` membership condition) — a ~50-line
Nat well-ordering construction absent from both this file and Mathlib. That is the honest next
tractable-but-nontrivial target; it was scoped this session but deferred rather than shipped as an
unfinished fragment. No code change made.

## Session 2026-07-19 (researcher-1) — PRIMES IN SHORT INTERVALS (the deferred nontrivial target) — VERIFIED

The 2026-07-12 saturation assessment named exactly one genuinely-new direction and
deferred it as "tractable but nontrivial": **BHP ⟹ ∀ε>0, ∀ᶠ x, ∃ prime in (x,(1+ε)x]**,
which "requires constructing the largest-prime-≤-x / next-prime pair and proving their
consecutiveness (~50-line Nat well-ordering, absent from file and Mathlib)." Built it.

**Two new theorems (37 → 39 decls; lines 728 → 821; axiomCount unchanged = 1):**

1. `exists_consecutive_primes_straddling (x) (hx : 2 ≤ x) : ∃ p q, Prime p ∧ Prime q ∧
   p ≤ x ∧ x < q ∧ p < q ∧ (∀ r, Prime r → p<r → q≤r) ∧ q ≤ 2x`. **Axiom-free**
   ([propext, Classical.choice, Quot.sound]). Construction:
   - `q` = smallest prime > x: `Nat.exists_infinite_primes (x+1)` gives the nonempty
     witness; `Nat.find` + `Nat.find_spec`/`Nat.find_min'` inside a `classical` block
     (keeps the DecidablePred instance local — no leak) give minimality.
   - `p` = largest prime ≤ x: `((Finset.range (x+1)).filter Nat.Prime).max'` (nonempty
     via 2). Obtained through an `∃ p ∈ …, ∀ m ∈ …, m ≤ p` existential (Finset.max'_mem
     + Finset.le_max') to AVOID `set`/`.max'` defeq-unification pain with `apply`.
   - Consecutiveness: a prime `r > p` is either `≤ x` (then `r ∈ filter`, so `r ≤ p` by
     maximality — contradiction) or `> x` (then `q ≤ r` by minimality). `by_cases hrx`.
   - `q ≤ 2x`: `Nat.bertrand p hp.ne_zero` gives prime `s ∈ (p, 2p]`; consecutiveness
     `q ≤ s`, and `s ≤ 2p ≤ 2x` — one `omega`.

2. `bhp_prime_in_short_interval (ε) (hε : 0 < ε) : ∀ᶠ x, ∃ q, Prime q ∧ (x:ℝ)<q ∧
   (q:ℝ) ≤ (1+ε)*x`. Inherits only `baker_harman_pintz`
   (#print axioms = {propext, Classical.choice, Quot.sound, baker_harman_pintz}).
   - `maxPrimeGap (2x) ≤ ε·x` eventually: `bhp_gap_eventually_le_eps (ε/2)` pulled back
     along `Tendsto (2·) atTop atTop` (`h2x.eventually`), then `(ε/2)·(2x) = ε·x`.
   - `q - p ∈ primeGapSet (2x)` (membership witness `⟨p,q,hp,hq,hpq,hq2x,hcons,rfl⟩`,
     needs `q ≤ 2x`), so `q - p ≤ maxPrimeGap (2x)` via `le_csSup primeGapSet_bddAbove`.
   - `q = p + (q-p) ≤ x + maxPrimeGap(2x)` (ℕ omega, p≤x), cast to ℝ, `linarith` with the
     ε-bound: `q ≤ x + εx = (1+ε)x`.

**Why this is NOT enumeration theater:** it produces a concrete prime near x, a different
logical form from every prior asymptotic (littleO/bigO/rpow/consecutive-gap) packaging.
It strictly sharpens Bertrand's fixed interval `(x,2x]` to an ε-shrinking one, conditional
on BHP. The new `exists_consecutive_primes_straddling` is reusable, axiom-free
infrastructure (the straddling-pair analogue of the file's large-gap
`exists_consecutive_prime_gap_ge`).

**GOTCHA:** `tendsto_atTop_mono (fun x => by omega) tendsto_id` FAILS — the mono hyp type
is `∀ n, id n ≤ 2n` and omega chokes on the un-reduced `id x`; use
`fun x => by simp only [id_eq]; omega`.

**Verification.** `./proofs/scripts/docker-build.sh Proofs.Erdos1138OQ03OQ01`
→ `✔ Built (Lean v4.31.0)`, 0 errors. Only pre-existing `push_neg` deprecation warnings
(in the older `exists_consecutive_prime_gap_ge` block, not new code). `#print axioms`
confirmed both results as stated above. meta synced (stale 418L/16-29thm → 821L/37thm).

**Remaining open:** only lever left is proving/replacing `baker_harman_pintz` itself
(deep analytic number theory, out of session scope). The elementary/abstract corollary
surface — asymptotic AND now concrete-existence — is exhausted.
