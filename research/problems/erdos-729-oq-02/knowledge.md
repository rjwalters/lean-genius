# Knowledge Base: erdos-729-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

## Session 2026-06-15 (researcher-2) — build-error fix in the registered file

**Bug found + fixed:** `Erdos729Problem.lean:96` (`reducedDenominator`, registered at
`Proofs.lean:1888`) had `Classical.choose (⟨1, fun _ => rfl⟩ : ∃ d : ℕ, d > 0)`. The
second component `fun _ => rfl` is a lambda and cannot inhabit the Prop `1 > 0`
(`= Nat.le 1 1`, an inductive, not a function type) — a genuine type error that the
website-only deployer never catches (the Lean aggregate isn't built under the blackout).
Replaced with `Nat.one_pos` (`⟨1, Nat.one_pos⟩`); the replacement proves the same Prop and
is correct independent of whether the original compiled, so the edit is strictly safe. The
def is an unused `noncomputable` placeholder, so semantics are unaffected.

**Axiom assessment (unchanged, all deep / not Mathlib-dischargeable):**
- `legendre_identity` (:153) — Legendre's `v_p(n!)` formula; being discharged in R10's open
  PR **#24474** (do NOT duplicate).
- `erdos_1968_classical` (:72) — Erdős 1968, `a+b ≤ n + O(log n)` (research result).
- `barreto_leeham_theorem`/`barreto_leeham_bound` (:123/:127) — the Barreto–Leeham resolution
  (the open-question's answer; published research, multi-week).
Build-pending verification of the fix (dual blackout: docker exit 124, Aristotle 404).

## Session 2026-07-08 (researcher-6) — axiom-free 2-adic digit-sum bound

**Mode**: REVISIT (MODERATE, phase ACT). **Outcome**: progress (new verified companion).

### What I Did
- Added `proofs/Proofs/Erdos729DigitSumBound.lean` (5 theorems, 0 axioms / 0 sorries,
  green docker build, 7743 jobs; `#print axioms` = {propext, Classical.choice, Quot.sound}).
- Proved the elementary 2-adic core of the parent's Erdős-1968 constraint, which the
  main file only carries as the **deep axiom** `erdos_1968_classical`:
  - `v2_factorial`: `v₂(n!) = n − s₂(n)` (Legendre at p=2).
  - `v2_add_le_of_dvd`: `a!·b! ∣ n! ⟹ v₂(a!)+v₂(b!) ≤ v₂(n!)`.
  - `erdos_two_adic_bound`: **`a + b ≤ n + s₂(a) + s₂(b)`** — sharp, subtraction-free.
  - `digitSum_two_le_log`: `s₂(m) ≤ Nat.log 2 m + 1`.
  - `erdos_two_adic_bound_log`: `a+b ≤ n+(⌊log₂a⌋+1)+(⌊log₂b⌋+1)` (the recognisable log shape).

### Key Findings
- The classical Erdős direction (`a!b!|n! ⟹ a+b ≤ n+O(log n)`) is **elementary and
  axiom-free** in its 2-adic content; only the "mod small primes" (Barreto–Leeham)
  extension is genuinely deep.
- Engine: `Nat.factorization_prime_le_iff_dvd` (factorization monotone under dvd) +
  `Nat.factorization_mul` + `Nat.factorization_def` (= padicValNat at prime) +
  `sub_one_mul_padicValNat_factorial` + `List.sum_le_card_nsmul` + `Nat.digits_len`.
- **Latent soundness note:** the main-file axiom `erdos_1968_classical` is false at
  `n=0` (`a=b=1`: `DividesFactorial 0 1 1` holds since `1·1 ∣ 0!=1`, but the conclusion
  needs `2 ≤ 0 + C·log 0 = 0`). The ℕ-valued `erdos_two_adic_bound` is the correct,
  edge-safe replacement for the classical direction. Left the axiom untouched (out of
  OQ-02 scope; do not overwrite the contested main file).
- Two 135 (SIGBUS, no diagnostic) build flakes before a clean green — volume-corruption
  pattern; retry, don't edit.

### Files Modified
- `proofs/Proofs/Erdos729DigitSumBound.lean` (new)
- `src/data/research/problems/erdos-729-oq-02.json` (knowledge)

### Next Steps
- Sharpen: `s₂(a)+s₂(b)−s₂(n)` = number of base-2 carries adding `a` and `n−a`
  (Kummer); characterize equality `a+b = n + carries`.

## Session 2026-07-08 (researcher-1) — ELIMINATED the unsound parent axiom

**Mode**: REVISIT (RICH, phase ACT). **Outcome**: axiom removed from the registered file.

Completes the step researcher-6 deferred ("Left the axiom untouched … out of OQ-02
scope"). The parent `Erdos729Problem.lean` still shipped the **unsound**
`erdos_1968_classical` (false at `n∈{0,1}`, `Real.log n = 0`; refuted by `a=b=1`).
`Erdos729DigitSumBound.lean` already proved the sound replacements
(`erdos_two_adic_bound`, and `erdos_1968_uniform` — the uniform real-log form,
`C=4/log 2`, `n≥2`), but the parent never adopted them and remained inconsistent.

**This session (VERIFIED host-side, `#print axioms`):**
- `import Proofs.Erdos729DigitSumBound` into the parent.
- **Removed `axiom erdos_1968_classical`.** Parent axioms 3 → 2 (only the deep
  `barreto_leeham_theorem`/`barreto_leeham_bound` remain).
- `erdos_proof_via_powers_of_two` now concludes the sharp `a+b ≤ n+s₂(a)+s₂(b)`
  (re-exports `erdos_two_adic_bound`) — `#print axioms` = {propext, Classical.choice,
  Quot.sound}, i.e. axiom-free.
- `erdos_729_statement`'s first conjunct restated to the sound **uniform** form
  (`∃ C>0, ∀ n a b, 2≤n → …`), discharged by `erdos_1968_uniform`. Depends only on
  `barreto_leeham_theorem` now (no more `erdos_1968_classical`).
- meta.json `erdos-729`: axiomCount 3→2, lineCount →251.

**Build note:** Docker unusable this window — corrupt Mathlib cache
(`HasConicalPullbacks.ir` invalid header) then persistent exit-135 SIGBUS under fleet
memory starvation (~7 attempts). Verified instead on the **host** via
`LAKE_UNSAFE=1 ./bin/lake env lean` against prebuilt Mathlib oleans (compiled the
sibling → its olean, then the edited parent → EXIT 0, then `#print axioms`). See
[[reference-host-verify-light-mathlib-files-cache-get]].

### Terminus
Classical direction now fully axiom-free. Remaining `barreto_leeham_*` axioms are the
genuine open-question answer (published, multi-week) — NOT session-sized. Do not reclaim
for axiom elimination.

## Session 2026-07-08 (researcher-1): eliminate the UNSOUND barreto_leeham_bound axiom [VERIFIED — 1 axiom remains]

**Mode:** AXIOM HUNT. `Erdos729Problem.lean` carried 2 axioms. Inspection showed
`barreto_leeham_bound` was not merely unproven but **unsound** — it asserts a false
proposition:
`∀ C>0, ∃ D>0, ∀ n a b, DividesFactorialModSmall n a b C → a+b ≤ n + D·log n`.
For any `D`, take `n=1, a=b=1`: `k·1!·1! ∣ 1!` forces `k=1` (prime factors of `1` empty, so
`DividesFactorialModSmall 1 1 1 C` holds), yet `a+b = 2 > 1 + D·log 1 = 1`. Same small-`n`
defect the companion already documented for the retired `erdos_1968_classical`. An axiom
asserting `False` makes the file logically inconsistent.

**Fix (2→1 axioms):**
- `DividesFactorialModSmall n a b C` unfolds to `∃ k, (primes of k ≤ C) ∧ k·a!·b! ∣ n!`,
  which already forces `a!·b! ∣ n!` (since `a!·b! ∣ k·a!·b!`, via `k·a!·b! = a!·b!·k` +
  `dvd_mul_right`).
- So the **sound** uniform form (add `2 ≤ n`) is a corollary of the axiom-free
  `Erdos729DigitSum.erdos_1968_uniform` (`C = 4/log 2`). Converted the axiom to a verified
  `theorem barreto_leeham_bound` and tightened `erdos_729_summary`'s second conjunct with
  `2 ≤ n`.
- The deep `barreto_leeham_theorem` (`¬InfinitelyManyExceptions C`, the actual
  Barreto–Leeham "NO" resolution — genuinely open/hard for small `C`) is left as a
  documented axiom.

**Verification:** docker `Built Proofs.Erdos729Problem`; `#print axioms barreto_leeham_bound`
= `{propext, Classical.choice, Quot.sound}` (axiom-free), and `erdos_729_summary` now depends
only on `barreto_leeham_theorem` (the removed axiom no longer appears). File 251→271 lines,
7→8 theorems, 2→1 axioms. meta.json + research metadata synced.

**Note for future work:** the remaining axiom is the deep resolution and is not
session-sized. The elementary axiom-free theory (digit-sum bound, uniform real-log bound,
Legendre identities) is complete across the companion files.

## Session 2026-07-09 (researcher-7) — Kummer at p=2: carry content of (★) (0 new axioms)

**Mode**: ACT (SOLVED-side; executes researcher-6's deferred "Next Steps": characterize
`s₂(a)+s₂(b)−s₂(a+b)` = base-2 carries via Kummer). Parent + companions were at frontier
(1 deep axiom `barreto_leeham_theorem`; elementary theory complete). Added the sharp *carry*
layer under the bound (★) `a+b ≤ n+s₂(a)+s₂(b)`, which prior sessions left as a one-sided
inequality without its equality/slack analysis.

**Added to `Erdos729DigitSumBound.lean` (4 theorems, VERIFIED 0-axiom, docker `[7743/7743]` green):**
- `v2_choose_add_digitSum`: **subtraction-free Kummer at p=2** —
  `v₂(C(a+b,a)) + s₂(a+b) = s₂(a) + s₂(b)`. The valuation term is Kummer's carry count.
- `digitSum_two_add_le`: **binary digit-sum subadditivity** `s₂(a+b) ≤ s₂(a)+s₂(b)` —
  NOT a named lemma in the pinned Mathlib (checked). Immediate corollary (drop v₂ ≥ 0).
- `excess_eq_v2_choose`: the slack of (★) at the extremal `n=a+b` equals `v₂(C(a+b,a))`.
- `choose_odd_iff_digitSum_add`: **no-carry criterion** `¬2∣C(a+b,a) ↔ s₂(a+b)=s₂(a)+s₂(b)`.

**Key findings / API:**
- Mathlib HAS Kummer digit-form `Nat.sub_one_mul_padicValNat_choose_eq_sub_sum_digits'`, but
  only with truncated ℕ-subtraction on the RHS. Proved the subtraction-free additive form
  directly from this file's `v2_factorial` instead: take `padicValNat 2` of the factorial
  identity `C(a+b,a)·a!·b! = (a+b)!` (`Nat.choose_mul_factorial_mul_factorial` +
  `Nat.add_sub_cancel_left`), split via `padicValNat.mul` (needs all factors ≠0), substitute
  Legendre, close with `omega` + three `Nat.digit_sum_le`. Self-contained; omega handles the
  truncated subtractions given `s₂ ≤ n`.
- `dvd_iff_padicValNat_ne_zero hchoose` + `not_not` turns the odd criterion into
  `padicValNat 2 (choose) = 0 ↔ …`, then `omega` off the identity (proves the iff directly).
- `(Nat.choose_pos (Nat.le_add_right a b)).ne'` for `choose (a+b) a ≠ 0`.
- 3× SIGBUS exit-135 at olean-write (elaboration clean `[7743/7743]` 2.5–3.0s, no type
  errors) — fleet memory pressure, not code; retry-loop went green. `#print axioms` build
  also needed a 135 retry (then all 4 = {propext, Classical.choice, Quot.sound}).

### Terminus (unchanged)
Only `barreto_leeham_theorem` (the deep Barreto–Leeham "NO" resolution) remains axiomatized
in the parent — genuinely open/hard, not session-sized. The elementary 2-adic theory now
covers both the bound (★) AND its exact carry-slack characterization.

## Session 2026-07-11 (researcher-1) — filled the delegated digit-sum-one characterization

**Mode**: ACT (SOLVED-side; executes the standing nextAction "prove s_p(n)=1 <-> n=p^k
for general p"). The maximality lemma `sub_one_mul_padicValNat_factorial_eq_pred_iff`
proved `(p-1)·v_p(n!) = n-1 ⟺ s_p(n)=1` but **explicitly delegated** the equivalence
`s_p(n)=1 ⟺ n=p^k` (both here and in the p=2 Kummer companion). Closed that gap.

**Added to `Erdos729LegendrePrimeRecurrence.lean` (5 theorems, VERIFIED 0-axiom
`{propext, Classical.choice, Quot.sound}`, host `lake env lean` EXIT 0):**
- `digitSum_pos` : `m≠0 → 0 < s_p(m)` — nonempty digit list + nonzero top digit
  (`Nat.getLast_digit_ne_zero`) as a lower bound (`List.le_sum_of_mem`).
- `digitSum_prime_pow` : `s_p(p^k)=1` — the easy ⟸ direction via
  `Nat.digits_base_pow_mul` (m=1): `digits p (p^k) = replicate k 0 ++ [1]`.
- `isPow_of_digitSum_eq_one` : the ⟹ direction, strong induction on n using the
  file's own left-shift law `digitSum_prime_mul_add`: `n = p·(n/p)+n%p` forces the
  low digit `n%p ∈ {0,1}`; `n%p=1` ⟹ s_p(n/p)=0 ⟹ n/p=0 (digitSum_pos) ⟹ n=p^0;
  `n%p=0` ⟹ s_p(n/p)=1, recurse (n/p<n) ⟹ n=p^{j+1}.
- `digitSum_eq_one_iff_isPow` : the full iff.
- `sub_one_mul_padicValNat_factorial_eq_pred_iff_isPow` : capstone — maximality of
  v_p(n!) now stated directly as `⟺ ∃k, n=p^k` (no delegated step).

**Key API**: `Nat.digits_base_pow_mul hb hm : digits b (b^k * m) = replicate k 0 ++ digits b m`;
`Nat.digits_of_lt p 1 _ hp : digits p 1 = [1]`; `List.le_sum_of_mem` (member ≤ sum in ℕ).
**GOTCHA**: `rw [← hdecomp]` where `hdecomp : p*(n/p)+n%p = n` rewrites EVERY `n`
(including inside `n/p`, `n%p`) — proving `p*(n/p)=n` this way loops. Instead
`rw [hr0] at hdecomp; simpa using hdecomp`.

### Terminus (unchanged)
Only the deep `barreto_leeham_theorem` axiom in the parent remains. The elementary
p-adic theory (Legendre, Kummer/multinomial carries, digit-sum recurrences, and now
the digit-sum-one ↔ prime-power characterization) is complete and axiom-free.

## Session 2026-07-11 (researcher-5) - Kummer digit-sum form + subadditivity + divisibility criteria

**Mode**: REVISIT (RICH problem, core already solved)
**Outcome**: progress (outward extension, 5 new axiom-free theorems)

### What I Did
- Confirmed the main-file axiom fix (nextStep #1) was already landed: Erdos729Problem.lean is down to 1 axiom (barreto_leeham_theorem only).
- Checked Mathlib v4.26.0: Kummer's theorem IS present (`sub_one_mul_padicValNat_choose_eq_sub_sum_digits`, carries form `padicValNat_choose'`) — so re-proving Kummer would be duplication. Instead extended in directions Mathlib does NOT cover.
- Added 5 axiom-free theorems to `Erdos729LegendreGeneral.lean`, all building on the existing `sub_one_mul_padicValNat_factorial_digitSum`:
  - `sub_one_mul_padicValNat_choose_add_digitSum`: carry-free additive Kummer.
  - `digitSum_add_le`: base-p digit-sum subadditivity (Mathlib gap).
  - `padicValNat_choose_eq_div`: division-form Kummer in gallery digitSum shape.
  - `not_dvd_choose_iff_digitSum_add`: p∤C(m+n,m) ↔ no base-p carries (Mathlib gap).
  - `dvd_choose_iff_digitSum_lt`: p∣C(m+n,m) ↔ ≥1 carry.

### Key Findings
- The subtraction-free additive rearrangement of Kummer is the right engine: subadditivity and both divisibility criteria drop out as one-line `omega` corollaries once digit sums are bounded by their arguments.
- Mathlib genuinely lacks digit-sum subadditivity and the prime-non-divisibility digit-sum criterion; both are general-purpose and upstreamable.

### Verification
- Host `lean` (v4.26.0) elaboration: exit 0, no errors/warnings.
- `#print axioms` on all 5: `[propext, Classical.choice, Quot.sound]` only — axiom-free.
- Docker build: transient SIGBUS-135 at C-codegen phase after a clean 2.3s elaboration (host-lean fallback used to verify).

### Files Modified
- proofs/Proofs/Erdos729LegendreGeneral.lean (+~130 lines, 5 theorems)
- src/data/research/problems/erdos-729-oq-02.json (knowledge)

### Next Steps
- Consider upstreaming `digitSum_add_le` and `not_dvd_choose_iff_digitSum_add` to Mathlib.
- Equality/sharp-boundary case connects to Mathlib's carries-Finset form of Kummer.

## Session 2026-07-12 (researcher-10) — power-of-two characterization (converse of digitSum_two_pow)

**Mode:** REVISIT (RICH, core solved). **Outcome:** progress (3 axiom-free theorems).

Closed the standing open converse flagged after the central-binomial 2-adic session
(PR #38419 had `digitSum_two_pow : s_2(2^k)=1` one-directional; the converse was left open
"for iff"). Added to `Erdos729LegendreGeneral.lean` (after `padicValNat_centralBinom_two_pow`):

- `digitSum_two_eq_one_imp_two_pow : ∀ n, 0 < n → digitSum 2 n = 1 → ∃ k, n = 2^k` — the
  converse. Strong induction on `n` via the digit recurrence `s_2(n) = n%2 + s_2(n/2)`
  (from `Nat.digits_def'`): even ⇒ `s_2(n/2)=1`, recurse, `n=2^{j+1}`; odd ⇒ `s_2(n/2)=0`,
  so `n/2=0` (`digitSum_pos` contrapositive), `n=1=2^0`. omega handles the div/mod and the
  atom-level `0 < digitSum ∧ digitSum = 0` contradiction.
- `digitSum_two_eq_one_iff : 0 < n → (s_2(n) = 1 ↔ ∃ k, n = 2^k)` — full characterization.
- `padicValNat_centralBinom_two_eq_one_iff : 0 < n → (v_2(C(2n,n)) = 1 ↔ ∃ k, n = 2^k)` —
  sharp form of `padicValNat_centralBinom_two_pow`: `C(2n,n)` is even-but-not-div-by-4 iff
  `n` is a power of two (via `padicValNat_centralBinom_two_eq_digitSum`).

**Genuinely new (not filler):** upgrades a one-directional value fact to a full iff /
characterization. The forward `⇐` was known; the `⇒` (single-1-bit ⟹ power of two) was the
missing half and is the content.

### Verification
Host `lean` v4.26.0 elab (Docker SIGBUS-prone): whole file **EXIT 0**, no errors/warnings.
`#print axioms` on all three = `[propext, Classical.choice, Quot.sound]` — axiom-free (no
sorryAx, no ofReduceBool). File 539 → ~600 L. Parent axiom `barreto_leeham_theorem`
(in `Erdos729Problem.lean`) untouched; this general file stays 0-axiom.

### Frontier
The elementary base-2/base-p p-adic theory (Legendre, Kummer additive/carry-count defect,
central binomial `v_2 = s_2`, and now the power-of-two locus of `v_2(C(2n,n))=1`) is
complete and axiom-free. Only the deep parent `barreto_leeham_theorem` remains.
