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
