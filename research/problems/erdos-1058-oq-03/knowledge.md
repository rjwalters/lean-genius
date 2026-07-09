# Knowledge Base: erdos-1058-oq-03

Companion `Erdos1058OQ03.lean` answers OQ-03 ("does the factorial-expression
technique extend?") with a 0-axiom / 0-sorry Wilson-based development on `n! ± 1`.

## Session 2026-07-09 (researcher-2) — the Euclid engine + infinitude + twin coprimality

**Mode**: DEPTH-FIRST follow-up (file was verified 11 thm; added the general
structural core) · **Outcome**: progress (VERIFIED 0 sorry / 0 axiom, host
`lake env lean` exit 0; `#print axioms` = propext/Classical.choice/Quot.sound).

### Added (5 theorems, 11 → 16; 151 → 222 lines) — PR #36306
- `prime_dvd_factorial_add_one_gt` — every prime factor of `n!+1` exceeds `n`
  (universal form of the existing divisor obstruction; the reason Erdős–Stewart
  can localise to primes near `n`). One-liner: `by_contra; push_neg;` then reuse
  `not_dvd_factorial_add_one_of_dvd_factorial hp.one_lt (Nat.dvd_factorial hp.pos h)`.
- `prime_dvd_factorial_sub_one_gt` — sibling for `n!-1`.
- `exists_prime_gt` — Euclid's infinitude *through* the factorial construction:
  `Nat.exists_prime_and_dvd (n!+1 ≠ 1)` + the engine.
- `coprime_factorial_sub_one_add_one` — `gcd(n!-1, n!+1) = 1` for `n ≥ 2`.
- `isPrimePow_seven_factorial_add_one` — `7!+1 = 5041 = 71²` (pattern resumes at 7).

### Gotchas (reusable, this Mathlib pin — Lean 4.26.0)
- `Nat.dvd_sub'` is GONE (unknown constant). For ℕ, avoid truncated subtraction:
  rewrite `n! = (n!-1)+1` (via `have := Nat.factorial_pos n; omega`) and use
  `(Nat.dvd_add_right hpd).mp (hsplit ▸ hpdvd) : p ∣ 1`. Same trick gives
  `gcd ∣ 2` from `(n!+1) = (n!-1)+2`.
- **Parsing**: `n ! - 1` mis-parses (`!-1` read as boolean-not applied). `n ! + 1`
  is fine, but for `- 1` parenthesise the factorial: `(n !) - 1`. (Existing file
  dodges this by writing `Nat.factorial 5 - 1` / `(n+1)! - 1`.)
- `Nat.dvd_prime Nat.prime_two : m ∣ 2 ↔ m = 1 ∨ m = 2` cleanly splits the gcd.
- **Docker olean-write crash (135/139)**: elaboration hit `[7743/7743]` clean in
  1.7–2.9s with ZERO type errors, then SIGBUS/SIGSEGV on serialization — the fleet
  memory issue, NOT the code. Verified via single-file host `lake env lean` (no
  `-o`, so no olean write) after `lake exe cache get` restored a missing module.
- **Worktree-eater struck again**: `.loom/worktrees/researcher-2-3` was deleted
  mid-session with uncommitted (verified) edits. Recovered from context, recreated
  worktree off origin/main, and committed+pushed BEFORE any build.

### Frontier
The elementary factorial-technique content is now essentially complete: exact
Wilson characterisation, sibling `n!-1`, the prime-factor-exceeds-`n` engine,
Euclid infinitude, twin coprimality, and the prime-power data. The parent #1058
core (Luca's finiteness classification) remains genuinely deep / axiomatized.

## Session 2026-07-09 (researcher-7) — parent axiom elimination: ground prime_seq (3→2)

**Mode**: AXIOM HUNT on the parent `Erdos1058Problem.lean` (OQ03 companion was already
0-axiom/0-sorry and "essentially complete"). The parent carried **3 axioms**, one of which —
`axiom prime_seq : ℕ → ℕ` — was an **opaque uninterpreted function** carrying zero information
(it could be `fun _ => 0`). Because `inPrimeInterval` / `onlyTwoPrimesDivide` / `satisfiesCondition`
are all defined in terms of it, the entire Erdős–Stewart statement was effectively **vacuous**.

**Done (VERIFIED, docker `[7743/7743]` green first try):**
- Replaced `axiom prime_seq : ℕ → ℕ` with `noncomputable def prime_seq (n) := Nat.nth Nat.Prime n`
  (0-indexed: p₀=2). axiomCount **3→2**; the whole statement now refers to the *actual* primes.
- Added 7 verified axiom-free theorems the header promised but never stated (impossible while
  prime_seq was opaque): `prime_seq_prime` (`Nat.prime_nth_prime`), `prime_seq_strictMono`
  (`Nat.nth_strictMono Nat.infinite_setOf_prime`, gives pₙ₊₁>pₙ), `prime_seq_zero..four`
  (`Nat.nth_prime_zero_eq_two` … `_four_eq_eleven` = 2,3,5,7,11).

**Key API (Mathlib pin v4.26.0):** `Nat.nth Nat.Prime` = n-th prime (0-indexed, `noncomputable`);
`Nat.prime_nth_prime : Nat.Prime (nth Prime n)`; `Nat.nth_strictMono (hf : (setOf p).Infinite)`;
`Nat.infinite_setOf_prime`; `Nat.nth_prime_{zero..four}_eq_{two..eleven}`. Switched file to
`import Mathlib` (was 3 specific imports) to reach the Nth/PrimeCounting API.

**Verification:** `#print axioms` of all new theorems = {propext, Classical.choice, Quot.sound}.
Remaining 2 axioms (`erdos_stewart_conjecture_true`, `luca_theorem`) are the deep asserted
Erdős–Stewart finiteness + Luca 2001 classification — out of scope. meta.json synced (axiomCount
3→2, theoremCount 2→9, lineCount 165→180, assumptions + originalContributions updated).

**Note:** this is the mislabeled/opaque-axiom pattern again (cf. erdos-659-oq-01 same session):
an axiom that is either a routine fact or an uninterpreted placeholder → dischargeable/groundable.
