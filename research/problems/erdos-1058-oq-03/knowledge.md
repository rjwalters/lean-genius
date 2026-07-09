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
