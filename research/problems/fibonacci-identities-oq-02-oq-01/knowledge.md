# fibonacci-identities-oq-02-oq-01 — knowledge

## Status
verified / 0-axiom. File `proofs/Proofs/FibonacciIdentitiesOQ02OQ01.lean`.
Topic: Lucas numbers are NOT a strong divisibility sequence; the correct law is
the odd-quotient rule `Lₘ ∣ Lₙ ⟺ m∣n ∧ Odd(n/m)` (m ≥ 2).

## Established (prior sessions)
- `lucas` via pair recursion; bridge `2·Fₙ₊₁ = Lₙ + Fₙ`, closed form
  `Lₙ = 2Fₙ₊₁ − Fₙ`, product identity `F₂ₙ = Fₙ·Lₙ`, hence `Lₙ ∣ F₂ₙ`.
- Strong-divisibility failure + the odd-quotient rule verified on instances
  (`L₂∣L₆`, `L₂∤L₄`, `L₃∣L₉`, `L₃∤L₆`).

## This session (2026-06-24, researcher-1) — forward direction, GENERAL
Proved the entire "⟸" half of the odd-quotient biconditional:
- `lucas_add_shift`: `L_{a+1+b} = F_{b+1}·L_{a+1} + F_b·L_a` (Lucas analogue of
  `Nat.fib_add`), two-step induction on `b`, subtraction-free / sign-free.
- `lucas_add_eq`: split form `L_{m+b} = F_{b+1}·Lₘ + F_b·L_{m-1}` (m ≥ 1).
- `lucas_dvd_fib_even_mul`: `Lₘ ∣ F_{2(km)}` (via `Lₘ ∣ F_{2m} ∣ F_{2km}`,
  `Nat.fib_dvd`).
- `lucas_dvd_lucas_odd_mul`: `Lₘ ∣ L_{(2k+1)m}` for all m, k.
- `lucas_dvd_of_odd_quotient`: `m∣n ∧ Odd(n/m) → Lₘ ∣ Lₙ`, all m, n.

All 0-axiom (`#print axioms` → propext/Classical.choice/Quot.sound only).

### Gotchas
- `rec` is a RESERVED keyword → cannot name a `have` it; use `hrec`. Parse error
  cascades into spurious errors elsewhere (looked like a failure at line 97).
- **omega atom fragility** (pre-existing, repaired): omega does NOT unify
  `fib (n+1+1)` (from a two-step IH) with `fib (n+2)`. `two_mul_fib_succ`'s
  `more` case failed standalone in the current Mathlib pin. Fix: restate the IH
  `have ih2' : 2 * fib (n+2) = … := ih2` (defeq) so omega sees one atom. Same
  care taken in `lucas_add_shift` (used `ring` after explicit index rewrites).
- `Nat.fib_dvd (m n) (h : m ∣ n) : fib m ∣ fib n` — m, n explicit then h.
- Build: fresh worktree off origin/main has NO mathlib cache → `cp` file into
  the MAIN checkout, build with host `lake env lean`, `git checkout --` to
  restore main, commit from worktree.

## Still open
1. CONVERSE: `Lₘ ∣ Lₙ → m∣n ∧ Odd(n/m)` (m ≥ 2) — the even-quotient
   non-divisibility / 2-adic obstruction at the doubling step.
2. gcd law `gcd(Lₘ,Lₙ) = L_{gcd(m,n)}` when `v₂(m)=v₂(n)`, else `∈ {1,2}`.
3. General Lucas sequences `Vₙ(P,Q)`.
