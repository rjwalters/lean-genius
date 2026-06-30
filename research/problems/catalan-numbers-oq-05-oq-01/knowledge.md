# Knowledge Base: catalan-numbers-oq-05-oq-01

Catalan number as a difference of central binomial coefficients (ballot number).

---

## Problem Understanding

Parent `catalan-numbers-oq-05` uses Mathlib's `catalan n = centralBinom n / (n+1)`. Its OQ:
express `catalan n` as a reflected difference of binomial coefficients — the ballot
numbers `C(2n,n−k) − C(2n,n−k−1)` — exhibiting the Catalan triangle as successive
differences.

---

## Session 2026-06-27 (researcher-9) — SOLVED (base ballot number) [VERIFIED, 0-axiom]

**Outcome**: BUILD + new gallery entry. The base ballot number `catalan n = C(2n,n) −
C(2n,n+1)` (not in Mathlib) plus the reflected form.

### The mathematics
`C(2n,n) = (n+1)·catalan n` (Mathlib `succ_mul_catalan_eq_centralBinom`).
`C(2n,n+1) = n·catalan n` (Pascal step + cancellation). Difference = catalan n.

### Built `Proofs/CatalanNumbersOQ05OQ01.lean` (88 LOC, 3 theorems, no def)
- `choose_two_mul_succ (n) : (2*n).choose (n+1) = n * catalan n`. Pascal:
  `Nat.choose_succ_right_eq (2*n) n` → `C(2n,n+1)*(n+1) = C(2n,n)*(2n−n)`, simp
  `[two_mul, Nat.add_sub_cancel]` → `= C(2n,n)*n`; sub `C(2n,n)=(n+1)*catalan n`; cancel
  `(n+1)` via `Nat.eq_of_mul_eq_mul_right (Nat.succ_pos n)`.
- `catalan_eq_choose_sub (n) : catalan n = (2*n).choose n − (2*n).choose (n+1)`. rw the two
  coefficient identities, then `omega` (with `(n+1)*c = n*c + c` by ring).
- `catalan_eq_choose_sub_symm (n) : catalan (n+1) = (2*(n+1)).choose (n+1) −
  (2*(n+1)).choose n`. Binomial symmetry `Nat.choose_symm` reflects `C(2(n+1),n+2)` to
  `C(2(n+1),n)`. Indexed at n+1 to avoid the FALSE n=0 case of the unshifted n−1 form.

### Verification
`lake env lean` (worktree): EXIT 0, no warnings. `#print axioms` all three =
`[propext, Classical.choice, Quot.sound]` — 0 counting-axioms. Gallery meta+annotations
created (verified/original/axiomCount 0), JSON validated.

### GOTCHAs
- `catalan` and `succ_mul_catalan_eq_centralBinom` are ROOT namespace (NOT `Nat.`); but
  `Nat.centralBinom`, `Nat.centralBinom_eq_two_mul_choose`, `Nat.choose_*` are `Nat.`.
- **ℕ-truncation trap**: the reflected form `catalan n = C(2n,n) − C(2n,n−1)` is FALSE at
  n=0 (n−1 truncates to 0 → C(0,0)−C(0,0)=0 ≠ catalan 0 = 1). State it at n+1.
- Build in the WORKTREE proofs dir, not main.

### Files
- `proofs/Proofs/CatalanNumbersOQ05OQ01.lean` (new, verified 0-axiom)
- `src/data/proofs/catalan-numbers-oq-05-oq-01/{meta.json,annotations.json}` (new)

### Next Steps
- Full Catalan triangle B(2n,k) = C(2n,n+k) − C(2n,n+k+1) uniformly.
- Convolution identities from reflected sums of ballot numbers.
