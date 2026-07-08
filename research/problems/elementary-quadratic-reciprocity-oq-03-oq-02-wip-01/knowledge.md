# Knowledge: Kronecker Symbol WIP Completion

## Result (2026-07-07)

**Target 1 — full second-argument multiplicativity — is proven and machine-verified**
in `proofs/Proofs/ElementaryQuadraticReciprocityOQ03OQ02.lean` (0 sorries, 0 axioms,
builds under Mathlib v4.26).

New declarations:
- `kronecker_eq_sign_jacobi (a n : ℤ) (hn : n ≠ 0)` — normal form:
  `kronecker a n = (if n < 0 then kroneckerNeg1 a else 1) * jacobiSym a n.natAbs`.
- `kroneckerNeg1_sq` (private) — `kroneckerNeg1 a * kroneckerNeg1 a = 1`.
- `kronecker_mul_right (a m n : ℤ) (hmn : m * n ≠ 0)` — `(a/mn) = (a/m)(a/n)`.
- `kronecker_mul_right_odd` retained as the `ℕ`-typed odd-modulus corollary.

## Key insights

- **`jacobiSym.mul_right'` needs only nonzero moduli, not oddness.** The prior
  session assumed the general even/negative case required supplementary laws
  `(2/n)`, `(-1/n)`. That is true for the *classical* Kronecker symbol, but this
  file's `kronecker` definition routes the whole modulus through `jacobiSym |n|`,
  so multiplicativity is immediate from `jacobiSym.mul_right' a (b₁≠0) (b₂≠0)`.
- **Normal-form trick.** The three special-modulus branches (`n = 0, ±1`) obstruct
  a direct `split_ifs` when the three `kronecker` calls have *different* moduli
  (`m*n`, `m`, `n`). Collapsing each to `sign(n)·J(a||n|)` first makes the
  remaining case analysis purely about signs.
- **Sign multiplicativity** across a nonzero product: the only nontrivial case is
  `m<0, n<0` (then `m*n>0`), where the two sign characters must cancel — handled
  by `kroneckerNeg1_sq` (a value in `{±1}` squares to 1).
- **Scope caveat (honesty).** At even moduli the file's symbol equals Jacobi's
  value at 2, NOT the classical mod-8 character `kronecker2` (which is defined in
  the file but never wired into `kronecker`). So `kronecker_mul_right` is
  multiplicativity of the symbol *as defined* — it coincides with the classical
  Kronecker symbol at all odd moduli and at `n = ±1`. Status kept `wip`.
- **Build gotcha:** local Docker builds of this file SIGSEGV/exit-135 on the
  `#print axioms` commands (stack overflow); the origin/main version always
  *replays* its cached olean so the crash only appears once the file is edited.
  Commented the `#print axioms` block out; the file otherwise builds in ~2s.

## Update (2026-07-08) — self-reciprocity of the prime 2

New theorem `kronecker2_eq_kronecker_two (n : ℕ) (hn : 0 < n) (hno : n % 2 = 1)`:
`kronecker2 (n : ℤ) = kronecker 2 n`, i.e. `(n/2) = (2/n)` for odd positive `n`.
This bridges the two a-priori distinct "2-characters" that coexist in the file:
- `kronecker2` — a function of the *numerator*, the even real Dirichlet character
  mod 8 (Section 6: `kronecker2_mul` / `_periodic` / `_neg` / `_values`), and
- `kronecker 2 ·` — a function of the *denominator* (Section 8: `kronecker_two_odd`).
They agree on the odd integers (both `+1` on `±1 mod 8`, `−1` on `±3 mod 8`), so
the proof is `kronecker_two_odd` + `unfold kronecker2` + a residue comparison by
`omega`. Build-verified (3058 jobs, 0 sorries, 0 axioms). `theoremCount` 25→26.

*Build note:* the file still exhibits the documented exit-135 SIGSEGV on the
first fresh build after an edit (elaborates fully — `3058/3058` — then crashes on
finalization). A plain retry builds green (environmental / shared-volume, not a
proof error). Do NOT edit the proof in response to a line-less 135.
*(Reproduced again 2026-07-08: fresh build `✖ 135` at `3058/3058`, plain retry
`✔ Built`. Same behaviour, same fix.)*

## Update (2026-07-08 #2) — denominator-side periodicity of the supplementary characters

Two new theorems establish that the two *denominator-side* quadratic characters
are periodic Dirichlet characters (theoremCount 26→28, lineCount 477→510,
0 sorries / 0 axioms):
- `kronecker_neg_one_periodic (n hn hno)` — for odd positive `n`,
  `(-1/(n+4)) = (-1/n)`: the sign character `(-1/·)` is periodic mod 4.
- `kronecker_two_periodic (n hn hno)` — for odd positive `n`,
  `(2/(n+8)) = (2/n)`: the character `(2/·)` is periodic mod 8.

Both are one-liners off the Section-8 supplementary laws: rewrite the numeral
addition `(n:ℤ)+k = ((n+k:ℕ):ℤ)` (`push_cast; ring`), apply `kronecker_neg_one_odd`
/`kronecker_two_odd` on both sides, then close with `(n+k)%k = n%k` by `omega`.

**Why this matters (honest framing).** These are the *denominator-side* complement
of `kronecker2_periodic` (which is the *numerator* character `(·/2)`). Combined
with `kronecker_mul_right` (multiplicativity in the denominator), they exhibit the
supplementary characters `(-1/·)` and `(2/·)` as Dirichlet characters mod 4 and mod
8 — the periodicity + multiplicativity data the Gauss-sum route to generalized
reciprocity (refinement 2) rests on. This is incremental structural progress, not
the reciprocity core itself, which still needs the Gauss sum (open).

## Open work

1. Refine `kronecker` to use `kronecker2` at the 2-adic part (→ classical symbol
   at even moduli), then re-prove `kronecker_mul_right` for the refined def.
   (`kronecker2_eq_kronecker_two` is a step toward this: it shows the refined and
   current defs would agree at odd moduli, so only the even branch changes.)
2. Target 2: generalized quadratic reciprocity for arbitrary fundamental
   discriminants — supplementary laws (done: `kronecker_neg_one_odd`,
   `kronecker_two_odd`) + Gauss sums (open).
