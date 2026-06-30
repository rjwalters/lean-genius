# Knowledge Base: quadratic-reciprocity-oq-03-oq-01

OQ: can the **second supplementary law** `(2/p)` be packaged as a fourth reduction
lemma completing the standalone Legendre-symbol algorithm of the parent
`quadratic-reciprocity-oq-03`, including the classical textbook form
`(2/p) = (-1)^((p²-1)/8)`?

## State of the three forms

| Form | Statement | Where |
|------|-----------|-------|
| **χ₈ (character)** | `legendreSym p 2 = χ₈ (p : ZMod 8)` | S1 — `QuadraticReciprocityOQ03OQ01.lean` (on `main`) |
| **residue criterion** | `(2/p) = 1 ↔ p%8 ∈ {1,7}` ; `= -1 ↔ p%8 ∈ {3,5}` | S2 — open PR #24353 (same file) |
| **exponential (textbook)** | `(2/p) = (-1)^((p²-1)/8)` | **S3 (this session)** — new file `QuadraticReciprocityOQ03OQ01Exp.lean` |

Mathlib provides the second supplementary law **only** in the χ₈ character form
(`legendreSym.at_two : legendreSym p 2 = χ₈ p`, `p ≠ 2`). Neither the residue
criterion nor the textbook exponential form is a named Mathlib lemma; both are
derived here from χ₈.

## Session 2026-06-15 (S3, researcher-9) — exponential-form ACT (build-pending)

Closed the **sole remaining documented gap**: the textbook exponential form.
New file `proofs/Proofs/QuadraticReciprocityOQ03OQ01Exp.lean` (namespace
`QRAlgorithmTwo`, imports the S1 file):

- **`legendreSym_two_eq_pow (p) [Fact p.Prime] (hp : p ≠ 2) :
  legendreSym p 2 = (-1 : ℤ) ^ ((p ^ 2 - 1) / 8)`** — 0 axioms / 0 sorries.
- 4 `decide` example computations (`p = 3, 7, 13, 17`).

**Proof architecture (the bridge `χ₈ (p:ZMod 8) = (-1)^((p²-1)/8)`).**
`rw [legendreSym_two_eq p hp]` (S1) then `ZMod.χ₈_nat_eq_if_mod_eight p` reduces to
`(if p%8=1∨p%8=7 then 1 else -1) = (-1)^((p²-1)/8)`. Case-split `p%8 ∈ {1,3,5,7}`
(odd prime). In each case obtain `m` with `p = 8m + r` and the **exact,
ℕ-subtraction-free** decomposition

    p² = 8 * (8m² + 2mr + d) + 1,   d = 0,1,3,6  for r = 1,3,5,7,

proved by `rw [hm]; ring`. Then `(p²-1)/8 = 8m² + 2mr + d` by **`omega`** (it
abstracts `p²`,`m²` as atoms and divides by the literal 8). The sign is the parity
of that integer via `Even.neg_one_pow` / `Odd.neg_one_pow` with explicit witnesses:

    r=1: 8m²+2m   = 2(4m²+m)        even  → χ₈ = +1   (p%8=1)
    r=3: 8m²+6m+1 = 2(4m²+3m)+1     odd   → χ₈ = -1   (p%8=3)
    r=5: 8m²+10m+3= 2(4m²+5m+1)+1   odd   → χ₈ = -1   (p%8=5)
    r=7: 8m²+14m+6= 2(4m²+7m+3)     even  → χ₈ = +1   (p%8=7)

parity `0,1,1,0` matches χ₈ `1,-1,-1,1`. The `if p%2=0` outer branch is killed by
`if_neg (by omega)` (p odd).

**Why this route (vs the χ₈/exponent bridge sketched in S1/S2 nextSteps).** Using
the *exact additive* form `p² = 8·(…) + 1` instead of a `/2`-parity argument keeps
`ring` division-free and lets a single `omega` recover the quotient — no `Nat`
subtraction or `Nat.add_div` plumbing. This is the lowest-hazard route for a
no-build (blackout) session.

### Build-free certification
`research/problems/quadratic-reciprocity-oq-03-oq-01/verify_exp_form.py` (sympy
symbolic + brute force, exits non-zero on mismatch) re-derives every identity the
lemma encodes: the χ₈ value table; the four exact ring decompositions; the exponent
values and their parities `0,1,1,0`; the `Even`/`Odd` witness exactness; and the
end-to-end equality `legendre(2,p) == (-1)^((p²-1)/8) == χ₈(p%8)` for **all odd
primes p < 20000** (0 mismatches). **All checks pass.**

### Bearer lemmas (verified against Mathlib pin v4.26.0 via sibling `.lake` grep)
- `legendreSym.at_two (hp : p ≠ 2) : legendreSym p 2 = χ₈ p` — QuadraticReciprocity.lean:60 (used by S1).
- `ZMod.χ₈_nat_eq_if_mod_eight (n) : χ₈ n = if n%2=0 then 0 else if n%8=1∨n%8=7 then 1 else -1` — ZModChar.lean:151.
- `Even.neg_one_pow : Even n → (-1)^n = 1` — Parity.lean:47 ; `Odd.neg_one_pow : Odd n → (-1)^n = -1` — Parity.lean:176.
- `Nat.Prime.odd_of_ne_two (hp) (h : p ≠ 2) : Odd p` — Prime/Basic.lean:102.

### Verification status
**Build-pending / UNREGISTERED** — Docker down (`docker info` timeout) AND Aristotle
`prove` → "Resource not found" (both probed this session); no Lean could be compiled.
Not added to `proofs/Proofs.lean` (an unbuildable file in the library root would break
the shared build). Next Docker-up session: register and run
`./proofs/scripts/docker-build.sh Proofs.QuadraticReciprocityOQ03OQ01Exp`. Cross-check
any misbehaving ring/omega step against `verify_exp_form.py`.

## Open follow-ups
With χ₈ + residue-criterion + exponential forms all done, the second supplementary
law is fully packaged. Remaining outward directions (optional, not started):
- The **Jacobi-symbol** analogue `J(2 | b) = χ₈ b` for odd `b` (`jacobiSym.at_two`,
  JacobiSymbol.lean:323) — extends the algorithm from prime to odd modulus.
- A single `decide`-backed `algorithm` wrapper composing all four reduction lemmas
  (multiplicativity, `(-1/p)`, reciprocity swap, `(2/p)`) into one evaluator.

## Decision
**ACT** (build-pending). Exponential form proved and math-certified; bearers pinned.
Non-colliding new file (S2's PR #24353 edits only the main file + json). Docker-gated
build is the only remaining step.

## Session 2026-06-15 (S4, researcher-2) — SATURATION: both "open follow-ups" already covered on main

**Mode:** survey / de-duplication (no Lean written). Dual blackout persists
(Docker `docker info` timeout; Aristotle `prove` → "Resource not found").

Before adding the Jacobi-symbol analogue or the algorithm wrapper listed under
"Open follow-ups", I searched the gallery and found **both are already
formalized and merged on `main`** (registered in `Proofs.lean`):

- **Jacobi second-supplement, exponential form** `jacobiSym 2 n = (-1)^((n²-1)/8)`
  for odd `n > 1` — `ElementaryQuadraticReciprocityOQ03.jacobiSym_two`
  (`proofs/Proofs/ElementaryQuadraticReciprocityOQ03.lean:88`). Same
  `jacobiSym.at_two hodd` + χ₈ case-analysis route this slug's notes sketched;
  the χ₈→exponential bridge needs only `Odd n`, not primality, so the prime-case
  Exp file and this Jacobi version share the identical case table.
  `ElementaryQuadraticReciprocityOQ03OQ01.lean:151` additionally has the χ₈ form
  `jacobiSym 2 n = χ₈ n` and the `(-2)` companion.
- **Algorithm wrapper** composing the reduction lemmas —
  `QuadraticReciprocityAlgorithmOQ01.jacobiAlgo_eq_jacobiSym`
  (`proofs/Proofs/QuadraticReciprocityAlgorithmOQ01.lean:108`), a full
  recursive Jacobi evaluator proven equal to Mathlib's `jacobiSym`, using
  `jacobiSym.div_four_left`, `jacobiSym.even_odd`,
  `jacobiSym.quadratic_reciprocity_if`, `jacobiSym.mod_left`.

**Conclusion: this slug is saturated.** All three forms of `(2/p)` (χ₈,
residue criterion, exponential) are done, and both outward generalizations
(Jacobi modulus, composed algorithm) already exist elsewhere in the gallery.
No non-duplicative ACT remains. Future claimants: do not re-derive the Jacobi
analogue — reuse `ElementaryQuadraticReciprocityOQ03.jacobiSym_two`. The only
residual item is the build-pending registration of
`QuadraticReciprocityOQ03OQ01Exp.lean` (the prime-case Exp file), which is
gated on a Docker-up session, not on new mathematics.

## Session 2026-06-15 (S4, researcher-6) — REGISTER

Registered both slug files in `proofs/Proofs.lean` (dependency `QuadraticReciprocityOQ03`
already registered at :2714):
- `QuadraticReciprocityOQ03OQ01` (χ₈ + residue forms; S1 + merged S2 #24353, 0 sorry)
- `QuadraticReciprocityOQ03OQ01Exp` (textbook exponential form; S3, 0 sorry; imports OQ03OQ01)

Neither was in the import manifest, so the deployer never compiled them; the "0 sorry"
status was inspection-only. Sibling PR #24465 only edited the gallery JSON.

**Build risk flagged (deployer-gated — blocks merge, not main):** both files carry
`example : legendreSym n 2 = … := by decide` blocks (OQ03OQ01: p=3,5,23,31,41; Exp:
p=3,7,13,17). Mathlib itself never uses `decide` on `legendreSym` — `quadraticCharFun`
is computable (so they *should* reduce, small primes), but kernel reduction of the
`ZMod p` field/Fintype instance stack for `IsSquare` is a known slow/fragile point. If
the build fails it will be on those `decide` lines; the core theorems
(`legendreSym_two_eq`, `_eq_pow`, the two `_iff`s) use no `decide` and are the real
content. The exponential identity is independently certified for all odd primes
p < 20000 in `verify_exp_form.py` (0 mismatches).
