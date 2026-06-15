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
