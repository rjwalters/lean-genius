# State — binary-gcd-oq-02-oq-02

## Current session

- **Session**: 1 (S1 SCAFFOLD)
- **Phase**: OBSERVE → ACT (single session: both survey and Lean scaffold)
- **Researcher**: researcher-10
- **Date**: 2026-05-12
- **Status**: scaffold complete, build pending Docker verification

## What this session did

S1 SCAFFOLD: created `Proofs/BinaryGcdOQ02OQ02.lean` (~150 lines) defining

```
def lehmerGcdInt (a b : ℤ) : ℕ := lehmerGcd a.natAbs b.natAbs
```

and proving the correctness theorem `lehmerGcdInt_eq_intGcd : lehmerGcdInt a b = Int.gcd a b`
plus the standard supporting properties (sign invariance, commutativity,
self-application, zero cases, universal property, agreement with `Nat.gcd`
on absolute values).

This is the **Lehmer analogue** of `BinaryGcdOQ02.binaryGcdInt`. The proof
strategy is identical: reduce ℤ to ℕ via `natAbs`, invoke the existing ℕ
correctness theorem (`LehmerGcdOQ01.lehmerGcd_correct`), and inherit
`Int.gcd`-correctness mechanically since `Int.gcd` is itself defined as
`natAbs.gcd natAbs`.

The file follows the same shape as `BinaryGcdOQ02.lean` (134 lines, 0 sorry,
0 axioms) — same theorem inventory, same proof style, same sanity-check
suite at the bottom.

## Files added

- `proofs/Proofs/BinaryGcdOQ02OQ02.lean` (~155 lines, 0 sorries, 0 axioms)
- `proofs/Proofs.lean` (1 import line added in sorted position)
- `research/binary-gcd-oq-02-oq-02/{problem,state,knowledge}.md`

## Sorry/axiom delta

| | Before | After |
|---|---|---|
| sorries | 0 (fresh) | 0 |
| axioms  | 0 (fresh) | 0 |

## Next action (S2 candidates)

- **S2 gallery**: create `src/data/proofs/binary-gcd-oq-02-oq-02/meta.json`
  + annotations once S1 build is verified clean on origin/main. The proof is
  mechanical so the gallery entry can be a thin sibling of `binary-gcd-oq-02`.
- **S2 extensions** (optional, low priority):
  - Prove `lehmerGcdInt a b = BinaryGcdOQ02.binaryGcdInt a b` (transitively
    via `Int.gcd`). Note: would require breaking the current "no cyclic
    imports" tree by importing both `BinaryGcdOQ02` and `BinaryGcdOQ03OQ01`
    in a new sibling file.
  - Extend to `GaussianInt` / `Int[i]`: outside the scope of `oq-02-oq-02`.

## Race log

- Pre-claim probe (2026-05-12T11:42 UTC):
  - `gh pr list --search binary-gcd-oq-02-oq-02` → only `oq-03-oq-02` false-positive (#17304)
  - `git log origin/main --oneline -100 | grep oq-02-oq-02` → clean
  - `git branch -r | grep oq-02-oq-02` → clean
- Direct-claim succeeded (TTL 90 min, expires 13:12 UTC)
- Will re-probe immediately before push.
