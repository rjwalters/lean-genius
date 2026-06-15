# Problem: solution-of-cubic-oq-03-oq-03-oq-01

**Name (pool):** Can the Ferrari factorization axioms in `GeneralQuartic.lean` be proved?

**Tier:** B · **Significance:** 6 · **Tractability:** 7 · **Tags:** algebra, gallery-extracted

## Statement (as posed)

The open question asks whether the *Ferrari factorization axioms* used in
`proofs/Proofs/GeneralQuartic.lean` (the gallery's formalization of the solution
of the general quartic by radicals) can be discharged to theorems.

## Reframing (ORIENT, 2026-06-14)

The posed framing is **stale**. Reading the current source, every
Ferrari-*factorization* declaration is **already a proven `theorem`**, not an
`axiom`:

| Declaration | Line | Status |
|---|---|---|
| `ferrari_factorization_id` | 167 | theorem (proved) |
| `ferrari_hβ2_of_resolvent` | 183 | theorem (proved) |
| `ferrari_factorization_backward_ne` | 207 | theorem (proved) |
| `ferrari_factorization_forward_ne` | 232 | theorem (proved) |
| `ferrari_factorization` | 323 | theorem (proved) |

`grep -c '^axiom ' GeneralQuartic.lean` → **3**, `grep -c sorry` → **0**.

So the **genuine residual** is exactly the three axioms that remain, none of which
is a "Ferrari factorization" axiom per se:

- **(A1) `quartic_has_four_roots`** (line 268) — Fundamental Theorem of Algebra
  instance: the monic degree-4 `quarticPoly a b c d` has a 4-element root set,
  `∃ r₁..r₄, ∀ x, eval x = 0 ↔ x ∈ {r₁,r₂,r₃,r₄}`.
- **(A2) `biquadratic_forward`** (line 275) — when `q = 0`, a root of
  `y⁴ + p y² + r` has `y²` equal to one of `(-p ± √(p²−4r))/2`
  (`√` = `Complex.cpow · (1/2)`).
- **(A3) `biquadratic_backward`** (line 283) — the converse of A2.

This problem is therefore an **axiom-discharge** task on an otherwise complete,
0-sorry file, not new mathematics.
