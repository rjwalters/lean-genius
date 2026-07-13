# Knowledge Base: prob-method-second-moment-oq-02

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

---

## Session 2026-06-15 — triangle second moment & threshold certificate (build-free)

The OQ-02 application layer culminates in the triangle threshold `p*(n) = 1/n` in
`G(n,p)`. The genuinely case-heavy step (the deferred §C "Paley–Zygmund overlap-class
calculation", the part earmarked for 0–2 strategic Lean sorries) is the **second moment**
of the triangle count `X`. This session certifies that calculation EXACTLY, so the
eventual Lean ACT has a verified target. (Build-free: Docker blackout.)

**`verify_triangle_threshold.py`** (sympy + exact `Fraction`) certifies:

- **Overlap classes are exhaustive.** Ordered pairs of triangle slots `(T,T')` split by
  `|E(T)∪E(T')|`: `=T` (exp 3), 2 shared vertices = shared edge (exp 5), 1 shared vertex
  (exp 6), 0 shared vertices (exp 6). Counts sum to `C(n,3)²` (checked `n=3..11`).
- **Closed form (symbolic in n):**
  `Var[X] = C(n,3)·[ p³ + 3(n−3)p⁵ − (3n−8)p⁶ ]`, proved equal to the raw overlap-class
  `E[X²] − E[X]²` with `E[X] = C(n,3)p³`.
- **Brute-force cross-check (exact in p):** enumerating all `2^{C(n,2)}` graphs for
  `n = 3,4,5,6` reproduces both `E[X]` and `E[X²]` as polynomials in `p` — 0 mismatches.
- **Threshold at `p = c/n`, `n→∞`:** `E[X] → c³/6` (so `np→0 ⟹ E[X]→0 ⟹` Markov gives
  Pr(triangle)→0, subcritical) and `Var[X]/E[X]² → 6/c³` (so `np→∞ ⟹` ratio →0 ⟹
  Paley–Zygmund gives Pr(triangle)→1, supercritical). This pins `p*(n) = 1/n`.

The dominant variance term is the shared-EDGE class (`3·C(n,3)(n−3)p⁵`), exactly the term
the Lean §C must isolate. The shared-edge ordered-pair count `3·C(n,3)(n−3)` and the
exponent-5 weight are now machine-checkable constants for the formalization.
