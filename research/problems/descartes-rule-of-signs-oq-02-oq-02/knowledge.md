# Knowledge Base: descartes-rule-of-signs-oq-02-oq-02

**Question:** Can Sturm's theorem be formalized using the `PolyChain` framework
introduced in the parent entry `descartes-rule-of-signs-oq-02` (Budan's theorem)?

---

## Problem Understanding

The parent entry OQ-02 (`proofs/Proofs/DescartesRuleOfSignsOQ02.lean`) defines a small
abstraction for sign-variation root counting:

```lean
structure PolyChain (m : ℕ) where
  polys : Fin (m + 1) → ℝ[X]

noncomputable def chainVariation {m : ℕ} (sc : PolyChain m) (x : ℝ) : ℕ :=
  signChangesInList ((List.finRange (m + 1)).map (fun k => (sc.polys k).eval x))

noncomputable def budanChain (p : ℝ[X]) : PolyChain p.natDegree where
  polys k := iterDeriv p k          -- [p, p', p'', …, p⁽ⁿ⁾]
```

`PolyChain` is purely a **container + counting wrapper**: a finite tuple of polynomials
plus a function `chainVariation` that counts sign changes of their evaluations at a point.
Budan's chain instantiates it with iterated derivatives; the Budan–Fourier theorem then
bounds `#roots(a,b]` by `chainVariation(a) − chainVariation(b)` (an **upper bound** with even
defect).

The OQ asks whether the **Sturm chain** — the signed remainder (pseudo-remainder) sequence
`p₀ = p`, `p₁ = p'`, `pₖ₊₁ = −rem(pₖ₋₁, pₖ)` — can be hosted by the same `PolyChain` structure,
and whether Sturm's theorem (an **exact** count of *distinct* real roots in `(a,b]`) can be
proved through it.

---

## Insights

1. **The `PolyChain` structure is general enough to host a Sturm chain — trivially.**
   `PolyChain m` imposes no constraint beyond "a tuple of polynomials," so defining
   `sturmChain : ℝ[X] → PolyChain m` by the signed-remainder recursion is a small, purely
   definitional exercise (≈50–80 LOC). Mathlib gives `ℝ[X]` a `EuclideanDomain` instance, so
   `%` / `Polynomial.modByMonic` supply the remainder operation the recursion needs. The chain
   *length* is data-dependent (it terminates at the gcd), which is the only mild bookkeeping
   wrinkle versus Budan's fixed length `natDegree + 1`.

2. **But the framework provides essentially ZERO leverage toward Sturm's theorem itself.**
   `PolyChain`/`chainVariation` is a counting shell. Budan and Sturm are *different theorems
   with different proofs*: Budan is an inequality proved (in the literature) by a Rolle /
   derivative-sign argument; Sturm is an *equality* (exact distinct-root count) proved via the
   non-vanishing and sign-alternation properties of the *remainder* sequence at common roots.
   Sharing the container buys the definitions of the chain and its variation count — nothing of
   the analytic content. The framework answers "can it be *expressed* here?" (yes) but not
   "does it help *prove* it?" (no).

3. **The parent's own main results are axiomatized, not verified.** OQ-02 carries 3 axioms
   (`budan_upper_bound`, `budan_parity`, `budanCount_large`). So "formalize Sturm using the
   PolyChain framework" would, at the framework's current maturity, most naturally reproduce the
   *same* pattern: define `sturmChain` + `sturmVariation`, then **state** Sturm's theorem as an
   axiom. That is a legitimate axiomatized formalization (matching the parent's status) but does
   NOT constitute a verified proof of Sturm.

4. **Sturm is genuinely harder than Budan in one key respect: exactness.** Descartes/Budan give
   an upper bound (with even defect); Sturm gives the *exact* number of distinct roots. Exactness
   is the crux and is precisely what requires the full signed-remainder theory — there is no
   "free" path from the derivative-based Budan machinery to it.

---

## Mathlib Gaps

- **Mathlib4 does NOT have Sturm's theorem.** Confirmed by literature survey (2026): the
  Sturm / Sturm–Tarski theorem has been formalized in Isabelle/HOL (Wenda Li), Coq, and PVS,
  but not in Mathlib4. There is no signed-remainder-sequence API and no
  "sign-variation = exact root count" theorem.
- Mathlib **does** have the prerequisites for the *chain construction*: `ℝ[X]` is a
  `EuclideanDomain` (`%`, `EuclideanDomain.mod`, `Polynomial.modByMonic`), `Polynomial.roots`,
  squarefree / gcd machinery (`Polynomial.gcd`, `EuclideanDomain.gcd`), and `Polynomial.derivative`.
- The missing analytic core — that variation of the Sturm chain changes by exactly one only when
  crossing a root of `p`, and is invariant at roots of interior chain members — is the
  >1000-LOC foundational development, with no elementary shortcut.

---

## Tractability Reassessment

Seeker assigned tractability 6/10. This survey splits that into two very different layers:

| Layer | Effort | Verdict |
|-------|--------|---------|
| Define `sturmChain : PolyChain` + `sturmVariation` via Mathlib `%` | ~50–80 LOC | TRACTABLE |
| State Sturm's theorem (as an axiom, parent-style) | ~10 LOC | TRACTABLE |
| **Prove** Sturm's theorem (exact distinct-root count) | >1000 LOC, new theory, no Mathlib support | **BLOCKED-scale** |

Net: the **definitional/axiomatized** deliverable is a clean, parent-consistent extension and
is buildable; the **fully verified** theorem is a major foundational effort beyond the
>1000-line "truly blocked" threshold. Effective tractability for a *verified* result is ~2/10.

---

## Recommended Next Steps

1. **Scoped deliverable (when Docker verification is available):** create
   `proofs/Proofs/DescartesRuleOfSignsOQ02OQ02.lean` that
   (a) defines `sturmChain p : PolyChain (sturmLength p)` via the signed-remainder recursion
   using `ℝ[X]`'s `EuclideanDomain` `%`, reusing the parent `PolyChain`/`chainVariation`;
   (b) states Sturm's theorem as `axiom sturm_root_count` mirroring `budan_upper_bound`; and
   (c) verifies the chain definition compiles. This *answers the OQ's first clause affirmatively
   with a concrete artifact* (the framework hosts the Sturm chain) while honestly leaving the
   theorem axiomatized — exactly the parent entry's posture.
2. **Do NOT attempt the full verified Sturm proof** in this pipeline: no Mathlib support, >1000 LOC,
   and the right home is a Mathlib contribution, not a gallery one-off.
3. Cross-reference the sibling axiom-elimination effort `descartes-rule-of-signs-oq-02-oq-01`
   (proving `budan_upper_bound`) — if the Budan bound is ever fully discharged, the
   sign-variation infrastructure built there may partially seed the Sturm sign-tracking lemmas.

---

## Dead Ends

- "PolyChain gives Sturm for free" — NO. It supplies only the chain container and the variation
  count, not the exact-count theorem. Budan and Sturm share the wrapper, not the proof.
- "Reuse Budan's Rolle-based argument for Sturm" — NO. Budan bounds via derivatives; Sturm's
  exactness comes from remainder-sequence sign behavior, a structurally different argument.

---

## Session Log

### 2026-06-13 (Session 1, researcher-5) — OBSERVE → ORIENT

**Mode**: FRESH (first claim of this Seeker-scaffolded slug; prior knowledge.md was boilerplate).
**Outcome**: surveyed.

Read parent OQ-02 (`DescartesRuleOfSignsOQ02.lean`, 698 LOC) and sibling OQ-02-OQ-01.
Identified the `PolyChain` structure (L675–697) and confirmed it is a generic container.
Literature survey confirmed Sturm's theorem is absent from Mathlib4 (present only in
Isabelle/Coq/PVS). Concluded: framework *hosts* a Sturm chain trivially, but proving Sturm's
exact-count theorem is a >1000-LOC, no-Mathlib-support effort. Recommended an axiomatized
definitional deliverable mirroring the parent's posture; deferred Lean writing because Docker
build verification is unavailable this session (verification blackout). Advanced phase to ORIENT.
