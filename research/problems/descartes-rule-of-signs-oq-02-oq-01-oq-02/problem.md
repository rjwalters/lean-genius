# Problem: Discharging Sturm's Exact Count Axiom (descartes-rule-of-signs-oq-02-oq-01-oq-02)

## Statement

### Plain Language

The slug `descartes-rule-of-signs-oq-02-oq-01-oq-02`
(file `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`,
458 LOC, **0 sorries**, **1 axiom**, **26 theorems**, **6 definitions**)
formalises Sturm's theorem (1829) on exact root counting for squarefree
real polynomials. The Lean development implements the Sturm sequence
via Euclidean division (`p₀ = p`, `p₁ = p'`, `pₖ₊₁ = -(pₖ₋₁ % pₖ)`),
defines a sign-variation count `sturmVariations p x`, and proves four
corollaries (`sturm_no_roots`, `sturm_unique_root`, `sturm_two_roots`,
`sturm_count_le_variations`) plus monotonicity (`sturmVariations_antitone`).

The single remaining axiom is the **main theorem itself**:

```lean
axiom sturm_exact_count_axiom
    (p : ℝ[X]) (hp : p ≠ 0) (hpsc : Squarefree p)
    (a b : ℝ) (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    rootsInInterval p a b = sturmVariations p a - sturmVariations p b
```

i.e. for a squarefree `p ∈ ℝ[X]` and `a < b` with `p(a) ≠ 0`, `p(b) ≠ 0`,
the number of distinct real roots in `(a, b]` equals the drop in the
Sturm sign-variation count from `a` to `b`.

The open question recorded as **OQ-02-OQ-01-OQ-02** is:

> Can `sturm_exact_count_axiom` be fully proved in Lean (and the
> `axiom` declaration replaced by a `theorem`)?

## Statement (formal target)

Replace

```lean
axiom sturm_exact_count_axiom ...
```

at line 258 of `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`
with

```lean
theorem sturm_exact_count_axiom
    (p : ℝ[X]) (hp : p ≠ 0) (hpsc : Squarefree p)
    (a b : ℝ) (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    rootsInInterval p a b = sturmVariations p a - sturmVariations p b := by
  ...
```

so that

- the gallery `meta.json` fields update `axiomCount: 1 → 0`,
  `theoremCount: 28 → 29`, `status: "axiomatized" → "verified"`,
  `badge: "axiom" → "verified"` (or `"original"`); and
- the four corollaries (`sturm_no_roots`, `sturm_unique_root`,
  `sturm_two_roots`, `sturm_count_le_variations`) — currently
  one-liners that `rw [sturm_exact_count …]` — become fully
  verified without any axiom dependency.

## Why This Matters

1. **Last axiom on the Sturm chain.** The parent
   `descartes-rule-of-signs-oq-02` (Budan's theorem, 1807) and its
   open-question sibling `descartes-rule-of-signs-oq-02-oq-01`
   (Budan's upper-bound axiom) both still depend on at least one
   structural axiom for the sign-change accounting. Sturm is the
   *strongest* statement in the chain (an *equality*, not just an
   upper bound), so discharging its axiom retires the last
   real-root-counting black box for squarefree polynomials.

2. **Constructive root counting.** The four corollaries
   (`sturm_no_roots` etc.) are *the* practical interface for
   downstream consumers of this development. Verifying them
   axiom-free means a Lean-verified pipeline from any concrete
   squarefree polynomial to an exact root count via Euclidean GCD.

3. **Bridge to algebraic geometry.** Sturm's theorem is the
   foundation of real-algebraic-geometry tooling (cylindrical algebraic
   decomposition, Tarski quantifier elimination over ℝ, Hermite's
   theorem connecting roots to quadratic-form signatures). An
   axiom-free Sturm in Mathlib-style Lean opens the door to porting
   the rest of that pipeline.

## Classification

- **Tier**: research extension (OQ branch of a closed gallery entry).
- **Difficulty**: substantial — the axiom encodes the *core* of
  Sturm's argument (continuity + sign-stability + GCD identity).
  Estimated total formalization cost ~400–800 LOC of new Lean
  spread across 4–8 ACT iterations.
- **Status**: NEW (this PR; first claim, S1 OBSERVE bootstrap).

## Related Proofs

| Slug | Relation |
|---|---|
| `descartes-rule-of-signs-oq-02` | Parent: Budan's theorem (1807), upper bound via derivative tower. |
| `descartes-rule-of-signs-oq-02-oq-01` | Sibling: Budan's upper-bound *axiom* (`budan_upper_bound_axiom`), in S2 PREP. |
| `descartes-rule-of-signs-oq-01` | Cousin: original Descartes Rule of Signs (positive roots, 1637). |
| `descartes-rule-of-signs-oq-03` | Cousin: Descartes-style bounds on root *multiplicities*. |

## Path to Verification

This PR (S1 OBSERVE bootstrap) establishes the research directory and
catalogues the available infrastructure. A multi-cycle S2+ ACT plan is
outlined in `state.md` "Next Action" and `knowledge.md` §8.
