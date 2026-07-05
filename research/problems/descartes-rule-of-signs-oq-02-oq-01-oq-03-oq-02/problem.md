# Problem: Effective bisection depth for Vincent root isolation — explicit k ≤ log₂(w / minGap S) + 1

## Statement

### Plain Language
The parent entry (`descartes-rule-of-signs-oq-02-oq-01-oq-03`, "Vincent's Theorem:
Bisection Subdivision Eventually Isolates Real Roots") proves the *existential*
termination statement `exists_level_isolates : ∃ k, ...`: for a finite root set
`S ⊆ ℝ` with minimum gap `δ = minGap S > 0` and starting interval width `w > 0`,
**some** bisection level `k` makes every dyadic subinterval (width `w / 2^k`)
root-isolated (meets `S` in at most one point).

This leaf upgrades that existential to an **effective, explicit bound**: exhibit a
concrete level `k ≤ log₂(w / δ) + 1` (equivalently `k = ⌈log₂(w / δ)⌉`) that already
isolates. This matches the `O(log(w / δ))` subdivision-depth complexity analysis of
the Vincent–Akritas–Strzeboński (VAS) / bisection real-root isolation algorithm,
turning a pure existence proof into a computable termination certificate.

### Formal Statement
$$
\forall (S : \mathrm{Finset}\ \mathbb{R})\ (w : \mathbb{R}),\ 0 < w \ \Longrightarrow\
\frac{w}{2^{\,k(w,S)}} < \operatorname{minGap} S,
\qquad k(w,S) := \left\lceil \log_2\!\frac{w}{\operatorname{minGap} S} \right\rceil .
$$

Concretely, strengthen the parent's `exists_width_lt` / `exists_level_isolates`
(which pick `k` by the Archimedean/`∃` argument) to an explicit-witness form, e.g.

```
theorem level_isolates_explicit (S : Finset ℝ) {w : ℝ} (hw : 0 < w) :
    ∀ k, Nat.clog 2 ⌈w / minGap S⌉₊ ≤ k →
      w / 2 ^ k < minGap S
```

and package a `level_isolates_explicit_bound` stating
`w / 2 ^ (Nat.clog 2 ⌈w / minGap S⌉₊) < minGap S`, so that the resulting
subintervals are root-isolated by the parent's `subsingleton_of_width_lt_minGap`.
The witness `k = ⌈log₂(w / δ)⌉` (Mathlib `Nat.clog 2`) is minimal up to the `+1`,
giving the tight `k ≤ log₂(w / δ) + 1` bound.

## Classification

```yaml
tier: B
significance: 6
tractability: 7
tags:
  - algebra
  - polynomials
  - real-algebraic-geometry
  - root-isolation
  - vincent-theorem
  - bisection
  - effective-bounds
  - nat-clog
  - archimedean
  - termination
  - seeker-selected
```

**Significance**: 6/10
**Tractability**: 7/10

## Why This Matters

1. **Effective termination** - Converts the existential termination guarantee of
   Vincent's bisection theorem into an explicit `O(log(w / δ))` depth bound, the
   quantitative content actually used to bound the running time of VAS / VCA
   real-root isolation.
2. **Reuses a verified base** - The parent entry already supplies `minGap`,
   `minGap_pos`, `subsingleton_of_width_lt_minGap`, and `width_after_bisect`
   (`w / 2^k`); only the Archimedean `exists_width_lt` step needs replacing by an
   explicit `Nat.clog 2` witness, so the delta is small and self-contained.
3. **Mathlib-aligned** - `Nat.clog 2`, `Nat.clog_le`, and `Nat.lt_pow_succ_log_self`
   give the ceiling-log arithmetic directly, making this a clean effective-bounds
   exercise with no new mathematical content beyond the explicit constant.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| descartes-rule-of-signs-oq-02-oq-01-oq-03 | Parent: proves the existential `exists_level_isolates`; this leaf makes `k` explicit. |
| descartes-rule-of-signs-oq-02-oq-01 | Budan upper-bound ancestor in the same lineage. |
