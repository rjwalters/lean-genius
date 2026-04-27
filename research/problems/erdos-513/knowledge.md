# Erdős #513 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

Let $f=\sum_{n=0}^\infty a_nz^n$ be a transcendental entire function. What is the greatest possible value of\[\liminf_{r\to \infty} \frac{\max_n\lvert a_nr^n\rvert}{\max_{\lvert z\rvert=r}\lvert f(z)\rvert}?\]



It is trivial that this value is in $[1/2,1)$. K\"{o}v\'{a}ri (unpublished) observed that it must be $>1/2$. Clunie and Hayman \cite{ClHa64} showed that it is $\leq 2/\pi-c$ for some absolute constant $c>0$. Some other results on this quantity were established by Gray and Shah \cite{GrSh63}.

See also [227].




References


[ClHa64] Clunie, J. and Hayman, W. K., The maximum term of a power series. J. Analyse Math. (1964), 143-186.

[GrSh63] Gray, Alfred and Shah, S. M., A note on entire functions and a conjecture of Erd\H{o}s. Bull. Amer. Math. Soc. (1963), 573-577.


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #2
- Problem #227
- Problem #512
- Problem #514
- Problem #39
- Problem #1

## References

- ClHa64
- GrSh63

## Sessions

### 2026-04-27 (researcher-7) - Replace `axiom maxModulus` with concrete `iSup` definition

**Mode**: REVISIT (prior session marked maxModulus concretization "too complex")
**Outcome**: PROGRESS — eliminated 2 axioms from `Erdos513Problem.lean` (6 → 4)

**What I Did**

1. Audited file: 6 axioms total (`maxModulus`, `maxModulus_nonneg`, `maxTerm_le_maxModulus`, `kovari_lower_bound`, `clunie_hayman_upper_bound`, `erdos_513_exact_value`)
2. Replaced `axiom maxModulus a r : ℝ` with a concrete `noncomputable def` using `iSup` over `Metric.sphere (0 : ℂ) r` of `‖powerSeriesFun a z‖`, where `powerSeriesFun a z := ∑' n, a n * z^n`.
3. Replaced `axiom maxModulus_nonneg` with a one-line theorem (`le_max_left 0 _`) since the definition wraps with `max 0 (...)`.
4. Verified via Docker build (23s, exit 0) — only minor unused-variable warnings remain.

**Key Insight: `tsum` returns 0 for non-summable cases**

Lean's `tsum` (`∑' n, ...`) is defined to return 0 when the family is not summable. This means `powerSeriesFun a z` is always well-defined, even for sequences `a` that don't define an entire function. The `max 0 (...)` wrapper in the iSup also handles unbounded suprema (which return their default in `ℝ`), so `maxModulus_nonneg` follows trivially.

For transcendental entire functions (the only case the downstream axioms apply to), the series is summable, so the definition agrees with the classical max modulus.

**Remaining Axioms (4)**

1. `maxTerm_le_maxModulus` — μ(r) ≤ M(r). Classical Cauchy estimate result; provable but requires Cauchy's integral formula (substantial Mathlib API).
2. `kovari_lower_bound` — research-level (Kövári unpublished); not provable here.
3. `clunie_hayman_upper_bound` — research-level (Clunie–Hayman 1964); not provable here.
4. `erdos_513_exact_value` — the OPEN conjecture itself.

**Files Modified**

- `proofs/Proofs/Erdos513Problem.lean` (lines 41-56; +12 lines, -8 lines)

**Next Steps**

1. Update `axiomCount` in meta.json (if it exists for this entry; `src/data/research/problems/erdos-513.json` has `axiomCount: 6` to update to 4)
2. Consider tackling `maxTerm_le_maxModulus` — would require Cauchy estimate; large effort but axiom-eliminating

---

*Generated from erdosproblems.com on 2026-01-13*
