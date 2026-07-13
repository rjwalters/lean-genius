# Hurwitz's Theorem — Completing the Proof (`hurwitz-theorem-incomplete-01`)

## Goal

Complete the formalization in `proofs/Proofs/HurwitzTheorem.lean`. The file proves
**Hurwitz's "1, 2, 4, 8" theorem**: an `n`-square identity

$$\Bigl(\sum_{i=1}^n x_i^2\Bigr)\Bigl(\sum_{j=1}^n y_j^2\Bigr) = \sum_{k=1}^n z_k^2,\qquad z_k \text{ bilinear in } x,y,$$

exists **iff** `n ∈ {1, 2, 4, 8}`. The "if" direction and most of "only if" are done.

## Current state (session 1, 2026-06-28)

- File: `proofs/Proofs/HurwitzTheorem.lean`, 2042 lines, **0 axioms**, **1 sorry**.
- `hurwitz_theorem` and the "if" direction (`identities_exist_for_admissible`) are complete.
- `hurwitz_only_if` is complete **except** for one case. Case analysis in `hurwitz_only_if`:
  - `n ∈ {1,2,4,8}`: admissible (immediate). ✓
  - `n = 3`: `no_three_square_identity`. ✓
  - `n` odd, `n ≥ 5`: `no_odd_nsquare` — a clean determinant argument
    (`det(M)² = (−1)ⁿ = −1 < 0` contradiction). ✓
  - **`n` even, `n ∉ {2,4,8}` (i.e. n = 6, 10, 12, 14, …): the sole remaining `sorry` (line ~1937).**

### The infrastructure already in place (verified, 0-axiom)

From an `NSquareIdentity n`, normalizing the last form to the identity yields
`n − 1` real `n × n` matrices `M_j = crossMat nsi ⟨0⟩ ⟨j⟩` (`j = 1 … n−1`) with:

| Property | Lemma in file |
|----------|---------------|
| `Mⱼᵀ = −Mⱼ` (skew-symmetric) | `crossMat_skewSym` |
| `Mⱼᵀ Mⱼ = I` (orthogonal) | `crossMat_transMul` |
| `Mⱼ² = −I` (complex structure) | `crossMat_sq_neg_one` |
| `Mⱼ Mₖ + Mₖ Mⱼ = 0`, `j≠k` (anticommute) | `crossMat_anticommute` |

So `{M_1, …, M_{n−1}}` is a representation on `ℝⁿ` of the Clifford algebra
`Cl(0, n−1)` (negative-definite form). The theorem is then equivalent to the
**Hurwitz–Radon** statement that the minimal faithful real representation
dimension of `Cl(0, n−1)` exceeds `n` unless `n ∈ {1,2,4,8}`.

## The blocker (confirmed real this session)

The missing step is the representation-theoretic classification:

```
Cl(0,1) ≅ ℂ        → min real rep dim 2 = 2   ✓ (n=2 admissible)
Cl(0,3) ≅ ℍ        → min real rep dim 4 = 4   ✓ (n=4 admissible)
Cl(0,5) ≅ M₄(ℂ)    → min real rep dim 8 > 6   ✗ (n=6 impossible)
Cl(0,7) ≅ M₈(ℝ)²   → min real rep dim 8 = 8   ✓ (n=8 admissible)
Cl(0,9) ≅ M₁₆(ℝ)   → min real rep dim 16 > 10 ✗ (n=10 impossible)
```

This requires (a) the structure theorem `Cl(0,k) ≅ matrix algebra over ℝ/ℂ/ℍ`,
(b) **Bott periodicity** `Cl(0,k+8) ≅ Cl(0,k) ⊗ M₁₆(ℝ)`, and (c) **Artin–Wedderburn**
for real semisimple algebras.

**Mathlib audit (this session).** `Mathlib/LinearAlgebra/CliffordAlgebra/Equivs.lean`
contains only the small isomorphisms — `CliffordAlgebra` over a degenerate/1-dim form
to `ℂ`, to `ℍ` (quaternions), and to dual numbers. There is **no** general
`Cl(0,k)`-to-matrix-algebra classification, **no** Bott periodicity, and **no**
Artin–Wedderburn for real semisimple algebras anywhere in the `CliffordAlgebra`
directory (`Basic, BaseChange, Conjugation, Contraction, Equivs, Even, EvenEquiv,
Fold, Grading, Inversion, Prod, SpinGroup, Star`). The file's "not in Mathlib as of
April 2026" note is accurate. Building this is estimated **>1000 lines** of new
foundational material.

**Classification: BLOCKED** (needs >1000 lines of foundational Clifford-algebra
representation theory that Mathlib does not provide). This is *not* a tactical gap —
it is genuine missing mathematics.

## Elementary reduction recorded for future work (ORIENT)

While the full case is blocked, the **n ≡ 2 (mod 4)** subfamily (n = 6, 10, 14, …;
write `n = 2m` with `m` **odd**) admits a clean, fully elementary reformulation that
converts the *skew* generators into the standard *symmetric-involution* (positive
Clifford) picture. This is the conventional entry point to the Hurwitz–Radon argument
and is worth formalizing as a stepping stone even though it does not by itself close
the case.

Let `N = n − 1 = 2m − 1` (odd) and define the product `W := M_1 M_2 ⋯ M_{N}`.
Using only the four verified properties above (each `Mᵢ² = −I`, skew, anticommuting):

1. **`W` commutes with every `Mᵢ`.** Moving `Mᵢ` past `W` flips sign once per
   anticommuting factor; there are `N − 1 = 2m − 2` (even) of them, so
   `Mᵢ W = (−1)^{N−1} W Mᵢ = W Mᵢ`.
2. **`W² = (−1)^{N(N+1)/2} I = −I`** (since `N(N+1)/2 = (2m−1)m ≡ m ≡ 1 (mod 2)`).
   [General identity: a product of `k` pairwise-anticommuting square-roots of `−I`
   satisfies `(M_1⋯M_k)² = (−1)^{k(k+1)/2} I`.]
3. **`Wᵀ = (−1)^{N(N+1)/2} W = −W`**, so `W` is itself a skew, orthogonal complex
   structure — *central* relative to the generators.
4. Set **`Sᵢ := W Mᵢ`**. Then, using `W` central and `W² = −I`:
   - `Sᵢᵀ = Mᵢᵀ Wᵀ = (−Mᵢ)(−W) = W Mᵢ = Sᵢ`  → **symmetric**;
   - `Sᵢ² = W² Mᵢ² = (−I)(−I) = I`           → **involution**;
   - `Sᵢ Sⱼ = W² Mᵢ Mⱼ = −Mᵢ Mⱼ = −Sⱼ Sᵢ` for `i ≠ j` → **anticommute**;
   - conjugating by `Sⱼ` (`j ≠ i`) gives `Sⱼ Sᵢ Sⱼ = −Sᵢ`, so `tr(Sᵢ) = 0`
     (balanced `±1` eigenspaces, forcing `n` even — consistent).

So for `n ≡ 2 (mod 4)` the problem becomes: **`n − 1` pairwise-anticommuting
symmetric involutions on `ℝⁿ`**, i.e. a representation of the *positive-definite*
Clifford algebra `Cl(n−1, 0)`. The obstruction is then the minimal faithful real
rep dimension of `Cl(n−1, 0)` (e.g. `Cl(5,0) ≅ M₄(ℂ)`, rep dim 8 > 6) — still
requiring the classification, but now in the cleaner symmetric form.

**Caveat:** this construction needs `m` odd (`n ≡ 2 mod 4`), since only then is
`W² = −I`. For `n ≡ 0 (mod 4)`, `n ∉ {4,8}` (n = 12, 20, …) one has `W² = +I`
instead, so a different descent (the genuine Bott step) is required. The
`n ≡ 2 (mod 4)` reduction does **not** shorten the `n ≡ 0 (mod 4)` work.

## Recommendation

Mark **BLOCKED**. The single remaining `sorry` is mathematically equivalent to the
Hurwitz–Radon theorem and depends on Clifford-algebra representation theory absent
from Mathlib. Do **not** add scaffolding theorems on top of it. Productive future
directions, in order of value:

1. **Upstream / build the Clifford classification** (`Cl(0,k)` structure +
   Bott periodicity + real Artin–Wedderburn) — the only path that closes the proof.
2. Formalize the elementary `Sᵢ = W Mᵢ` reduction above as verified lemmas
   (`crossMat`-product `W` is a central skew complex structure for `n ≡ 2 mod 4`),
   giving a clean symmetric-involution restatement of the open case. Verified
   infrastructure, but does not close the `sorry`.
3. Leave the `sorry` documented and accurate (current state) — preferable to any
   overclaim.

## References

- A. Hurwitz, *Über die Komposition der quadratischen Formen* (1898).
- J. Radon, *Lineare Scharen orthogonaler Matrizen* (1922).
- Conway & Smith, *On Quaternions and Octonions* (2003), Ch. on Hurwitz's theorem.
- Lawson & Michelsohn, *Spin Geometry* (1989), Ch. I (Clifford algebra classification,
  Bott periodicity table).
