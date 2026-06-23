# Problem: Can the $O(n^\omega)$ Keller-Gehrig algorithm (1985) be formalised, extending the Krylov framework to subcubic complexity?

## Statement

### Plain Language

The Krylov method (formalised in `CayleyHamiltonMinpolyOQ03.lean`) computes the
minimal polynomial of an $n\times n$ matrix in $O(n^3)$ field operations,
using $n$ matrix-vector products of $O(n^2)$ each.

Keller-Gehrig (1985) gives a $O(n^\omega)$ algorithm, where $\omega < 3$ is the
matrix-multiplication exponent (e.g. Strassen's $\omega = 2.807$, currently
$\omega \approx 2.37$). The asymptotic speed-up is genuine: it relies on
repeated squaring of $M$ itself, replacing $n$ Krylov steps with $\lceil \log_2 n \rceil$
matrix products of size $n\times n$.

**Open question.** Can this algorithm be formalised in Lean 4 over Mathlib?

### Formal Statement (target)

$$
\text{KellerGehrig}(M) \text{ computes } \mu_M \text{ in } O(n^\omega) \text{ field operations.}
$$

More precisely, three layers of formalisation are possible:

1. **Structural layer.** Define a *squared-Krylov sequence*
   $T_k := M^{2^k}$ for $0 \le k \le \lceil \log_2 n \rceil$, and prove the
   recurrence $T_{k+1} = T_k \cdot T_k$.  ✅ Tractable in Mathlib today.

2. **Correctness layer.** Show that the span of
   $\{v, Mv, M^2 v, \dots, M^{2^{\lceil \log_2 n\rceil}-1} v\}$ contains
   $\{v, Mv, \dots, M^{n-1} v\}$, hence the minimal polynomial can be
   recovered from the squared-Krylov vectors in $\lceil \log_2 n\rceil$
   matrix-matrix products plus one matrix-vector solve. ✅ Tractable.

3. **Complexity layer.** Prove the operation count is $O(n^\omega)$. ❌ **Blocked**
   on (a) Mathlib having no operation-counting / complexity-monad framework
   and (b) Mathlib having no fast matrix multiplication implementation; the
   default `Matrix.mul` is the naive cubic algorithm.

## Classification

```yaml
tier: B
significance: 6
tractability: 6
tags:
  - linear-algebra
  - matrices
  - polynomials
  - minimal-polynomial
  - krylov-method
  - computational-complexity
  - keller-gehrig
  - subcubic
  - research
  - seeker-selected
  - gallery-extracted
```

**Significance**: 6/10 — Foundational result in the asymptotic complexity of
exact linear algebra; gateway to the entire Storjohann / Giesbrecht literature
on $O(n^\omega)$ algorithms for canonical forms (Hermite, Smith, Frobenius).

**Tractability**: 6/10 — Layer (1) is straightforward (≈ 30 lines). Layer (2)
needs a short bridge proof. Layer (3) requires infrastructure Mathlib does not
yet have.

## Why This Matters

1. **Closes the algorithmic chapter of `cayley-hamilton-minpoly`.**
   `CayleyHamiltonMinpolyOQ03.lean` formalises Krylov at $O(n^3)$; the
   Keller-Gehrig algorithm is the natural successor showing the same
   structural objects (Krylov sequence, annihilating polynomial) survive into
   the subcubic regime.

2. **Provides a clean target for the "complexity in Mathlib" discussion.**
   Even partial layer-(1)/layer-(2) progress puts a stake in the ground:
   "here is the proof that the asymptotic gain is structural, modulo a
   complexity oracle." A future Mathlib complexity-monad PR would slot in
   without rewriting the linear-algebra core.

3. **Aligns with the active OSforGFF / Mathlib-upgrade plan** (project memory)
   which contemplates richer computational-algebra infrastructure.

## Mathlib Infrastructure Map

### Available today (✅)

| Object | Mathlib API | OQ-03 wrapper |
|--------|-------------|---------------|
| Matrix powers | `Matrix.pow_succ`, `Matrix.pow_mul` | n/a |
| Polynomial evaluation at a matrix | `Polynomial.aeval` | `aeval_mulVec_eq_krylov_sum` (OQ-03:111) |
| Minimal polynomial existence | `minpoly K M` | `minpoly_annihilates_vec` (OQ-03:135) |
| Krylov sequence | — | `krylovVec` (OQ-03:73) |
| Krylov recurrence | — | `krylov_recurrence` (OQ-03:318) |
| Iteration bound $d \le n$ | — | `krylov_iteration_bound` (OQ-03:236) |
| Cyclic vector → maximal Krylov | — | `nonderogatory_krylov_optimal` (OQ-03:256) |

### Missing today (❌)

1. **No squared-Krylov sequence** $T_k = M^{2^k}$ in OQ-03 or Mathlib.
2. **No "span of Krylov prefixes" API** in OQ-03 (only LinearIndependent).
3. **No complexity monad** in Mathlib (no `Cost` / `WithCount` / Sterling
   tagged-monad). This blocks any *quantitative* statement of $O(n^\omega)$.
4. **No fast matrix multiplication.** `Matrix.mul` is `Σ_k (M i k) * (N k j)`,
   the textbook $O(n^3)$ algorithm. Strassen, Coppersmith-Winograd, etc., are
   absent.
5. **No matrix-multiplication exponent $\omega$.** Even as an opaque constant
   $\omega \in [2, 3]$ with axioms.

## Decomposition (S2-S6)

The proposed decomposition keeps each session under 100 lines of Lean and
under one Docker build:

### S2 — squared-Krylov sequence (≈ 35 lines, 1 build)

* `def squareKrylov (M : Matrix (Fin n) (Fin n) K) : ℕ → Matrix (Fin n) (Fin n) K
   | 0     => M
   | k + 1 => squareKrylov M k * squareKrylov M k`
* `theorem squareKrylov_eq_pow_two : squareKrylov M k = M ^ (2 ^ k)`
  (single `Nat.rec` + `Matrix.pow_mul` + `pow_succ`).
* `theorem squareKrylov_recurrence : squareKrylov M (k+1) = squareKrylov M k * squareKrylov M k`
  (definitional).

### S3 — Krylov prefix span dominated by squared-Krylov (≈ 60 lines, 1 build)

* `theorem krylov_in_squareKrylov_span :
     ∀ i < 2 ^ k, ∃ p : K[X], p.natDegree < 2 ^ k ∧
       (aeval M p).mulVec v = krylovVec M v i`
* The polynomial $p$ is the trivial $X^i$; the lemma is the statement that
  Horner-evaluation against the squared-Krylov sequence reproduces $M^i v$.

### S4 — bound $2^{\lceil \log_2 n\rceil} \ge n$ (≈ 25 lines, no build)

* `theorem squareKrylov_index_bound : ∃ k, 2 ^ k ≥ n` (constructive: `k = n`).
* Pure `Nat`/`Pow` lemma — independent of any matrix machinery.

### S5 — informal complexity comment + outline of layer-3 (no Lean)

* Markdown analysis updating `knowledge.md` and `state.md`: enumerates what a
  future complexity layer needs (`Cost` monad, fast matmul oracle, $\omega$
  axiom). Closes layer (1) + (2) and explicitly defers layer (3).

### S6 — promotion gate (optional)

* Decide whether layers (1)+(2) constitute enough to *open* a gallery entry,
  or whether `cayley-hamilton-minpoly-oq-03-oq-02` should remain in
  research-only state pending complexity infrastructure.

## Risk Notes

1. **Complexity-monad bikeshed.** The natural Mathlib home for a complexity
   monad does not exist; multiple incompatible designs are plausible
   (cost-passing-style, comonadic, free-monad-of-arithmetic-ops). S2-S4 are
   designed to commit to **none** of these and keep the structural layer
   completely independent of any future choice.

2. **Reachable scope is layer 1 + 2, not layer 3.** This must be explicit in
   PRs to avoid the "stated $O(n^\omega)$, formalised $O(n^3)$" pitfall.
   `meta.json` for any gallery promotion should call the status
   `axiomatized` with the complexity claim stated as an assumption, **not**
   `verified`.

3. **No measured speed-up.** Because the underlying `Matrix.mul` is
   $O(n^3)$, any computable instance of the algorithm in Lean would in fact
   run cubically. The asymptotic claim is structural, not measurable.

4. **Naming clash with `nonderogatory_krylov_optimal`.** The "optimal" in
   OQ-03 refers to dimension, not asymptotic time. Keller-Gehrig's
   asymptotic optimality is a separate claim. We use the names
   `squareKrylov` / `subcubicKrylov` to avoid overloading.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `cayley-hamilton-minpoly-oq-03` | Parent: O(n³) Krylov framework (368 lines) |
| `cayley-hamilton-minpoly-oq-04` | Cyclic vector → nonderogatory case; Keller-Gehrig handles this case with no extra work |
| `cayley-hamilton-minpoly-oq-05-oq-01-oq-04*` (WIP01-05) | Block-Krylov refinements — the spiritual ancestors of Keller-Gehrig in our gallery |
| `cayley-hamilton-minpoly-oq-02-oq-03` | Minimum polynomial as gcd via Cayley-Hamilton bridge |

## References

* W. Keller-Gehrig, *Fast algorithms for the characteristic polynomial*,
  Theoretical Computer Science **36** (1985), 309-317.
* M. Giesbrecht, *Nearly optimal algorithms for canonical matrix forms*,
  SIAM J. Comput. **24** (1995), 948-969.
* A. Storjohann, *Algorithms for matrix canonical forms*, PhD thesis,
  ETH Zürich (2000).
* J. von zur Gathen & J. Gerhard, *Modern Computer Algebra*, §12.3
  (Cambridge UP, 2013).
