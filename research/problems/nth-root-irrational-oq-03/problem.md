# Problem: Transcendence — Hermite-Lindemann / Lindemann-Weierstrass

**Slug**: nth-root-irrational-oq-03
**Created**: 2026-05-12
**Status**: Active (S1 OBSERVE)
**Source**: gallery-gap (parent: `nth-root-irrational`)
**Wiedijk-100**: #52 (Transcendence of $e$) and #53 (Transcendence of $\pi$)

## Problem Statement

### Formal Statement

**Hermite–Lindemann (1882).** For every nonzero algebraic $\alpha \in \overline{\mathbb{Q}}$, $e^{\alpha}$ is transcendental over $\mathbb{Q}$ (equivalently, $\Z$).

**Lindemann–Weierstrass (1885).** For algebraic numbers $\alpha_1, \dots, \alpha_n$ which are linearly independent over $\mathbb{Q}$, the values $e^{\alpha_1}, \dots, e^{\alpha_n}$ are algebraically independent over $\mathbb{Q}$.

**Corollaries.**

- $e$ is transcendental (take $\alpha = 1$). Wiedijk #67.
- $\pi$ is transcendental (assume $\pi$ algebraic; then $i\pi$ is algebraic, so $e^{i\pi} = -1$ is transcendental — contradiction). Wiedijk #53.
- $\log \alpha$ is transcendental for algebraic $\alpha \notin \{0,1\}$.
- $\sin \alpha, \cos \alpha, \tan \alpha$ are transcendental for nonzero algebraic $\alpha$.

### Why This Matters

Transcendence of $\pi$ resolved squaring-the-circle (2,000-year-old problem) and is one of the marquee results of 19th-century number theory. The Lindemann–Weierstrass theorem unifies transcendence of $e$ and $\pi$, and it is the founding theorem of modern transcendence theory (Gelfond-Schneider 1934, Baker 1966, $\rho$-adic analogues, Schanuel's conjecture, …).

## Status in This Project (S1 OBSERVE — 2026-05-12)

This slug is **substantially duplicative** of existing project infrastructure:

| Lean file | Lines | Sorries | Axioms | Scope |
|-----------|------:|--------:|-------:|-------|
| `proofs/Proofs/HermiteLindemann.lean` | 390 | 0 | **1 (`hermite_lindemann`)** | Statement of HL + LW; corollary derivations for $e$ and $\pi$ |
| `proofs/Proofs/eTranscendental.lean` | 304 | 1 | 0 | Transcendence of $e$ (Hermite 1873 line of proof) |
| `proofs/Proofs/ETranscendentalOQ01.lean` | 538 | 1 | 0 | Strong form: $1, e, e^2, \dots, e^n$ are $\Q$-linearly independent |
| `proofs/Proofs/ETranscendentalOQ02.lean` | 715 | 1 | 0 | Irrationality measure $\mu(e) = 2$ (via continued fraction $[2;1,2k,1]$) |
| `proofs/Proofs/ETranscendentalOQ03.lean` | 219 | 0 | **2** | $\mu(e) = 2$ via Liouville framework (uses 2 deep axioms) |
| `proofs/Proofs/PiTranscendental.lean` | 457 | 1 | 0 | Transcendence of $\pi$ |

The "open question 03" framing under `nth-root-irrational` (which is about irrationality of $\sqrt[n]{k}$ for $k$ not a perfect $n$-th power, an *algebraic* question) is **orthogonal** to Hermite–Lindemann / Lindemann–Weierstrass (a *transcendence* question on a different parent).

### Mismatch With Parent

Parent `nth-root-irrational` formalizes:

$$
p(x) \in \mathbb{Z}[x] \text{ irreducible over } \mathbb{Q}, \deg p \geq 2 \implies \text{all roots of } p \text{ are irrational.}
$$

This is a purely **algebraic** result (roots of irreducible polynomials of degree $\geq 2$ lie in proper extensions of $\Q$, hence are not in $\Q$). It says nothing about transcendence — it characterises which algebraic numbers are *also* irrational.

Lindemann–Weierstrass, by contrast, asserts that $e^\alpha$ is **not algebraic at all** for nonzero algebraic $\alpha$. The two problems share only the high-level "expanding our understanding of $\Q$" goal; the techniques (Eisenstein / minimal polynomial vs. Hermite-style auxiliary polynomials + integral estimates) are entirely disjoint.

A more accurate parent for this open question would be `e-transcendental-oq-N` (which already exists, with OQ-01/02/03 filed) or `hermite-lindemann-oq-N` (no slug yet). The current placement reflects a seeker-stage classification choice we inherit but should not be misled by.

### Existing Axiom Inventory (Hermite–Lindemann)

- `HermiteLindemann.lean:147`: `axiom hermite_lindemann : ∀ α : ℂ, α ≠ 0 → IsAlgebraic ℚ α → Transcendental ℤ (Complex.exp α)`
- `ETranscendentalOQ03.lean:114`: `axiom irrational_liouvilleWith_two (x : ℝ) (hx : Irrational x) : LiouvilleWith 2 x` — Dirichlet's approximation lower bound, *provable from Mathlib*
- `ETranscendentalOQ03.lean:154`: `axiom e_not_liouvilleWith_gt_two (p : ℝ) (hp : p > 2) : ¬LiouvilleWith p (exp 1)` — sharp upper bound from regular continued-fraction expansion of $e$

The HL axiom is the deep one: a complete proof requires roughly 800–1500 lines of formalization (auxiliary polynomial $f(x) = x^{p-1}(x-\alpha)^p \cdots (x-n\alpha)^p / (p-1)!$, integral analysis $F(x) = \sum_{j \geq 0} f^{(j)}(x)$, prime-selection argument, archimedean integer-vs-bound contradiction).

The two `ETranscendentalOQ03` axioms are routine-Mathlib lemmas (Dirichlet's approximation theorem and a continued-fraction upper bound on the irrationality measure of $e$). They are tractable axiom-elimination targets.

## Strategy

Rather than restart Lindemann–Weierstrass from scratch (which would duplicate the existing 2,600+ lines), this slug's research should focus on **bridge work** between existing infrastructure and current Mathlib:

### Tier A — Axiom Reduction (highest value)

1. **Eliminate `irrational_liouvilleWith_two`** (Dirichlet approximation). Mathlib has `Real.exists_rat_btwn` and `Nat.exists_pos_of_lt`; the Liouville-with-exponent-2 statement should follow from `Irrational.exists_approx_rat_of_pos` or similar Mathlib API.
2. **Eliminate `e_not_liouvilleWith_gt_two`**. Harder — depends on having Mathlib's continued-fraction API match the regular CF expansion of $e$ used in `ETranscendentalOQ02.lean`. Likely needs a 100–200 line Lean proof, possibly with sorries deferred.

### Tier B — Statement Bridges (moderate value)

3. **Bridge `axiom hermite_lindemann` to Mathlib if/when upstream API lands.** Mathlib has had a [Lindemann-Weierstrass formalization PR](https://github.com/leanprover-community/mathlib4/pulls?q=is%3Apr+Lindemann) under active development; once it stabilises, the axiom in `HermiteLindemann.lean` can be discharged. Until then, document the gap and any partial Mathlib hooks (e.g., `Transcendental ℤ` typeclass).
4. **Statement equivalence lemmas.** The exact form of "transcendence over $\Z$" vs "transcendence over $\Q$" vs the algebraic-independence formulation in LW require small bridging lemmas. Some of these may live in Mathlib already (`Transcendental.algMap`).

### Tier C — Pedagogical Documentation (low value but useful)

5. **Cross-reference all transcendence files** in the gallery. The current state has them as separate entries with no `crossReferences`; a unified narrative thread improves discoverability.

## Plan for Subsequent Sessions

| Iteration | Goal | Files Touched | Expected Outcome |
|----------:|------|----------------|------------------|
| 1 (this) | S1 OBSERVE — duplicate detection + scope clarification | `research/problems/nth-root-irrational-oq-03/{problem,knowledge,state}.md`, `src/data/research/problems/nth-root-irrational-oq-03.json` | Doc-only PR documenting overlap + roadmap |
| 2 | S2 ACT — discharge `irrational_liouvilleWith_two` axiom | `proofs/Proofs/ETranscendentalOQ03.lean` (replace `axiom` with `theorem … := by …`) | Axiom count 2 → 1 on this file |
| 3 | S3 — bridge LW statement equivalences | `proofs/Proofs/HermiteLindemann.lean` (add `equiv` lemmas, no new content) | Improved API surface |
| 4 | S4 — discharge `e_not_liouvilleWith_gt_two` if tractable, or document blocker | `proofs/Proofs/ETranscendentalOQ03.lean` | Either axiom count 1 → 0 or BLOCKED with justification |

## References

- **Hermite, C.** (1873) *Sur la fonction exponentielle*. Comptes Rendus 77, 18–24, 74–79.
- **Lindemann, F.** (1882) *Über die Zahl π*. Math. Ann. 20, 213–225.
- **Weierstrass, K.** (1885) *Zu Lindemann's Abhandlung*. Sitz. Berlin Akad.
- **Baker, A.** (1990) *Transcendental Number Theory*, CUP. Ch. 1–2 cover Hermite-Lindemann; Ch. 6 covers Baker's theorem (generalization).
- **Niven, I.** (1956) *Irrational Numbers*, Carus Math. Monographs 11. Has a clean accessible proof.
- Mathlib: `Mathlib.NumberTheory.Transcendental.Liouville.*` (Liouville's constructions); `Mathlib.Data.Real.Pi.Irrational` (`Real.pi_irrational`).

## Open Questions Generated This Iteration

None this iteration — S1 OBSERVE focuses on duplicate detection and roadmap. Open questions may emerge from S2/S3 axiom-discharge attempts.
