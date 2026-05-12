# `inverse-galois-d4-oq-03` — Knowledge map

## Primary references

### Foundational

1. **A. Capelli**, *Sulla riduttibilità delle equazioni algebriche*, Nota II, Atti Accad. Sci. Fis. Mat. Napoli **3** (1897). Capelli's irreducibility theorem for $X^n - a$ — the prerequisite for any Galois group computation.

2. **N. Jacobson**, *Basic Algebra I*, 2nd ed., W.H. Freeman (1985), §4.10. Standard textbook treatment of binomial Galois groups including the metacyclic embedding $G_n(a) \hookrightarrow \mathbb{Z}/n \rtimes (\mathbb{Z}/n)^{\times}$.

### Classification papers

3. **W. Y. Velez**, *On normal binomials*, Acta Arithmetica **36** (1979/80), 113–124. Identifies when $X^n - a$ is normal (i.e., its splitting field equals $\mathbb{Q}(\sqrt[n]{a})$) — a necessary condition for many "small" Galois groups including dihedral.

4. **A. Schinzel**, *Polynomials with Special Regard to Reducibility*, Encyclopedia of Mathematics and its Applications **77**, Cambridge University Press (2000), §2. Comprehensive treatment of $X^n - a$ reducibility, including the role of $-4b^4$ exception.

5. **L. C. Kappe, B. Warren**, *An elementary test for the Galois group of a quartic polynomial*, American Mathematical Monthly **96** (1989), 133–137. Explicit discriminant-based criteria for $n = 4$.

### Surveys and exposition

6. **D. Cox**, *Galois Theory*, 2nd ed., Wiley (2012), §8.6. Detailed exposition of $X^n - a$ over $\mathbb{Q}$ with explicit Galois group calculations for small $n$.

7. **K. Conrad**, "Galois groups of the splitting fields of separable polynomials." Online expository notes (https://kconrad.math.uconn.edu/blurbs/galoistheory/separable2.pdf). Worked examples for $n \in \{3, 4, 5, 6, 8\}$.

## Mathlib API status (as of `mathlib4 v4.26.0`)

### Present infrastructure

| API | File | Notes |
|---|---|---|
| `Polynomial.X_pow_sub_C` | `Mathlib.Algebra.Polynomial.Lifts` | The polynomial $X^n - c$ as a `Polynomial` |
| `Polynomial.X_pow_sub_C_ne_zero` | `Mathlib.FieldTheory.SplittingField.Construction` | Nonvanishing |
| `IsSplittingField` | `Mathlib.FieldTheory.SplittingField.IsSplittingField` | Abstract splitting field interface |
| `Polynomial.Gal` | `Mathlib.FieldTheory.PolynomialGaloisGroup` | $\operatorname{Gal}(f/K)$ as a group |
| `IsPrimitiveRoot` | `Mathlib.RingTheory.RootsOfUnity.Basic` | Primitive $n$-th roots; embedding into splitting field |
| `Polynomial.cyclotomic` | `Mathlib.RingTheory.Polynomial.Cyclotomic.Basic` | $\Phi_n(X)$ |
| `Polynomial.Eisenstein` | `Mathlib.RingTheory.Polynomial.Eisenstein.Basic` | Eisenstein criterion (used in parent for $X^4 - 2$ irreducibility) |
| `AdjoinRoot.lift` | `Mathlib.RingTheory.AdjoinRoot` | Used in parent for $\mathbb{R}$-embedding argument |
| `Polynomial.Monic.irreducible_of_isPrimePow` | `Mathlib.RingTheory.Polynomial.Cyclotomic.Eval` | One ingredient of Capelli for prime-power $n$ |

### Gaps (would need to be built or imported)

| Missing API | Sketch | Difficulty |
|---|---|---|
| Capelli's theorem (full $n$): $X^n - a$ reducible $\Leftrightarrow$ ($\exists p$ prime $\mid n$, $a \in (\mathbb{Q}^{\times})^p$) or ($4 \mid n$ and $a \in -4(\mathbb{Q}^{\times})^4$) | Reduce to prime-power cases via $X^{nm} - a = \prod$ form, then handle $4 \mid n$ Aurifeuillean exception | MEDIUM-HARD; spans $\sim$200 lines. Some pieces exist (`Polynomial.X_pow_sub_C_irreducible` for $n$ prime). |
| `dihedralGroup` definition and `MulEquiv` to known small dihedrals | `Mathlib.GroupTheory.SpecificGroups.Dihedral` exists as `DihedralGroup n` (order $2n$) | LOW; just need to wire it up |
| Metacyclic embedding $G_n(a) \hookrightarrow \mathbb{Z}/n \rtimes (\mathbb{Z}/n)^{\times}$ for general $a$ | Generalize the $n = 4$, $a = 2$ pattern from `InverseGaloisD4.lean` | MEDIUM; $\sim$300 lines, parallel to existing code |
| Galois group order $n \varphi(n)$ when $\sqrt[n]{a} \notin \mathbb{Q}(\zeta_n)$ | Standard, uses primitive root theory | MEDIUM |
| Discriminant-based dihedral test for $n = 4$ (Kappe–Warren) | Explicit polynomial in $a$ determines $D_4$ vs $\mathbb{Z}/4$ vs $V_4$ | LOW for the test predicate; MEDIUM to prove equivalence to abstract Galois group |

## Connection to parent (`inverse-galois-d4`)

The parent gallery proof establishes $D_4$ specifically for $a = 2$, $n = 4$ via:
- Lower bound: $4 \mid |\operatorname{Gal}|$ from Eisenstein irreducibility (Part III-A).
- Upper bound: $\mathbb{R}$-embedding argument, $i \notin \mathbb{Q}(\sqrt[4]{2})$ (Part IV).

This OQ-03 generalises Part IV: instead of $\mathbb{R}$-embedding tricks specific to $a > 0$, we need a uniform criterion. For $a < 0$ (e.g., $a = -2$), $\mathbb{R}$-embedding fails ($X^4 + 2$ has no real root); a different argument is needed, but the abstract conclusion ($D_4$, order $8$) survives by Schinzel's classification.

## Sibling open questions

From the parent's `openQuestions`:
- OQ-01: "Can the full structure of $D_4$ as a semidirect product $\mathbb{Z}/4 \rtimes \mathbb{Z}/2$ be identified in the Galois action?" — group-theoretic identification, complements OQ-03.
- OQ-02: "Can the Galois group of $X^n - p$ be computed for all $n$, $p$ in Lean?" — broader version of OQ-03, asking for *any* Galois group computation (not specifically dihedral).
- OQ-04 (this slug's pool tags): related to general criterion, status `available`.

OQ-03 sits in the *characterization* lane: not asking to compute every Galois group (OQ-02) nor identify the specific $D_4$ semidirect structure (OQ-01), but to give a clean decidable predicate for the dihedral subfamily.

## Tractability assessment

- **Existential difficulty** (low): Schinzel–Velez gives the answer in classical mathematics; no new theory required.
- **Mathlib-formalization difficulty** (medium-high): Capelli's full theorem is not in Mathlib; would need $\sim$200–300 lines just to state and prove the irreducibility prerequisite.
- **Gallery scope** (low for survey, high for full formalization): An S1 OBSERVE describing the criterion + an S2 Lean structure with the criterion as a `def`/`prop` and a sorry-bearing equivalence to the parent's $D_4$ realization is achievable. A complete formal proof of the Schinzel–Velez classification is a multi-month effort.

## Suggested next iteration scope (S2)

If pursued, S2 should produce a **non-building scaffold** in a new file `proofs/Proofs/InverseGaloisD4OQ03.lean` containing:
1. `def isDihedralCriterion (n : ℕ) (a : ℚ) : Prop := ...` — the decidable criterion above (Capelli-irreducibility + cyclotomic-collapse).
2. `theorem isDihedralCriterion_iff : isDihedralCriterion n a ↔ ∃ m, Nonempty (Gal(X^n - a/ℚ) ≃* DihedralGroup m) := by sorry` — the main equivalence.
3. `example : isDihedralCriterion 4 2 := by decide` — sanity check tying back to the parent's $D_4$ result.

The `sorry` in (2) carries the full Schinzel–Velez theorem; this is acceptable as a research scaffold and matches the gallery's `axiomatized` status pattern.
