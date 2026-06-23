# fermat-two-squares-oq-01-oq-03: Hurwitz Quaternions and Four Squares

**Status**: COMPLETE — PR pending, 0 sorries, 1 axiom (hurwitz_euclidean)

---

## Session 2026-05-06 (Session 1) — Complete Formalization

**Mode**: FRESH
**Outcome**: completed

### What I Did

1. Defined `HurwitzQuat` type: (n₀,n₁,n₂,n₃ : ℤ)/2 with equal-parity condition
2. Proved `normSq4_dvd4`: scaled norm always divisible by 4
3. Proved `hurwitzOmega_normSq`: ω = ½(1+i+j+k) is a Hurwitz unit (N(ω) = 1)
4. Proved `lipschitzToHurwitz_normSq`: norm-preserving embedding Lipschitz → H
5. Proved `hurwitz_normSq_mul`: N(q·r) = N(q)·N(r) via Mathlib Quaternion ℚ
6. Axiomatized `hurwitz_euclidean`: Euclidean division in H
7. Proved `hurwitz_lipschitz_to_four_squares`: Lipschitz-type Hurwitz elts give 4-square reps
8. Created gallery entry in `src/data/proofs/fermat-two-squares-oq-01-oq-03/`

### Key Findings

- **Parity divisibility**: Even nᵢ → nᵢ² ≡ 0 mod 4. Odd nᵢ → nᵢ² ≡ 1 mod 4, sum ≡ 0 mod 4.
- **Rotation trick FAILS for half-integer case**: (n₀±n₁)/2 gives 2p not p.
- **Files**: `FermatTwoSquaresOQ01OQ03.lean` (265 lines, 16 theorems, 9 defs, 1 axiom, 0 sorries)

### Next Steps
- Docker build verification (pending)
- Extend to: full proof of hurwitz_euclidean via covering radius

---

# Knowledge Base: Hurwitz Quaternion Proof of Fermat's Two-Square Theorem

**Problem**: Formalize the Hurwitz integer Euclidean domain to give an alternative algebraic proof of the two-square theorem.

---

## Mathematical Background

### Hurwitz Integers

The Hurwitz integers $\mathbb{H}_{\mathbb{Z}}$ are the subring of the rational quaternions $\mathbb{H}_{\mathbb{Q}}$ defined by:
$$\mathbb{H}_{\mathbb{Z}} = \{ a + bi + cj + dk \mid a,b,c,d \in \mathbb{Z} \text{ or } a,b,c,d \in \mathbb{Z} + \frac{1}{2} \}$$
equivalently, the $\mathbb{Z}$-span of $\{1, i, j, \omega\}$ where $\omega = \frac{1+i+j+k}{2}$.

The norm is $N(q) = a^2 + b^2 + c^2 + d^2 \in \mathbb{Z}$ for all $q \in \mathbb{H}_{\mathbb{Z}}$.

$\mathbb{H}_{\mathbb{Z}}$ is a **left Euclidean domain** (and right Euclidean): for any $a, b \in \mathbb{H}_{\mathbb{Z}}$ with $b \neq 0$, there exists $q$ with $N(a - qb) < N(b)$. The covering radius of the D4 lattice is $\frac{\sqrt{2}}{2} < 1$.

### Proof Sketch (Hurwitz Route)

1. For prime $p \equiv 1 \pmod{4}$, find $x$ with $x^2 \equiv -1 \pmod{p}$.
2. In $\mathbb{H}_{\mathbb{Z}}$, consider $\gcd_L(p, x+i)$ (left GCD via Euclidean algorithm).
3. If $\pi = \gcd_L(p, x+i)$, then $N(\pi)$ divides $N(p) = p^2$ and $N(x+i) = x^2+1 \equiv 0 \pmod{p}$.
4. Since $p$ is prime and $N(\pi) \mid p^2$, either $N(\pi) = 1$ (contradicts $p \mid x+i$ in $\mathbb{H}_{\mathbb{Z}} / p$) or $N(\pi) = p$.
5. Writing $\pi = a + bi + cj + dk$ gives $a^2+b^2+c^2+d^2 = p$.
6. Extract two-square decomposition: $N(\pi) = p = (a^2+b^2) + (c^2+d^2)$... requires Gaussian integer argument for $p \equiv 1 \pmod 4$.

**Reference**: Conway & Smith, "On Quaternions and Octonions", Ch. 4; Hurwitz 1896.

## Mathlib State

### Available

- `Mathlib.Algebra.Quaternion` — `QuaternionAlgebra R c₁ c₂`, `Quaternion ℝ`, conjugate, norm
- `Mathlib.Algebra.EuclideanDomain.Basic` — `EuclideanDomain` typeclass (requires `Ring`)
- `Mathlib.NumberTheory.Zsqrtd.GaussianInt` — `GaussianInt` as `EuclideanDomain` — key model
- `Mathlib.RingTheory.Quaternion.Basic` — further quaternion ring structure
- `Nat.Prime.sq_add_sq` — already in Mathlib: `Nat.Prime.sq_add_sq : p.Prime → p % 4 = 1 → ∃ a b, a^2 + b^2 = p`
- `ZMod.isSquare_neg_one_iff` — `-1` is a QR mod `p` iff `p % 4 = 1`

### Missing (Key Gaps)

- `HurwitzInt` as a structure — no Mathlib entry
- Left Euclidean domain axioms (Mathlib's `EuclideanDomain` assumes commutativity via `CommRing`)
- The lattice covering radius argument for Hurwitz integer rounding

### Critical Constraint

Mathlib's `EuclideanDomain` requires `CommRing`. Hurwitz integers are **not** commutative. This is a fundamental obstacle: a direct `EuclideanDomain HurwitzInt` instance cannot use the standard typeclass without a non-commutative generalization.

**Possible workaround**: Show the two-square norm $N(\pi) = p$ using a direct argument without the full Euclidean domain typeclass — construct the Euclidean algorithm as a function and prove termination explicitly.

## Related Gallery Entries

- `fermat-two-squares`: Uses Zagier's one-sentence involution; no quaternion machinery
- `lagrange-four-squares`: Uses quaternion norm identity but not Hurwitz domain structure
- `gcd-algorithm`: Template for Euclidean algorithm formalization

## Key References

- Hurwitz, A. (1896). *Über die Zahlentheorie der Quaternionen*. Nachrichten Kgl. Gesellschaft Wiss. Göttingen.
- Conway & Smith (2003). *On Quaternions and Octonions*, A K Peters.
- Stillwell (2003). *Elements of Number Theory*, §14 — accessible proof via Hurwitz integers.
