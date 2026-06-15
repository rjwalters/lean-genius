# Knowledge Base: pell-equation-oq-05

Norm Equations in Number Fields of Degree > 2.

---

## Problem Understanding

Pell's equation $x^2 - Dy^2 = 1$ is the norm-one equation
$N_{\mathbb{Q}(\sqrt D)/\mathbb{Q}}(x + y\sqrt D) = 1$. Its cyclic solution chain is the
rank-1 case of **Dirichlet's unit theorem**
$\mathcal{O}_K^\times \cong \mu_K \times \mathbb{Z}^{r_1 + r_2 - 1}$.
The open question asks for the higher-degree analogue: for $K$ of degree $n>2$, the
structure of $N_{K/\mathbb{Q}}(\xi) = m$ for $\xi \in \mathcal{O}_K$.

---

## Insights (Session 2, ORIENT — sympy-verified)

All claims below are checked from first principles by
`verify_norm_equations.py` (reproducible, Docker-independent). It does not plug in
reference values: signatures come from counting roots, norms from determinants of
multiplication matrices, units from actual ring products.

### 1. Rank, not degree, controls the number of fundamental units

| field | min poly | $(n,r_1,r_2)$ | unit rank $r_1{+}r_2{-}1$ |
|-------|----------|---------------|----------------------------|
| $\mathbb{Q}(\sqrt2)$ | $x^2-2$ | $(2,2,0)$ | **1** (classical Pell) |
| $\mathbb{Q}(\sqrt{-5})$ | $x^2+5$ | $(2,0,1)$ | 0 (finite unit group) |
| $\mathbb{Q}(\sqrt[3]2)$ | $x^3-2$ | $(3,1,1)$ | **1** (one complex place!) |
| $x^3-3x-1$ (cyclic cubic) | $x^3-3x-1$ | $(3,3,0)$ | **2** (two fund. units) |
| $\mathbb{Q}(\zeta_5)$ | $\Phi_5$ | $(4,0,2)$ | 1 |

Key realization: $\mathbb{Q}(\sqrt[3]2)$ has degree 3 but still rank 1 — its
signature $(1,1)$ has a single complex place. A *totally real* cubic ($x^3-3x-1$,
conductor 9) jumps to rank 2: genuinely **several fundamental units**, the real
novelty beyond Pell. The identity $r_1 + 2r_2 = n$ holds in every case.

### 2. The cubic norm form is a determinant (formalizable definition)

For $K=\mathbb{Q}(\sqrt[3]2)$, $t^3=2$, the norm of $\xi=a+bt+ct^2$ is
$\det$ of multiplication-by-$\xi$ on the power basis $\{1,t,t^2\}$:
$$N(a+bt+ct^2) = a^3 + 2b^3 + 4c^3 - 6abc,$$
derived (not assumed) from the multiplication matrix with columns
$\xi\cdot1,\ \xi\cdot t,\ \xi\cdot t^2$. This is the cleanest route to a Lean
formalization (`Algebra.norm` = det of the multiplication map).

### 3. Explicit fundamental unit of $\mathbb{Z}[\sqrt[3]2]$ and the Pell chain

$u = t-1$ has $N(u)=1$; its inverse is $u^{-1}=t^2+t+1$, verified by
$(t-1)(t^2+t+1)=t^3-1=1$. Every power $u^k$ has norm 1, producing the
higher-degree analogue of the Pell chain:
$u^2=(1,-2,1)$, $u^3=(1,3,-3)$, $u^4=(-7,-2,6)$, ... — infinitely many norm-1
solutions, organized as $\langle u\rangle \times \{\pm1\}$.

### 4. $N(\xi)=m$: finitely many classes mod units

$N(t)=2$, so $\xi=t$ solves $N(\xi)=2$; the coset $t\cdot u^k$ gives infinitely
many solutions in a **single** $\mathcal{O}_K^\times$-orbit ($\mathbb{Z}[\sqrt[3]2]$
has class number 1). General principle: solutions of $N(\xi)=m$ biject (up to units)
with integral ideals of norm $|m|$ — finitely many — so there are finitely many
solution classes. This is the $S$-unit/class-group finiteness packaging.

### 5. Pell recovered

$\mathbb{Q}(\sqrt2)$: $N(p+q\sqrt2)=p^2-2q^2$ (det), fundamental solution $(3,2)$,
Brahmagupta chain $(3,2)\to(17,12)\to(99,70)\to(577,408)$ all satisfy
$x^2-2y^2=1$. This **is** the parent `pell-equation` entry — the rank-1 special case.

---

## Mathlib API (located this session)

Module `Mathlib.NumberTheory.NumberField.Units.DirichletTheorem`:
- `NumberField.Units.rank` — unit rank, defined as `card (InfinitePlace K) - 1` ( $= r_1+r_2-1$ ).
- `NumberField.Units.rank_modTorsion` — $\mathbb{Z}$-rank of $(\mathcal{O}_K)^\times / \mathrm{torsion} = $ `card (InfinitePlace K) - 1`.
- `NumberField.Units.fundSystem` — a fundamental system of units.
- `NumberField.Units.basisModTorsion` — a $\mathbb{Z}$-basis of $(\mathcal{O}_K)^\times / \mathrm{torsion}$.

Supporting: `Algebra.norm`, `RingOfIntegers`, `NumberField.ClassNumber` / `ClassGroup`
(finiteness). The deep theorem is present; the work is **specialization + packaging**.

---

## Infrastructure Assessment

**Needed**: instantiate the abstract rank theorem for a concrete cubic; an explicit
fundamental-unit witness; finiteness-of-classes packaging.
**Decision**: BUILD (specialization), but **Docker-gated this session** — `lake build`
is unavailable, so no `.lean` was written. The ORIENT survey + reproducible sympy
verification de-risk the eventual ACT step.

---

## Dead Ends / Cautions

- Computing an *explicit regulator* for the cubic is not needed for the rank/finiteness
  statements and should be avoided as a rabbit hole.
- Mathlib does **not** ship explicit fundamental units for named fields; proving
  $t-1$ generates $\mathcal{O}_K^\times$ modulo torsion is manual (bounded, but real).

---

## Next Steps

1. **ACT (Docker-gated)**: `Proofs/PellEquationOQ05.lean` — instantiate
   `NumberField.Units.rank` for $K=\mathbb{Q}(\sqrt[3]2)$, prove rank $=1$ from signature $(1,1)$.
2. Recover-Pell lemma: real quadratic $\Rightarrow$ rank 1 (ties to parent).
3. Cubic norm via `Algebra.norm` / det; verify $N(t-1)=1$.
4. State finiteness of $N(\xi)=m$ classes via `ClassGroup` finiteness + `Units`.
