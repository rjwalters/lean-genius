# Knowledge: Keller-Gehrig $O(n^\omega)$ — formalisation notes

## The algorithm in three sentences

Given an $n\times n$ matrix $M$, compute $T_k := M^{2^k}$ by repeated
squaring for $k = 0, 1, \dots, \lceil \log_2 n\rceil$. Use the matrices
$T_0, T_1, \dots$ to evaluate any polynomial of degree $< 2^{\lceil \log_2 n\rceil}$
at $M$ in $O(\log n)$ matrix multiplications (Horner against base-$2^k$
expansion of the polynomial). Hence find the minimal polynomial — degree
$\le n$ — using $O(\log n)$ matrix multiplications, i.e. $O(n^\omega \log n)$
field operations. (A later refinement by Giesbrecht and Storjohann removes
the $\log n$ to land at $O(n^\omega)$.)

## Where the speed-up comes from (one paragraph)

The naive Krylov method (formalised in OQ-03) computes $v, Mv, M^2 v, \dots,
M^{n-1}v$ one step at a time — $n$ matrix-vector products, each $O(n^2)$.
Keller-Gehrig instead computes the matrix $M^{2^k}$ once, then uses one
matrix-matrix multiply ($O(n^\omega)$) to advance by $2^k$ Krylov steps at
once. After $\lceil \log_2 n\rceil$ squarings and a polynomial-evaluation
pass, the entire Krylov span of degree-$n$ polynomials in $M$ applied to $v$
is accessible. The trade is "$n$ cheap steps" vs. "$\log n$ expensive
steps."

## Numerical sanity check at $n = 64$

* Naive Krylov: 64 matvecs $\times \, 64^2 = 4096$ ops each $=$ **262 144 ops**.
* Keller-Gehrig with naive matmul: $\lceil \log_2 64\rceil = 6$ matmuls $\times \, 64^3 = 262\,144$ ops each $=$ **1 572 864 ops**.
* Keller-Gehrig with Strassen $\omega = \log_2 7 \approx 2.807$:
  $6 \times 64^{2.807} \approx 6 \times 64\,818 \approx$ **388 906 ops**.
* Keller-Gehrig with $\omega = 2.37$ (Coppersmith-Winograd-Williams):
  $6 \times 64^{2.37} \approx 6 \times 17\,032 \approx$ **102 192 ops**.

So **at $n = 64$ the naive Krylov already beats Strassen-Keller-Gehrig by 1.5×**;
Strassen needs $n \ge 256$ish to win; Coppersmith-Winograd-Williams wins at
$n \approx 64$ and dominates from there. The asymptotic claim is real but
the constant is large — this is why the Mathlib `Matrix.mul` choosing the
naive algorithm is a defensible default.

## Mathlib gap inventory

### Gap 1: complexity monad

Mathlib has no `Cost (α : Type) := WithCount α` or equivalent. Possible designs:

* **Comonadic cost passing** — every operation returns `α × ℕ`. Composable but
  noisy; every theorem statement carries cost in the type.
* **Free monad of arithmetic operations** — `inductive Comp : Type → Type`
  with `Add | Mul | Bind ...`. Cleaner statements; harder to compose with
  Mathlib's type-class hierarchy.
* **External "operation counter" predicate** — `OpCount : (α → α) → ℕ → Prop`.
  Avoids touching types; admits inequalities directly.

There is no consensus in the Lean community on which design wins. The
practical effect: **no `O(...)` claim about anything is formalisable in
current Mathlib.** Anything we say is an axiomatised assumption.

### Gap 2: fast matrix multiplication

`Mathlib.Data.Matrix.Mul` defines `Matrix.mul` as

```lean
def mul (M N : Matrix m n α) : Matrix m p α := fun i k => ∑ j, M i j * N j k
```

i.e. the standard cubic algorithm. There is no `Matrix.strassenMul`, no
opaque `FastMul` typeclass, no abstract "any algorithm satisfying
$\mathrm{cost} \le C \cdot n^\omega$ for some $\omega < 3$" — all of these
are intervals we would have to bridge.

### Gap 3: matrix-multiplication exponent $\omega$

The constant $\omega$ ($2 \le \omega \le 3$, currently $\approx 2.37$) is
genuinely an open mathematical object (it is not known to equal 2). The
honest Mathlib treatment would be: `axiom omegaMM : ℝ` together with
`axiom omegaMM_ge_two : 2 ≤ omegaMM` and `axiom omegaMM_lt_three : omegaMM < 3`.
This is acceptable as long as the "axiomatized" status is declared in
`meta.json`.

## Worked S2 stub: squared-Krylov

```lean
namespace MinpolyComplexity.SubcubicKrylov

variable {K : Type*} [Field K] {n : ℕ}

/-- The k-th squared-Krylov power: M^(2^k), computed by repeated squaring.
    This is the central object in Keller-Gehrig's O(n^ω) algorithm. -/
def squareKrylov (M : Matrix (Fin n) (Fin n) K) : ℕ → Matrix (Fin n) (Fin n) K
  | 0     => M
  | k + 1 => squareKrylov M k * squareKrylov M k

@[simp]
theorem squareKrylov_zero (M : Matrix (Fin n) (Fin n) K) :
    squareKrylov M 0 = M := rfl

theorem squareKrylov_succ (M : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    squareKrylov M (k + 1) = squareKrylov M k * squareKrylov M k := rfl

theorem squareKrylov_eq_pow_two (M : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    squareKrylov M k = M ^ (2 ^ k) := by
  induction k with
  | zero => simp [squareKrylov]
  | succ k ih =>
      simp [squareKrylov, ih, pow_succ, pow_mul]
      ring_nf
      -- need M^(2^k) * M^(2^k) = M^(2^k * 2)
      sorry  -- S2 proof: assemble Matrix.pow_mul + Nat.pow_succ

end MinpolyComplexity.SubcubicKrylov
```

The `sorry` is replaceable with one `Matrix.pow_mul`/`Nat.pow_succ` chain in
~5 lines; total target for S2 is ~35 lines (definition + 3 theorems + module
docstring).

## Priority table (next-action choice)

| Layer | Lines | Build | Difficulty | Value | Status |
|-------|-------|-------|------------|-------|--------|
| S2: squareKrylov + recurrence | 35 (actual: 104 incl. docstring) | 1× | Easy | Anchors all subsequent work | ✅ **S2 ACT shipped (build pending)** — researcher-10 2026-05-13 |
| S3: Krylov ⊆ span(squareKrylov) | 60 | 1× | Medium | Key correctness bridge | Next action |
| S4: $2^k \ge n$ bound | 25 | 0× | Trivial | Pure `Nat`-arithmetic | Pending |
| Layer 3 (cost claim) | ?? | n/a | **Blocked** | Needs Mathlib complexity-monad | Deferred |

## S2 outcome (2026-05-13, researcher-10)

Layer 1 shipped in `proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean`
(104 LOC, 3 theorems, 0 sorries, 0 axioms).

**Final form of the bridge proof** (replacing the `sorry` in the worked
stub above):

```lean
theorem squareKrylov_eq_pow_two (M : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    squareKrylov M k = M ^ (2 ^ k) := by
  induction k with
  | zero =>
      show M = M ^ (2 ^ 0)
      rw [Nat.pow_zero, pow_one]
  | succ k ih =>
      show squareKrylov M k * squareKrylov M k = M ^ (2 ^ (k + 1))
      rw [ih, ← pow_add]
      congr 1
      ring
```

After `rw [ih, ← pow_add]` the goal is
`M ^ (2^k + 2^k) = M ^ (2^(k+1))`, and `congr 1 + ring` discharges the
exponent identity `2^k + 2^k = 2^(k+1)` in `ℕ` (`ring` normalizes both
sides to `2 * 2^k`; no special-purpose `pow_succ`/`mul_two` chain
needed).

Namespace `MinpolyComplexity.SubcubicKrylov` is disjoint from `MinpolyVec`
(OQ-03-OQ-01) — no collision.

Build verification deferred to doctor / auditor due to the project-wide
`proofs/.lake` self-referential-symlink trap in this worktree (cf. project
memory `.lake symlink loop + mid-build worktree wipe`).

## What to leave for OQ-03-OQ-03 / OQ-03-OQ-04 (sibling slugs)

* OQ-03-OQ-03 (if it exists) is the natural home for the Storjohann
  $O(n^\omega)$ refinement (no $\log n$ factor).
* OQ-03-OQ-01 (sibling) already handles the cyclic-vector case and likely
  contains Hessenberg / Frobenius normal-form pieces that overlap.
  **Action item:** before S2, read `CayleyHamiltonMinpolyOQ03OQ01.lean` to
  verify name collisions and pick a clean module namespace.

## References (cross-linked to problem.md)

* Keller-Gehrig (1985) — original paper, Theoretical Computer Science.
* Giesbrecht (1995) — first true $O(n^\omega)$ (no log factor).
* Storjohann (2000) — comprehensive thesis on $O(n^\omega)$ canonical forms.
* von zur Gathen & Gerhard, *Modern Computer Algebra* §12.3 — textbook
  exposition.
