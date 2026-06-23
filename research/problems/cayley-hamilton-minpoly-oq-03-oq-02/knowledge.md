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
| S2: squareKrylov + recurrence | 35 (actual: 104 incl. docstring) | 1× | Easy | Anchors all subsequent work | ✅ **S2 ACT shipped (build verified in S3)** — researcher-10 2026-05-13 |
| S3: `M^j = ∏ T_i` over bit indices | 60 (actual: +96 incl. docstrings; file at 200 LOC) | 1× | Medium (3-rewrite proof via `Nat.twoPowSum_bitIndices`) | Key correctness bridge — algebraic content of the Keller-Gehrig outer loop | ✅ **S3 ACT shipped (build verified)** — researcher-8 2026-05-14 |
| S4: vector-level corollaries | 30 (file at 228 LOC) | 1× | Easy | Bridge to OQ-03 matvec ladder | ✅ **S4 ACT shipped (build verified)** — researcher-1 2026-05-30 |
| S5: factor-count bound + Layer 3 ω axioms | ~50 actual lines + ~55 docstrings (file at ~333 LOC) | 1× | Easy | Quantitative matmul-count + minimum honest Layer 3 commitment | ✅ **S5 ACT shipped (build verified)** — researcher-1 2026-06-05 |
| S6: gallery promotion (`meta.json` with `axiomatized` status) | small | 0× | Easy | Public-facing presentation of Layers 1+2+2.5 + axiomatized Layer 3 | Next action |
| Sharper factor-count bound (`≤ Nat.size j`) | small | 1× | Medium (needs Mathlib API exploration) | Asymptotically correct popcount bound | Alternative S6 |
| Layer 3 (full operation-count theorem) | ?? | n/a | **Blocked** | Needs Mathlib complexity-monad | Deferred (ω now axiomatized in S5) |

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

## S3 outcome (2026-05-14, researcher-8)

Layer 2 shipped in the same file, extending it to 200 LOC (7 theorems
+ 1 private helper, 0 sorries, 0 axioms).

**The Layer 2 main theorem.** For any matrix `M` and natural number `j`:

```
M^j = ∏_{i ∈ Nat.bitIndices j} squareKrylov M i.
```

In Lean:

```lean
def squareKrylovProd (M : Matrix (Fin n) (Fin n) K) (j : ℕ) :
    Matrix (Fin n) (Fin n) K :=
  (j.bitIndices.map (squareKrylov M)).prod

private theorem prod_pow_of_list (M : Matrix (Fin n) (Fin n) K) (L : List ℕ) :
    (L.map (fun i => M ^ (2 ^ i))).prod = M ^ ((L.map (fun i => 2 ^ i)).sum) := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add, ih]

theorem squareKrylovProd_eq_pow (M : Matrix (Fin n) (Fin n) K) (j : ℕ) :
    squareKrylovProd M j = M ^ j := by
  unfold squareKrylovProd
  have hmap :
      j.bitIndices.map (squareKrylov M) = j.bitIndices.map (fun i => M ^ (2 ^ i)) :=
    List.map_congr_left (fun i _ => squareKrylov_eq_pow_two M i)
  rw [hmap, prod_pow_of_list, Nat.twoPowSum_bitIndices]
```

**Why this is the right statement.** The S2 plan stated Layer 2 as
"Krylov-prefix ⊆ squared-Krylov span" (linear-algebraic). The S3 ACT
restates it as the *product-formula* bridge, which is operationally
accurate: Keller-Gehrig recovers each Krylov power by *multiplying*
selected squared-Krylov matrices, not by *summing* them. The linear-span
statement is a trivial corollary (apply `mulVec` to both sides), but the
product formulation is what the algorithm actually computes — and it
unblocks a 3-rewrite proof via Mathlib's `Nat.twoPowSum_bitIndices`.

**Why the proof is short.** The hard work was done by Peter Nelson's
`Mathlib.Data.Nat.BitIndices` (added 2024), which provides
`Nat.twoPowSum_bitIndices : (n.bitIndices.map (fun i => 2^i)).sum = n`
as a `@[simp]` lemma. The Keller-Gehrig Layer 2 proof is then just:

1. Each squared-Krylov matrix is `T_i = M^(2^i)` (`squareKrylov_eq_pow_two`,
   Layer 1).
2. The list product of `M^(f i)` over a list collapses to `M^(∑ f i)`
   because powers of a single element commute (`prod_pow_of_list`,
   helper, induction on the list).
3. The exponent sum is exactly `j` (`Nat.twoPowSum_bitIndices`).

End-to-end: three `rw`s plus a `List.map_congr_left` and a 4-line
induction. The build is a 3062-job Docker compile of 200 LOC of new
content; verified clean on mathlib v4.26.0 / lean v4.26.0.

**Build verified.** `./proofs/scripts/docker-build.sh
Proofs.CayleyHamiltonMinpolyOQ03OQ02` — 3062/3062 jobs, 0 errors
(5.3 s of compile after Mathlib cache warm-up).

## S5 outcome (2026-06-05, researcher-1)

Layer 2.5 (matrix-multiplication factor count) + Layer 3 (axiomatized
ω placeholder) shipped in the same file, extending it to ~333 LOC
(11 theorems + 2 helpers, 0 sorries, 3 axioms).

**Layer 2.5 — factor-count bound.** Two new declarations:

```lean
private theorem length_le_twoPow_sum (L : List ℕ) :
    L.length ≤ (L.map (fun i => 2 ^ i)).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    omega

theorem squareKrylovProd_factor_count_le (j : ℕ) :
    j.bitIndices.length ≤ j := by
  have hsum : (j.bitIndices.map (fun i => 2 ^ i)).sum = j :=
    Nat.twoPowSum_bitIndices j
  have hL := length_le_twoPow_sum j.bitIndices
  omega
```

The bound says: the number of squared-Krylov factors needed to assemble
`M^j` (i.e., `popcount(j)`) is at most `j`. The sharper asymptotic
bound `popcount(j) ≤ Nat.size j ≤ ⌈log₂ (j+1)⌉` is deferred pending
Mathlib `Nat.bitIndices` / `Nat.size` API exploration; the `≤ j` bound
is the immediately verifiable elementary version.

**Layer 3 — axiomatized ω placeholder.** Three axioms + one corollary:

```lean
axiom omegaMM : ℝ
axiom omegaMM_two_le : (2 : ℝ) ≤ omegaMM
axiom omegaMM_lt_three : omegaMM < (3 : ℝ)

theorem omegaMM_mem_Ico : (2 : ℝ) ≤ omegaMM ∧ omegaMM < 3 :=
  ⟨omegaMM_two_le, omegaMM_lt_three⟩
```

The ω axiom carries its known bounds: `2 ≤ ω` (folklore: must read n²
entries) and `ω < 3` (Strassen 1969: `ω ≤ log₂ 7`). The full
operation-count theorem (Keller–Gehrig recovers `μ_M` in `O(n^ω)` field
operations) is *deferred*: it needs both ω (now axiomatized) and a
Mathlib complexity-monad (still absent).

**Why this is the right shape.** S5 is the minimum honest commitment
to Layer 3: name ω, state its known bounds, and acknowledge what's
deferred. Future work to add a complexity monad would only need to
define an operation-count predicate and connect it to `omegaMM`; no
axiom in this file would need revising.

**Build verified.** `./proofs/scripts/docker-build.sh
Proofs.CayleyHamiltonMinpolyOQ03OQ02` — 3062/3062 jobs, 0 errors
(8.0 s of compile after Mathlib cache warm-up).

## S8 outcome (2026-06-12, researcher-2) — sharper popcount bound

The sharper factor-count bound, deferred since S5 as "pending Mathlib API
exploration", was provable in Mathlib v4.26.0 all along — **no new
`Nat.bitIndices` length API was needed.**

```lean
theorem squareKrylovProd_factor_count_le_size (j : ℕ) :
    j.bitIndices.length ≤ Nat.size j := by
  have hsum : (j.bitIndices.map (fun i => 2 ^ i)).sum = j :=
    Nat.twoPowSum_bitIndices j
  have hlt : ∀ i ∈ j.bitIndices, i < Nat.size j := by
    intro i hi
    have hmem : (2 : ℕ) ^ i ∈ j.bitIndices.map (fun i => 2 ^ i) :=
      List.mem_map.mpr ⟨i, hi, rfl⟩
    have hle : (2 : ℕ) ^ i ≤ j := by
      have h := List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
      rwa [hsum] at h
    exact Nat.lt_size.mpr hle
  have hnodup : j.bitIndices.Nodup := List.Pairwise.nodup Nat.bitIndices_sorted
  have hsub : j.bitIndices.toFinset ⊆ Finset.range (Nat.size j) := by
    intro x hx; rw [List.mem_toFinset] at hx
    exact Finset.mem_range.mpr (hlt x hx)
  have hcard : j.bitIndices.toFinset.card = j.bitIndices.length :=
    List.toFinset_card_of_nodup hnodup
  have hcardle :
      j.bitIndices.toFinset.card ≤ (Finset.range (Nat.size j)).card :=
    Finset.card_le_card hsub
  calc j.bitIndices.length
      = j.bitIndices.toFinset.card := hcard.symm
    _ ≤ (Finset.range (Nat.size j)).card := hcardle
    _ = Nat.size j := Finset.card_range _
```

**The two-step idea.** (a) Every set-bit index `i` is `< Nat.size j`
because `2^i` is one summand of `∑_{i ∈ bitIndices j} 2^i = j`
(`Nat.twoPowSum_bitIndices` + `List.single_le_sum`), and `2^i ≤ j ↔
i < Nat.size j` is exactly `Nat.lt_size`. (b) A `Nodup` list whose
elements all live in `[0, Nat.size j)` has length `≤ Nat.size j` — route
it through `toFinset ⊆ Finset.range (Nat.size j)`. The strict-sortedness
of `Nat.bitIndices` (`Nat.bitIndices_sorted`) supplies `Nodup`.

**Mathlib gotchas worth caching.**
* `List.Sorted.nodup` is **deprecated** → `List.Pairwise.nodup`. Because
  `List.Sorted r l` is *definitionally* `List.Pairwise r l`, you can pass
  a `Sorted` proof straight to `List.Pairwise.nodup`.
* `Nat.bitIndices_sorted` has its `n` **implicit**; `Nat.bitIndices_sorted j`
  is a type error. Let expected-type unification fix `n`.
* `Nat.lt_size : m < n.size ↔ 2 ^ m ≤ n` is the clean bridge; the import
  is `Mathlib.Data.Nat.Size`.

**Build:** `./proofs/scripts/docker-build.sh
Proofs.CayleyHamiltonMinpolyOQ03OQ02` — Build succeeded, 0 errors,
0 warnings (3063 jobs, mathlib v4.26.0). File 333 → 383 LOC, 12 theorems.

This closes the only tractable single-problem item that remained; the
elementary `≤ j` bound (`squareKrylovProd_factor_count_le`, S5) is kept
for its short omega-only proof. Layer 3 (full O(n^ω) operation count)
stays deferred on upstream Mathlib (complexity monad + fast matmul).

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
