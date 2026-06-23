# Knowledge Base: bezout-identity-oq-01-oq-01-oq-01-oq-02

HGCD (half-GCD / Schönhage) complexity extension of the binary-GCD bit-complexity
gallery proof. Survey iteration during the 2026-06-13 verification blackout
(Docker down, Aristotle backend 404 — both confirmed live this session), so this
is a build-free OBSERVE→ORIENT survey: no Lean committed.

---

## Problem Understanding

The parent `bezout-identity-oq-01-oq-01-oq-01` (Binary GCD O(log² n) bit complexity)
established the family's working pattern in `BezoutIdentityOQ01OQ01OQ01.lean`:

- `binaryGcdSteps : ℕ → ℕ → ℕ` — an **explicit, computable** step counter mirroring
  the algorithm's recursion (`termination_by a + b`).
- `binaryGcdSteps_le_log` — the **proved** O(log n) step bound (Part 1, 0 sorries).
- `stepBitOps`, `totalBitOps`, `binaryGcd_log_sq_bound` — per-step and total bit-op
  bounds; the closing Θ/Big-O statement is **bounded/axiomatized** (Part 2).

The OQ asks: does this extend to the HGCD algorithm of Schönhage, giving
`O(M(n) log n)` where `M(n)` is the integer-multiplication cost, via the recurrence
`T(n) = 2 T(n/2) + M(n)`? The Seeker statement itself names three sub-tasks:
(a) HGCD's invariant that 2×2 integer matrices encode partial Euclidean steps,
(b) the Master theorem in Lean (**currently absent from Mathlib**),
(c) parametrization over the multiplication primitive `M`.

### The key judgement (the survey's value)

The ask conflates a **tractable, build-free core** with a **cost-model-gated remainder**.
This is the same shape as the reframes used on `chinese-remainder-...-oq-01-oq-02`
(Garner: no Big-O cost monad → exact `Nat` op-counter with closed form) and
`erdos-szekeres-oq-02` (noncomputable spec → computable equality + exact comparison
count). Decompose:

- **Part (a) — the matrix invariant — is genuine, constructive, blackout-buildable
  linear algebra.** It is NOT gated on the Master theorem or on any cost model.
  This is the correct first compile and the real deliverable of the OQ.
- **Parts (b)+(c) — the Θ(M(n) log n) asymptotic via the Master theorem, parametric
  over `M` — are the cost-model-gated trap**, the same class as the parent's
  axiomatized Part 2, as `binary-gcd-...-oq-04-oq-03` (Brent average-case constant),
  and as `erdos-szekeres-oq-02`'s Θ(n log n) lower bound. Out of scope until Mathlib
  grows a Master/Akra–Bazzi theorem. Worse: `T(n)=2T(n/2)+Θ(n)` is the **critical
  case** of the Master theorem (the Θ(n log n) case), the hardest to formalize.

So the survey carves the precise tractable sub-claim out of the intractable
asymptotic, rather than reporting "blocked: needs Master theorem."

---

## Insights

### I1 — The HGCD matrix invariant is the integer continuant/convergent recurrence

A single Euclidean step `(r_{i-1}, r_i) ↦ (r_i, r_{i-1} - q_i r_i)` is left
multiplication of the column `(r_{i-1}, r_i)ᵀ` by the **quotient matrix**
`Q(q_i) = !![0, 1; 1, -q_i]` over `ℤ`. Hence for the remainder sequence
`r_0 = a, r_1 = b, r_{i+1} = r_{i-1} - q_i r_i`:

    (r_i, r_{i+1})ᵀ = Q(q_i) · Q(q_{i-1}) · … · Q(q_1) · (a, b)ᵀ.

Write `R_k = Q(q_k) ⋯ Q(q_1)`. The invariant has two provable halves:
- **`mulVec` correctness:** `R_k.mulVec ![a, b] = ![r_k, r_{k+1}]` (induction on k).
- **Determinant:** `det (Q q) = -1`, so `det R_k = (-1)^k` (by `Matrix.det_mul` +
  `Matrix.det_fin_two`). The entries of `R_k` are (up to sign) the Bézout cofactors
  `s_k, t_k` — i.e. the **continuants** `K(q_1,…,q_k)`, exactly what the extended
  Euclidean algorithm computes. This det = ±1 is what makes `R_k` unimodular, which
  is what lets HGCD splice a partial matrix into a recursive call.

### I2 — Mathlib already proves the field-level analogue (but the ℤ route is cleaner)

`Mathlib/Algebra/ContinuedFractions/Determinant.lean` proves
`determinant : Aₙ·B_{n-1} − A_{n-1}·Bₙ = (−1)ⁿ` for the continuant numerators/
denominators `A, B` of a `GenContFract` over a field `K`
(`ContinuantsRecurrence.lean` gives `nums_recurrence`/`dens_recurrence`). This *is*
the convergent-matrix determinant relation. **However**, that machinery lives over a
`DivisionRing`/field with `GenContFract` and `Pair K`; bridging it to integer
Euclidean quotients is bookkeeping (a/b's continued fraction = its Euclidean
quotient sequence, but the types differ). The practical first compile works
**directly with `Matrix (Fin 2) (Fin 2) ℤ`** products of `Q(q_i)` and proves
`det = (-1)^k` by induction with `Matrix.det_fin_two`/`Matrix.det_mul` — no detour
through `GenContFract`. Note the field result as the conceptual precedent, formalize
over ℤ.

### I3 — The exact-`Nat`-counter milestone mirrors the parent verbatim

By analogy to `binaryGcdSteps`/`stepBitOps`, define a **computable** HGCD that
returns `(R : Matrix (Fin 2) (Fin 2) ℤ, opCount : ℕ)` where `opCount` counts 2×2
matrix multiplications. The recurrence is then a concrete `Nat` (in)equality
`hgcdOps n ≤ 2 * hgcdOps (n/2) + c * stepBitOps n` — NOT a Big-O statement. This is
the maximal claim provable without a cost-model. The jump from this `Nat` recurrence
to the closed form `Θ(M(n) log n)` is precisely the Master-theorem step that Mathlib
cannot yet take.

---

## Suggested milestones (ACT plan, build-gated until Docker/Aristotle return)

- **MS1 (genuine math, blackout-buildable):** `Q : ℤ → Matrix (Fin 2) (Fin 2) ℤ`,
  the remainder-sequence product `R_k`, and the two invariant lemmas
  (`mulVec` correctness + `det R_k = (-1)^k`). ~40–80 LOC, pure `Matrix`/induction,
  zero Master-theorem dependency. **This is the clean first compile.**
- **MS2 (exact `Nat` counter):** computable HGCD returning `(R, opCount)`, plus the
  `Nat` recurrence inequality `hgcdOps n ≤ 2 hgcdOps (n/2) + c·stepBitOps n`. Reuse
  the parent's `stepBitOps`/`Nat.size`/`Nat.log` lemmas.
- **MS3 (the trap, document only):** `O(M(n) log n)` via the Master theorem
  (critical case `2T(n/2)+Θ(n)`), parametric over `M`. Blocked on Mathlib lacking
  Master/Akra–Bazzi. Mirror the parent's choice to **bound/axiomatize** the closing
  asymptotic rather than overclaim.

---

## Dead Ends

- **DE1 — "needs the Master theorem" is NOT a reason to skip the whole OQ.** The
  Master theorem blocks ONLY MS3 (the asymptotic). MS1/MS2 are independent of it.
  A prior pass had this slug filed "research-level, skip"; that was too coarse.
- **DE2 — Do not route MS1 through Mathlib's `GenContFract` continuants.** The field
  typing (`Pair K`, `DivisionRing`) makes the integer Euclidean bridge more work than
  proving `det = (-1)^k` directly over `Matrix (Fin 2) (Fin 2) ℤ`. Cite the field
  result (I2) as precedent only.
- **DE3 — No Big-O cost monad for `M(n)`.** As with Garner and binary-gcd-Brent,
  Mathlib has no cost model; the parametric multiplication cost `M` and the Θ bound
  cannot be stated as asymptotics — only as explicit `Nat` op-counts (MS2).
