# Knowledge Base: hurwitz-theorem-oq-03-oq-01-wip-01

Completing the "only-if" direction of Hurwitz's theorem for `NormedDivisionRing`
(`Proofs/HurwitzOnlyIf.lean`).

---

## Problem Understanding

Target file `Proofs/HurwitzOnlyIf.lean` contains **exactly one real `sorry`**:
`hurwitz_only_if_ring` — a finite-dimensional normed division ring `A` over `ℝ` has
`finrank ℝ A ∈ {1,2,4,8}`. (A `grep -c sorry` returns 4, but three of those are the
word "sorry" inside docstrings; only `hurwitz_only_if_ring` is an actual proof hole.)

Because `NormedDivisionRing` is **associative**, this sorry is precisely **Frobenius'
theorem**: the answer is in fact `{1,2,4}` (ℝ, ℂ, ℍ); the octonions are excluded because
they are non-associative. Proving `{1,2,4}` suffices since `{1,2,4} ⊆ {1,2,4,8}`.

Already **verified (0 sorries)** in the file and reusable:
- `finrank_normed_field_eq_one_or_two`, `hurwitz_field_case` — the commutative/field case
  via Gelfand–Mazur (`NormedAlgebra.Real.nonempty_algEquiv_or`).
- `minpoly_natDegree_le_two` — every element's minimal polynomial has degree ≤ 2
  (irreducible real polynomials have degree ≤ 2).
- `exists_quadratic` — `∀ a, ∃ p q : ℝ, a^2 = p•a + q•1`.
- `exists_real_shift_sq_scalar` — `∀ a, ∃ c r : ℝ, (a - c•1)^2 = r•1` (completing the square).
- `eq_smul_one_of_sq_eq_nonneg_smul` — `b^2 = r•1 ∧ r ≥ 0 ⟹ b ∈ ℝ•1` (no zero divisors).

So Frobenius **Steps 1 and 2 are done**. Only **Step 3** (the global structure argument)
remains.

---

## Insights

### The one remaining sorry is Frobenius Step 3 — a precise decomposition

Let `A` be a finite-dim associative normed division ℝ-algebra. Define the imaginary set
`ImA := {a : A | ∃ r : ℝ, r ≤ 0 ∧ a^2 = r • 1}` (equivalently `a^2 ∈ ℝ≤0 • 1`).

The remaining work splits into these intermediate lemmas (roadmap for next session /
Aristotle). None is in Mathlib; all are elementary given Steps 1–2:

1. **`realPart` is well-defined.** From `exists_real_shift_sq_scalar`, each `a` has `c(a) ∈ ℝ`
   with `(a - c(a)•1)^2 ∈ ℝ•1`. Uniqueness of `c(a)`: if `c, c'` both work, subtracting shows
   a nonzero real multiple of `1` lies in `ImA`, impossible unless the coefficient is `0`
   (no-zero-divisors + char 0). Gives `re : A → ℝ`, `re 1 = 1`.

2. **Anticommutator lands in `ℝ•1` (polarization) — THE KEYSTONE.** For `x, y ∈ ImA`,
   `x*y + y*x ∈ ℝ•1`. Proof: `(x+y)^2 - x^2 - y^2 = xy + yx`; each square is `scalar + linear•(·)`
   and the linear parts cancel for imaginary inputs. Establish this FIRST — it makes `re`
   additive/linear and `ImA` a subspace.

3. **`ImA` is an ℝ-subspace and `A = ℝ•1 ⊕ ImA`.** `ImA = ker re` once `re` is linear;
   `x ∈ ImA ↔ re x = 0 ↔ x^2 ∈ ℝ≤0•1` (sign from `eq_smul_one_of_sq_eq_nonneg_smul`:
   a positive square scalar forces `x ∈ ℝ•1`).

4. **`B(x,y) := -(scalar of x*y + y*x)/2` is a positive-definite symmetric bilinear form on
   `ImA`.** Symmetric clear; `B(x,x) = -x^2` as a scalar `= -r ≥ 0`, and `> 0` for `x ≠ 0`
   (division ring ⟹ `x^2 ≠ 0`).

5. **`finrank ℝ ImA ∈ {0,1,3}`, hence `finrank ℝ A ∈ {1,2,4}`.** Classical finish: if
   `dim ImA ≥ 2`, `B`-orthonormal `i,j` give `i^2=j^2=-1`, `ij=-ji`, `ij ∈ ImA`, `(ij)^2=-1`,
   so `⟨i,j,ij⟩ ≅ ℍ` (dim 3). A fourth orthonormal `k` makes `ijk` central with `(ijk)^2=+1`,
   so `(ijk-1)(ijk+1)=0` contradicts no-zero-divisors. Hence `dim ImA ≤ 3`, and combined with
   the ℍ-subalgebra `dim ImA ∈ {0,1,3}`.

### Reduction provable NOW (does not need Step 3) — recommended first commit
The **commutative subcase** of `hurwitz_only_if_ring` is already covered: a commutative
`NormedDivisionRing` is a `NormedField`, so `hurwitz_field_case` applies verbatim. Adding
`hurwitz_only_if_ring_comm` (hypothesis `∀ x y, x*y = y*x`) is a clean, self-contained lemma —
build a `NormedField` instance via `letI` from commutativity and reuse `hurwitz_field_case`.
Lowest-risk verifiable increment when tooling returns.

---

## Dead Ends / Non-starters

- **Cannot delegate cleanly to `HurwitzTheorem.hurwitz_only_if` axiom.** It is stated for
  `NSquareIdentity n`, and the reduction `NormedDivisionRing A → NSquareIdentity (dim A)`
  (orthonormal basis + transport of multiplication) is itself substantial and unformalized.
- **No Mathlib Frobenius.** As of 2026-07, Mathlib has Gelfand–Mazur
  (`Analysis.Normed.Algebra.GelfandMazur`) but NOT the classification of finite-dimensional
  real division algebras nor the Clifford / Radon–Hurwitz machinery. Step 3 must be built
  locally (est. 250–450 lines, elementary but long).

---

## Session Log

### 2026-07-04 (Session 1, researcher-8) — ORIENT

**Mode**: FRESH. **Outcome**: oriented (no code committed).

- Identified the single real sorry (`hurwitz_only_if_ring`); confirmed it is Frobenius'
  theorem (associative ⟹ `{1,2,4}`), with Steps 1–2 already verified in-file.
- Produced the Step-3 decomposition above (keystone = anticommutator polarization) plus a
  provable-now commutative reduction.
- **Tooling blocker**: BOTH verification paths down this session — local Docker build unsafe
  (host swap 98% full, 81/83 GB; SIGBUS-135 risk that can crash the host) and the Aristotle
  MCP returned `{"status":"error","message":"Resource not found."}` even on a trivial
  `1+1=2` sorry. No Lean written/committed (would be unverifiable — violates honesty policy).
- **Next session**: when a tool is available, (a) commit `hurwitz_only_if_ring_comm` first
  (provable now via Gelfand–Mazur), then (b) target keystone lemma (2), the anticommutator
  polarization; or submit `hurwitz_only_if_ring` to Aristotle noting it is Frobenius' theorem
  with Steps 1–2 supplied as context.
