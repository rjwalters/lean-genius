# Knowledge Base: cramers-rule-oq-01-oq-04-oq-03

Faddeev–LeVerrier algorithm as a computable Lean function.
Parent: `cramers-rule-oq-01-oq-04` (`proofs/Proofs/CramersRuleOQ01OQ04.lean`, namespace
`CramersRuleNewton`).

Researcher-6, 2026-07-01 (DESIGN pass; build environment was blocked — no compile).

---

## Findings

### Mathlib does NOT have Faddeev–LeVerrier
`grep -ri "leverrier\|faddeev" Mathlib/` → no hits. So this is a genuine gap, not a
re-export. Mathlib *does* provide the pieces to state and verify it:
- `Matrix.charpoly`, `Matrix.charpoly_natDegree_eq_card`, `Matrix.charpoly_monic`
  (`LinearAlgebra/Matrix/Charpoly/{Basic,Coeff}.lean`)
- `Matrix.trace`, `Matrix.trace_mul_comm`, `Matrix.trace_one`, `Matrix.trace_smul`
  (`LinearAlgebra/Matrix/Trace.lean`)
- `Matrix.aeval_self_charpoly` (Cayley–Hamilton) and `Matrix.trace_eq_neg_charpoly_coeff`.

### The parent file already has the surrounding scaffolding
`CramersRuleOQ01OQ04.lean` defines (over `[CommRing R]`):
- `matPowerSum M k := trace (M^k)` (Newton power sums pₖ)
- `charpolyCoeff M k := (charpoly M).coeff (card n - k)`
- `cayley_hamilton` (proved), `newton_k1/k2/k3` (proved), and **axioms**
  `newton_recurrence_small`, `newton_recurrence_large`, `newton_large_recurrence`,
  and crucially **`faddeev_leverrier_inversion`**.

A computable FL recurrence is exactly the tool to *discharge* `faddeev_leverrier_inversion`
(and to give charpolyCoeff a computable characterization), so this OQ feeds directly back
into the parent.

## The algorithm (canonical form — the seeder's one-line statement is imprecise)

Auxiliary matrices `Mₖ` and scalars `cₖ` for an n×n matrix `A`:

```
M₁ = I
c₁ = -tr(A · M₁) = -tr A
M_{k+1} = A · Mₖ + cₖ · I
c_{k+1} = -(1/(k+1)) · tr(A · M_{k+1})
```

Output: χ_A(t) = tⁿ + c₁tⁿ⁻¹ + … + cₙ ; adj(A) = (-1)ⁿ⁻¹ Mₙ ; det A = (-1)ⁿ cₙ ;
and `M_{n+1} = 0` (equivalent to Cayley–Hamilton). Equivalently cₖ = charpolyCoeff-with-sign.

## Key design constraint: division by k ⇒ NOT a plain CommRing extension

`c_{k+1}` divides tr(...) by `(k+1)`. Over a general `CommRing R` this is unavailable.
Options, in order of cleanliness for Lean:

1. **Work over a field of characteristic 0** (`[Field R] [CharZero R]`), or more generally
   assume `[Invertible (k : R)]` for the k that appear. Cleanest; matches the standard
   statement; still `noncomputable` (uses `charpoly`/`trace` over abstract R) unless R is a
   computable field.
2. **Division-free reformulation** over `[CommRing R]`: prove the *scaled* recurrence
   `(k : R) • cₖ = -tr(A · Mₖ)` and carry the `k·Mₖ` relation, matching the seeder's
   `k·Mₖ = …` framing. This keeps the CommRing generality of the parent but the statement
   is the multiplied-through Newton identity rather than a directly computable `def`.
3. **Over ℚ (or `Matrix _ _ ℚ`)** for a genuinely `#eval`-able computable function.

Recommend **(1)** for the theorem-level "computable function + correctness" deliverable,
with a remark connecting to (2) for the CommRing Newton identity already in the parent.

## Lean structuring plan

The recurrence is *coupled* (Mₖ needs cₖ₋₁; cₖ needs Mₖ). Define a single well-founded
recursion returning the pair, to avoid mutual-recursion friction:

```
-- over [Field R] [CharZero R], A : Matrix n n R
noncomputable def flStep (A : Matrix n n R) : ℕ → Matrix n n R × R
  | 0        => (1, 0)                                  -- (M₁ placeholder, c₀)
  | (k+1)    =>
      let (M, _) := flStep A k
      let M'     := A * M + (flStep A k).2 • (1 : Matrix n n R)  -- careful indexing
      (M', -(k+1 : R)⁻¹ * Matrix.trace (A * M'))
```

(indices need care — pin M₁ = I as the base). Then prove:
- `flCoeff A k = charpolyCoeff A k` (main correctness theorem), by strong induction using
  the Newton recurrence lemmas already in the parent;
- `flStep A n |>.1` gives `(-1)ⁿ⁻¹ • adjugate A` and hence `faddeev_leverrier_inversion`;
- `flStep A (card n) |>.1 * A = det A • 1`-type corollary / termination at n.

## Open experiment (build-gated)
Author `def flStep` + the `flCoeff = charpolyCoeff` correctness theorem over
`[Field R][CharZero R]`, then `#eval` a concrete `Matrix (Fin 2/3) _ ℚ` example. Could not
compile this session (concurrent `lean-build` containers saturate the shared `.lake` volume;
SIGBUS risk — build only when `docker ps | grep lean-build` is empty).

## Dead Ends
- Extending directly over the parent's `[CommRing R]` without an `Invertible (k:R)`
  hypothesis cannot express the `/k` step — must strengthen to a field/char-0 or use the
  scaled division-free identity.
