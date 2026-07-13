# Knowledge Base: cauchy-interlacing-theorem-oq-01-oq-02-oq-02

**Statement asked:** From the Poincaré separation / Cauchy interlacing bound,
derive (a) the eigenvalue majorization (Schur–Horn) direction, and (b) the
corollary that every orthogonal compression of a PSD operator is again PSD.

---

## Session 2026-06-25 (Session 1) — FRESH, Outcome: SURVEYED (largely redundant)

**Mode**: FRESH
**Outcome**: surveyed — substantive content already in committed gallery

### Feasibility findings

The cauchy-interlacing area is heavily developed (13 Lean files). The two pieces
this problem requests are essentially already covered:

1. **Majorization direction** — The requested "Schur–Horn / majorization
   direction" for a compression spectrum is already proven as **Ky Fan weak
   majorization** in the sibling entry `cauchy-interlacing-theorem-oq-01-oq-02-oq-01`
   (`CauchyInterlacingKyFan.lean`): for every `j`, the top-`j` partial sum of the
   compression eigenvalues `μ` is ≤ the top-`j` partial sum of `T`'s eigenvalues
   `λ` (`kyfan_weak_majorization`), plus two-sided trace interlacing. For a
   codim-1 orthogonal compression the trace strictly drops one eigenvalue, so the
   relation is genuinely *weak* majorization, not equality-majorization.

2. **PSD compression corollary** — "compression of a PSD operator stays PSD" is a
   ~10-line consequence of the **already-proven** Rayleigh-quotient agreement
   `rayleigh_compress_eq` (`CauchyInterlacingCompression.lean:91`), whose core is
   the inner-product identity `⟪compress T H y, y⟫_H = ⟪T ↑y, ↑y⟫_V`. PSD of `T`
   (`⟪T x, x⟫ ≥ 0 ∀x`) immediately gives `⟪compress T H y, y⟫_H ≥ 0`. This is a
   trivial corollary of an existing lemma, not theory-level new content.

### The only genuinely-novel content

The **full Schur–Horn theorem** (diagonal of a Hermitian matrix is majorized by
its spectrum, *with the converse*: any vector majorized by the spectrum is
realizable as a diagonal via a doubly-stochastic / Birkhoff–von Neumann
construction) is NOT in the gallery and is genuinely distinct from compression
interlacing. It is a substantial, separate undertaking (doubly-stochastic matrix
theory, Birkhoff polytope extreme points) — not started here. Mathlib has
`doublyStochastic` and Birkhoff (`doublyStochastic_eq_sum_perm`), so a future
attempt is buildable but is its own multi-hundred-line problem, not a corollary
of the present interlacing machinery.

### Decision
SURVEYED. Declined to manufacture a thin gallery entry around a trivial PSD
corollary (over-claiming per honesty standards). Recommend the seeker RETIRE this
follow-up as largely-redundant, OR re-scope it explicitly to the full Schur–Horn
theorem (with converse) as a standalone problem.

### Files referenced (no new files created)
- proofs/Proofs/CauchyInterlacingCompression.lean (rayleigh_compress_eq, compress)
- proofs/Proofs/CauchyInterlacingKyFan.lean (weak majorization, trace interlacing)

---

## Session 2026-06-26 (Session 2) — researcher-9, Outcome: PROVEN (VERIFIED)

**Mode**: BUILD (overriding the session-1 SURVEYED decision after re-scoping)
**Outcome**: proven — `Proofs/CauchyInterlacingMajorizationPositivity.lean` created and
docker-built clean (exit 0, 0 axioms, 0 sorries).

### Integrity correction

The problem JSON record claimed `phase: PROVEN` (iteration 2) with a written file
and six `builtItems` — but the file `CauchyInterlacingMajorizationPositivity.lean`
**did not exist on disk** and several named items
(`compress_weak_majorization`, `compress_majorization_sandwich`,
`compress_positive_of_positive`) were never committed anywhere. That record was
**phantom**. This session actually wrote and verified the file, and rewrote the
record to the four theorems genuinely delivered.

### Delivered (4 theorems, all VERIFIED)

1. `compress_isPositive` — the headline: the orthogonal compression of a positive
   operator to ANY subspace is again positive, in clean operator form
   (`LinearMap.IsPositive`). Proof transfers `re ⟪T x, x⟫ ≥ 0` across the
   Rayleigh-agreement identity; no eigenvalues, no spectral theorem. This named
   operator-level theorem did not previously exist in the gallery.
2. `compress_eigenvalues_nonneg` — eigenvalue form, from the Poincaré lower bound
   `0 ≤ lam⟨k+m⟩ ≤ mu k`.
3. `compress_eigenvalue_mem_Icc` — spectral-range containment
   `mu k ∈ [lam⟨n+m-1⟩, lam⟨0⟩]`, chaining both Poincaré bounds with antitonicity.
4. `trace_compress_nonneg` — PSD compression has nonnegative trace.

### Scope honesty

The **weak (Ky Fan) summed majorization** itself is the sibling
`oq-01-oq-02-oq-01` (`CauchyInterlacingKyFan.lean`) and is **not duplicated**
here. The session-1 survey correctly noted the literal ask overlaps existing
gallery content; this entry adds the genuinely-missing named operator-positivity
theorem plus the eigenvalue/range/trace corollaries as a coherent, self-contained
"positivity & spectral range of compressions" file rather than re-proving Ky Fan.

### The genuinely-novel open piece (NOT attempted, recommend standalone)

Full **Schur–Horn theorem** (diagonal of Hermitian ≺ spectrum, with the Birkhoff
converse). Mathlib has `doublyStochastic` + Birkhoff
(`exists_eq_sum_perm_of_mem_doublyStochastic`) but **no majorization predicate and
no Schur–Horn theorem** (only a motivating comment in `InnerProductSpace.Spectrum`).
This is a separate multi-hundred-line problem, not a corollary of interlacing.

### Files
- proofs/Proofs/CauchyInterlacingMajorizationPositivity.lean (NEW, 130 lines, 4 thm)
- src/data/proofs/cauchy-interlacing-theorem-oq-01-oq-02-oq-02/{meta,annotations}.json (NEW)
