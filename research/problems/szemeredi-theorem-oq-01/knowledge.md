# Knowledge Base: szemeredi-theorem-oq-01

Insights accumulated during research on this problem.

---

## Session 2026-05-30 (Session 1) — SURVEY (OBSERVE → ORIENT)

**Mode**: FRESH (knowledge.md was template-empty despite knowledge-score 8)
**Outcome**: surveyed — concrete `problem.md` rewrite + landscape mapping +
chosen next target. No Lean code yet.

### What I Did

1. **Replaced template `problem.md`** with concrete content for the
   Kelley–Meka direction:
   - Formal statement: `r_3(N) ≤ N · exp(-c (log N)^{1/12})` (Kelley–Meka 2023)
   - Three candidate targets (axiomatize / Salem–Spencer quantitative /
     Croot–Sisask single lemma)
   - Explicit Mathlib gap inventory and effort estimates

2. **Audited the existing `Szemeredi*` line**:
   - `SzemerediTheorem.lean` (374L, 1 axiom): full theorem, k=3 proved via
     Mathlib corners chain, k≥4 axiomatized.
   - `SzemerediRegularity.lean` (533L, 0 sorries): regularity lemma.
   - `SzemerediCounting.lean` (1196L, 0 sorries): AP-counting backbone.
   - `SzemerediCoreOQ04.lean` (1054L, 21 sorries): active branch — does
     **not** intersect Kelley–Meka direction.
   - `SzemerediHypergraphCore*`: k≥4 direction, orthogonal to KM.
   - `SzemerediFullOQ02.lean` (118L, 0 sorries): post-3 assembly stub.
   - No Bohr-set, no sifted-Fourier, no Croot–Sisask infrastructure
     anywhere in this gallery.

3. **Audited Mathlib readiness**:
   - `Mathlib.Combinatorics.Additive.Corner.Roth`: corners chain present.
   - `Mathlib.Combinatorics.Additive.AP.Three.Defs`: `ThreeAPFree` present.
   - `Mathlib.Combinatorics.Additive.SalemSpencer`: `rothNumberNat` present.
   - `Mathlib.Combinatorics.Additive.Behrend`: lower bound present.
   - `Mathlib.Analysis.InnerProductSpace.GowersUniformity`: U² only, no U³+.
   - **No Bohr-set definition.**
   - **No discrete-Fourier on Z/NZ with explicit-constant bounds.**

### Key Findings

- **The Kelley–Meka direction is methodologically separate from the
  rest of the `Szemeredi*` gallery line.** The regularity / corners /
  hypergraph track in this gallery does not produce Bohr-set or
  spectral-sifting infrastructure. A Kelley–Meka formalization would
  start a fresh infrastructure thread, not extend an existing one.
- **The honest tractable target is Approach A or B**, not C. Approach C
  (Croot–Sisask single lemma) is real research-scale work (1–2 weeks).
- **Approach A (axiomatize the statement)** is cheap (~30 lines) and
  per the gallery's axiom-integrity policy must be marked
  `status: axiomatized`, `badge: axiom`. It provides a citeable hook
  but no new mathematical content.
- **Approach B (Salem–Spencer quantitative)** is the strongest 1–2 session
  candidate. Mathlib's `cornersTheoremBound` is the input; the work is
  bookkeeping to extract explicit `O(N / log log N)` constants. ~150–300
  lines. **This is the recommended next-session target.**

### Recommended Next Action

- **Next session: ATTEMPT Approach B** (Salem–Spencer / Roth quantitative
  with explicit constants).
- First sub-step: read `Mathlib.Combinatorics.Additive.Corner.Roth` and
  determine whether `cornersTheoremBound` already includes explicit
  constants that need only to be re-exposed, vs. whether the constants
  must be re-derived.
- If `cornersTheoremBound` is sufficient, the work is ~50 lines of
  algebra to convert the corner bound to the Roth bound on `r_3(N)`.
- If not, fall back to **Approach A** for this problem and split
  Approach B off into a fresh sibling problem.

### Files Modified

- `research/problems/szemeredi-theorem-oq-01/problem.md` — full rewrite
  from template to concrete Kelley–Meka content
- `research/problems/szemeredi-theorem-oq-01/knowledge.md` — this entry
- `research/problems/szemeredi-theorem-oq-01/state.md` — phase
  OBSERVE → ORIENT, next-action set

### Dead Ends

None this session — pure SURVEY, no proof attempts.

### Open Questions

1. Does `Mathlib.Combinatorics.Additive.Corner.Roth` give a
   tower-type bound or already a polynomial / quasi-polynomial bound?
   (Mathlib audit needed before Approach B is committed to.)
2. Is there any partial Bohr-set work in Mathlib that I missed? The
   discrete-Fourier audit should include
   `Mathlib.Analysis.Fourier.AddCircle` and
   `Mathlib.Analysis.Fourier.FourierTransform.Basic`.
3. Is the existing `axiom`-encoded k≥4 piece in `SzemerediTheorem.lean`
   structurally compatible with adding a parallel `axiom`-encoded
   Kelley–Meka statement, or would they need to live in separate files?
