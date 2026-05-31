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

1. ~~Does `Mathlib.Combinatorics.Additive.Corner.Roth` give a
   tower-type bound or already a polynomial / quasi-polynomial bound?~~
   **RESOLVED (Session 2, researcher-1, 2026-05-30)**: tower-type.
   See Session 2 entry below.
2. Is there any partial Bohr-set work in Mathlib that I missed? The
   discrete-Fourier audit should include
   `Mathlib.Analysis.Fourier.AddCircle` and
   `Mathlib.Analysis.Fourier.FourierTransform.Basic`.
3. Is the existing `axiom`-encoded k≥4 piece in `SzemerediTheorem.lean`
   structurally compatible with adding a parallel `axiom`-encoded
   Kelley–Meka statement, or would they need to live in separate files?

---

## Session 2026-05-30 (Session 2) — Mathlib audit (ORIENT → DECISION)

**Mode**: FRESH-on-existing-survey (Session 1 ORIENT survey + this audit)
**Outcome**: Open question 1 resolved (tower-type); committed to Approach A; spin-off recommended for Approach B.

### What I did

Fetched `Mathlib/Combinatorics/Additive/Corner/Roth.lean` at pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0; same pin as the
project's `proofs/lake-manifest.json`). Inspected the definition and
docstring of `cornersTheoremBound`, the constant Mathlib uses to state
its Roth-on-`ℕ` corollary `roth_3ap_theorem_nat`.

### Key finding

`cornersTheoremBound` is **explicitly tower-type** per Mathlib's own
docstring (verbatim):

> *An explicit form for the constant in the corners theorem.*
>
> *Note that this depends on `SzemerediRegularity.bound`, which is a
> tower-type exponential. This means `cornersTheoremBound` is in practice
> absolutely tiny.*

Definition:

```lean
noncomputable def cornersTheoremBound (ε : ℝ) : ℕ :=
  ⌊(triangleRemovalBound (ε / 9) * 27)⁻¹⌋₊ + 1
```

The downstream `roth_3ap_theorem` uses this constant directly:

```lean
theorem roth_3ap_theorem (ε : ℝ) (hε : 0 < ε) (hG : cornersTheoremBound ε ≤ card G)
    (A : Finset G) (hAε : ε * card G ≤ #A) : ¬ ThreeAPFree (A : Set G) := ...
```

This is **density form**, not the **explicit-constant form** Approach
B would need. Inverting the dependence to read off `r_3(N) ≤ N · f(N)`
for some explicit `f` would propagate the tower-type structure
*through* the inversion, yielding `O(N / log* N)`-class bounds at best
— not the `O(N / log log N)` (Kelley-Meka) or `O(N / (log N)^{1+c})`
(Bloom-Sisask) form Approach B targets.

### Decision

**Commit to Approach A** (axiomatize Kelley-Meka, ~30 LOC). Status will
be `axiomatized`, badge `axiom`. This provides a citeable hook for the
gallery's Szemeredi family with honest no-content-added framing per the
project's axiom-integrity policy.

**Approach B**: spin off into sibling `szemeredi-theorem-oq-01-incomplete-01`
as a BLOCKED slug pending upstream Mathlib infrastructure (Bohr-set,
sifted-Fourier, U^3 uniformity). Seeker should extract on the next
curation cycle.

### Recommended next action (researcher next)

Ship Approach A axiomatize in a fresh session:

1. Create `proofs/Proofs/SzemerediTheoremOQ01.lean` (~30 LOC):
   - Standard Mathlib imports
   - `axiom kelley_meka_bound : ∀ N : ℕ, 1 ≤ N → r_3 N ≤ N * Real.exp (-c * (Real.log N)^(1/12))` (or the appropriate Mathlib-compatible form)
   - Comment block referencing Kelley-Meka 2023 and the spin-off sibling slug for Approach B
2. Create gallery entry `src/data/proofs/szemeredi-theorem-oq-01/`:
   - `meta.json`: status `axiomatized`, badge `axiom`, axiomCount 1
   - `annotations.json`, `index.ts` (minimal)
3. Update slug state.md: Phase DECISION-RECORDED → COMPLETED (or → ACT-shipped pending audit).

### Files modified

- `research/problems/szemeredi-theorem-oq-01/sessions/2026-05-30-s2-mathlib-audit-cornersTheoremBound.md` (new)
- `research/problems/szemeredi-theorem-oq-01/knowledge.md` — this entry
- `research/problems/szemeredi-theorem-oq-01/state.md` — Phase / Iteration / Active Approach / Next Action refresh
- `src/data/research/problems/szemeredi-theorem-oq-01.json` — currentState refresh
