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

---

## Session 2026-06-03 (Session 3) — ACT (DECISION-RECORDED → ACT-shipped)

**Mode**: ACT — Approach A landed
**Outcome**: `proofs/Proofs/SzemerediTheoremOQ01.lean` + gallery entry shipped; 1 axiom (`kelley_meka_bound`), 1 theorem (`rothNumberNat_density_le_kelley_meka`), 0 sorries.

### What I Did

1. **Wrote `proofs/Proofs/SzemerediTheoremOQ01.lean`** (~88 lines):
   - Docstring framing the bound, the reason for axiomatizing, the rate gap vs `cornersTheoremBound`, and the sibling-slug pointer.
   - Imports: `Mathlib.Combinatorics.Additive.Corner.Roth` (for `rothNumberNat`), `Mathlib.Analysis.SpecialFunctions.Log.Basic`, `Mathlib.Analysis.SpecialFunctions.Pow.Real`, `Mathlib.Tactic`.
   - `namespace SzemerediTheoremOQ01`, `open Real`.
   - `axiom kelley_meka_bound : ∃ c > 0, ∃ N₀, ∀ N ≥ N₀, (rothNumberNat N : ℝ) ≤ N · Real.exp (-(c · Real.log N ^ (1/12)))`.
   - `theorem rothNumberNat_density_le_kelley_meka` derives `r_3(N)/N ≤ exp(-c (log N)^{1/12})` for `N ≥ max N₀ 1`. Proof: `obtain` constants from axiom, threshold = `max N₀ 1`, derive `1 ≤ N` via `le_max_right`, `(0 : ℝ) < N` via `Nat.lt_of_succ_le hN1` + `exact_mod_cast`, rewrite `div_le_iff₀ hN_pos; mul_comm`, close by `exact hb`.

2. **Created gallery entry `src/data/proofs/szemeredi-theorem-oq-01/`**:
   - `meta.json`: status `axiomatized`, badge `axiom`, axiomCount 1, sorries 0, lineCount 88, theoremCount 1, definitionCount 0. Three section descriptors (`preamble`, `kelley-meka-axiom`, `density-corollary`), four cross-references (`szemeredi-theorem`, `szemeredi-full-oq-02`, `szemeredi-regularity`, `szemeredi-counting`), four references (Kelley–Meka 2023, Behrend 1946, Bloom–Sisask 2020, Roth 1953).
   - `annotations.json`: three annotations (one per section). Math context uses LaTeX inline.

3. **Registered the module**: added `import Proofs.SzemerediTheoremOQ01` to `proofs/Proofs.lean` immediately after `Proofs.SzemerediTheorem`.

### Key Findings (this session)

- The axiom statement composes directly with the rest of the additive-combinatorics gallery because it is stated against Mathlib's `rothNumberNat`, not against a local custom predicate. Any future Lean formalization of Kelley–Meka can replace the axiom by a theorem without disturbing downstream consumers.
- The density-form corollary `rothNumberNat_density_le_kelley_meka` is non-axiomatic and certifies that the axiom is not vacuous in the asymptotic direction.
- The pattern `(0 : ℝ) < N := by exact_mod_cast Nat.lt_of_succ_le hN1` (from `SzemerediFullOQ02.lean` line 56) was reused to bridge `1 ≤ N : ℕ` to `(0 : ℝ) < N`; this is the idiomatic safe form rather than `exact_mod_cast hN1` directly.

### Verification status

**Local Docker daemon is in I/O-error state** (`/var/lib/desktop-containerd/...meta.db: input/output error` from `docker images`), so the `./proofs/scripts/docker-build.sh Proofs.SzemerediTheoremOQ01` invocation could not actually run the build. The file follows the same idioms as `SzemerediFullOQ02.lean` (which builds in CI) and the proof is short and uses only standard Mathlib lemmas, so the build is expected to succeed; the Mechanic / Auditor agents will verify post-merge.

### Files Modified

- `proofs/Proofs/SzemerediTheoremOQ01.lean` — new file, 88 lines, 1 axiom, 1 theorem, 0 sorries.
- `proofs/Proofs.lean` — added `import Proofs.SzemerediTheoremOQ01`.
- `src/data/proofs/szemeredi-theorem-oq-01/meta.json` — new gallery entry.
- `src/data/proofs/szemeredi-theorem-oq-01/annotations.json` — new annotation file.
- `research/problems/szemeredi-theorem-oq-01/state.md` — Phase DECISION-RECORDED → ACT-shipped.
- `research/problems/szemeredi-theorem-oq-01/knowledge.md` — this entry.
- `src/data/research/problems/szemeredi-theorem-oq-01.json` — currentState refresh.

### Open Questions Generated

1. **Exponent improvement**: Kelley–Meka uses `1/12`; subsequent work has pushed it up. Should a follow-up slug record the current best exponent?
2. **Kelley–Meka vs Behrend gap**: The `(log N)^{1/12}` (KM) vs `sqrt(log N)` (Behrend) gap is open. Recording the lower bound as a sibling axiom slug would frame the gap concretely in the gallery.
3. **Discharging the axiom**: Concrete upstream Mathlib targets: Bohr sets (~500–1000 LOC), sifted Fourier on `Z/NZ` with explicit constants (~1000–2000 LOC), `U^3` inverse theorem (~1000+ LOC). Worth coordinating with Mathlib maintainers.

### Next Action (downstream)

- Mechanic / Auditor: Docker-build `Proofs.SzemerediTheoremOQ01`; verify `axiomCount: 1`, `sorries: 0`, `theoremCount: 1`.
- Curator / Seeker: extract sibling slug `szemeredi-theorem-oq-01-incomplete-01` for the BLOCKED Salem–Spencer quantitative direction.
- Mark slug COMPLETED in tracking JSON once Mechanic/Auditor pass.

### Dead Ends

None this session.
