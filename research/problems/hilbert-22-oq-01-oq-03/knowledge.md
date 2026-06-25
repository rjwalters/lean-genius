# Knowledge Base: hilbert-22-oq-01-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-06-25 (Session 1) — ORIENT survey

**Mode**: FRESH (fresh EMPTY claim) · **Outcome**: surveyed (phase OBSERVE→ORIENT)

### What I did
- Surveyed local Mathlib for the relevant infrastructure (no compile — build env under heavy concurrent-agent cache churn).
- Produced a feasibility assessment and a tractable↔blocked decomposition; recorded rich knowledge in the problem JSON.

### Key findings
- **Mathlib HAS**: the Schwarz lemma — `Analysis/Complex/Schwarz.lean`, but only the *center-fixing one-point* form (`dist_le_dist_of_mapsTo_ball_self`, `norm_le_norm_of_mapsTo_ball_self`, `norm_deriv_le_one_of_mapsTo_ball`); `PseudoEMetricSpace`/`EMetricSpace` (ENNReal, complete-lattice infima — junk-free); `UpperHalfPlane/Metric.lean` (hyperbolic metric on H); `Analysis/Complex/ValueDistribution/*` (Nevanlinna theory).
- **Mathlib LACKS**: unit-disk Poincaré/pseudohyperbolic metric; Schwarz–Pick (two-point form); Kobayashi pseudometric; Picard little/great theorem; modular λ universal cover 𝔻→ℂ∖{0,1}; Blaschke automorphism library.

### Decomposition
1. **BUILDABLE (<300 ln, pure ENNReal order theory, no analysis)** — abstract chain pseudometric from a symmetric atomic cost `c : X→X→ℝ≥0∞` with `c x x = 0`: `d p q = ⨅ chains, Σ c`; prove refl/symm/triangle (concatenation) ⇒ a `PseudoEMetricSpace`. The abstract Kobayashi skeleton; exactly properties (1)–(2).
2. **BUILDABLE** — `d_ℂ ≡ 0` (ℂ not Kobayashi hyperbolic) via affine maps `z ↦ p+(q−p)z/δ` from the disk realizing arbitrarily small chain cost.
3. **MEDIUM** — two-point Schwarz–Pick contraction on 𝔻 by conjugating Mathlib's center-fixing Schwarz with Blaschke automorphisms `φ_a(z)=(z−a)/(1−āz)`.
4. **BLOCKED (>1000 ln absent foundations)** — Picard's little theorem and `d_𝔻 = ρ`: gated on the modular λ universal cover, absent from Mathlib. Classified BLOCKED per build-vs-block, not premature "Mathlib lacks X".

### Next steps
Build item 1 (standalone, fully tractable, no complex analysis) as the first verified deliverable; then item 2 (`d_ℂ=0`); then item 3; defer item 4.

### Why no Lean this session
Build environment was under sustained concurrent-agent cache churn (≈3000 oleans/min rewritten; Docker down). Each `lake env lean` compile cost ~30 min and frequently crashed on mmap'd-olean races (SIGBUS/SIGSEGV). Attempting a new nontrivial complex-analysis proof under these conditions risked an unverified/overclaimed result; deferred Lean to a calm window.

---

## Session 2026-06-25 (Session 2) — BUILT Item 1 (verified)

**Mode**: continuation of Session-1 decomposition · **Outcome**: Item 1 delivered, machine-verified.

### What I did
- Implemented `proofs/Proofs/Hilbert22OQ01OQ03.lean` (204 lines): the abstract Kobayashi chain pseudometric skeleton (Item 1 of the Session-1 plan), exactly as scoped — pure ℝ≥0∞ order theory + list combinatorics, no complex analysis.
- Verified with `lake env lean Proofs/Hilbert22OQ01OQ03.lean` → EXIT 0 (Docker still down; single-file `lake env lean` against the symlinked prebuilt Mathlib oleans is the safe route and worked despite ~96 concurrent lean procs).
- Confirmed axiom profile with `#print axioms`: only `propext, Classical.choice, Quot.sound` — no `sorryAx`, no `Lean.ofReduceBool`, no `native_decide`. Genuinely `verified` / 0-axiom.
- Authored the gallery entry (`src/data/proofs/hilbert-22-oq-01-oq-03/{meta.json,annotations.json}`).

### Key implementation insights
- **Chain encoding**: represent a chain p⇝q by its *intermediate* vertices `mid : List X`; sum cost from the front via `chainCost c p mid q` (`c p q` for `[]`, `c p x + chainCost c x xs q` for `x::xs`). This avoids `List.head!`/`getLast!` entirely, so **every lemma is free of nonemptiness side-conditions** — the single biggest simplification.
- **Triangle = concatenation** (`chainCost_concat`, 2-case induction), **symmetry = reversal** (`chainCost_reverse`, uses concat with empty tail to peel the last edge), **reflexivity = empty chain**.
- `chainCost` MUST be marked `noncomputable` (ENNReal `+`/CommSemiring has no executable code → IR compile error otherwise). Only fix needed after the first compile.
- The two ENNReal lemmas that close the triangle inequality cleanly: `ENNReal.iInf_add : iInf f + a = ⨅ i, f i + a` and `ENNReal.add_iInf : a + iInf f = ⨅ b, a + f b` (both in `Mathlib/Data/ENNReal/Operations.lean`, namespace `ENNReal`).
- **Functoriality** (`chainDist_mono`): a cost-contracting map is distance-non-increasing — the order-theoretic shadow of the Kobayashi non-expansion theorem; this is the exact interface where Schwarz–Pick would plug in.
- `PseudoEMetricSpace` can be built from just `edist` + the 3 axioms (`toUniformSpace`/`uniformity_edist` have autoParam defaults).

### Status of the decomposition
- Item 1 (abstract pseudometric + functoriality): **DONE, verified.**
- Item 2 (`d_ℂ ≡ 0`): tractable once a concrete disk atomic cost exists; not yet built.
- Item 3 (two-point Schwarz–Pick via Blaschke conjugation): the natural next deliverable — supplies the concrete cost to instantiate `chainPseudoEMetricSpace`.
- Item 4 (Picard, `d_𝔻 = ρ`): still BLOCKED on the modular λ universal cover (absent from Mathlib).

---

## Session 2026-06-25 (Session 3) — BUILT the universal property (verified)

**Mode**: continuation · **Outcome**: coreflection layer delivered, machine-verified.

### What I did
- Extended `Proofs/Hilbert22OQ01OQ03.lean` (204 → 263 lines, 11 → 16 theorems, still
  0 sorry / 0 axiom) with **Part V: the universal property** — `chainDist c` is the
  *greatest pseudometric dominated by* the atomic cost `c` (its pseudometric
  coreflection).
- Verified: `lake env lean Proofs/Hilbert22OQ01OQ03.lean` → EXIT 0; `#print axioms`
  on all four new theorems → only `propext, Classical.choice, Quot.sound`.
- Updated the gallery entry (meta.json sections/counts/contributions, annotations.json).

### Key insight (why this, not Schwarz–Pick, this session)
- Items 2/3 (`d_ℂ ≡ 0`, Schwarz–Pick) both require the **concrete disk Poincaré /
  pseudohyperbolic cost** and Blaschke automorphism machinery, absent from Mathlib
  4.26 and genuine multi-hundred-line complex-analysis builds — high risk under the
  still-degraded build env (Docker down; `lake env lean` only, ~8 concurrent compilers).
- The universal property is **pure ℝ≥0∞ order theory + one list induction**, fully
  in-scope and low-risk, and answers a deeper question: *why* the infimum-over-chains
  definition is canonical. It is forced — `chainDist c` is the unique largest
  pseudometric below `c`.

### Proof technique (all short, robust)
- `chainDist_le_atomic`: `simpa using chainDist_le c p q []` (empty/single-edge chain).
- `le_chainCost_of_triangle` (the engine): induction on `mid`; cons step is a 3-line
  `calc d p q ≤ d p x + d x q ≤ c p x + chainCost c x xs q = chainCost c p (x::xs) q`
  via `htri`, `add_le_add (hdc p x) (ih x)`, `(chainCost_cons …).symm`.
- `le_chainDist_of_triangle`: `le_iInf` over the engine.
- `chainDist_eq_of_triangle`: `le_antisymm chainDist_le_atomic (le_chainDist_of_triangle … (fun _ _ => le_rfl) …)`.
- `chainDist_idem`: instantiate `chainDist_eq_of_triangle` at `chainDist c`, whose
  triangle inequality is `chainDist_triangle`.

### Status update
- Universal property / coreflection (new): **DONE, verified.**
- Items 2/3/4: unchanged — still gated on the disk Poincaré metric / modular cover.
