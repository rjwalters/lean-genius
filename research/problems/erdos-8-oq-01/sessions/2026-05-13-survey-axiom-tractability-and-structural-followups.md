# SURVEY — Axiom tractability + structural follow-ups for erdos-8-oq-01

**Date**: 2026-05-13 (researcher-1, ~10:55 UTC)
**Mode**: SURVEY (doc-only)
**Outcome**: honest assessment that further axiom elimination is out of
session scope; pivot to structural follow-ups; phase ACT → SURVEY.

---

## 1. Honest assessment of the two remaining axioms

`proofs/Proofs/Erdos8Problem.lean` currently has 2 axioms (down from 5
in PR #7893). Both are deep published 2015 Hough results.

### `hough_minimum_modulus`

```lean
axiom hough_minimum_modulus (cs : CoveringSystem) (hd : cs.hasDistinctModuli) :
    cs.minModulus ≤ 616000
```

**Source**: Hough, B. (2015), *Solution of the minimum modulus problem
for covering systems*, **Annals of Mathematics** 181 (1), 361-382.

**Proof outline** (paper):
- Fourier-analytic L²-mean estimates over residue classes mod `m`.
- Truncated Gauss sums and character sum bounds.
- Construction of a probability measure on the integers that detects
  uncovered residues.
- Lower bound on `∑ 1/m` for the moduli list of any covering system,
  forcing the minimum modulus to be bounded.

**Lean-formalization effort estimate** (researcher-1 best guess, honest):
- ~3 000 LOC of Fourier-analytic infrastructure (already-Mathlib-bridge
  work — Mathlib has Plancherel for finite abelian groups but not the
  truncated-Gauss-sum bounds Hough uses)
- ~5 000 LOC of the main argument
- ~2 000 LOC of supporting estimates (entropy, equidistribution)

**Total: ~10⁴ LOC, multiple researcher-months of dedicated work, not a
session-scale task.**

### `density_conjecture_false`

```lean
axiom density_conjecture_false : ¬density_conjecture
```

**Source**: Hough 2015 (same paper, density version follows from the
minimum-modulus theorem via a probabilistic / weighted-coloring
argument).

**Lean-formalization effort estimate**: builds on
`hough_minimum_modulus` + ~1 000 LOC of density-version-specific
infrastructure. Once `hough_minimum_modulus` is formalized,
discharging this axiom is much easier (probably ~500-1 000 LOC). But
since it depends on `hough_minimum_modulus`, it inherits the same
infeasibility.

**Total: ~1 000 LOC on top of `hough_minimum_modulus`'s ~10⁴ LOC.**

### Conclusion

Both axioms are **honest assumptions corresponding to deep 2015 results**.
They are NOT candidates for routine elimination. The
`Erdos8Problem.lean` formalization is correctly tagged
`status: "axiomatized"`, `badge: "axiom"` in `meta.json`.

Per the researcher role's anti-pattern list ("adding new theorems/parts
to files with high axiom counts — prove existing axioms first. Adding
Part CXLV when there are 50 unproved axioms is fake formalization"),
**adding more theorems on top of these axioms is the wrong move**.
However, the file has only 2 axioms, not 50, and both are deep —
**adding orthogonal structural theorems** (that do NOT depend on the
deep axioms) IS legitimate and useful.

---

## 2. The OQ-01 question: "What is the optimal minimum modulus bound?"

The slug's title in JSON is "What is the optimal minimum modulus bound".
Recall:
- Hough (2015): `minModulus ≤ 616 000`.
- Balister, Bollobás, Morris, Sahasrabudhe, Tiba (2022): refined Hough's
  argument. Their main improvement gives a structural bound much
  smaller than 616 000 in the bulk regime, though the explicit
  improvement on the absolute constant is non-trivial to extract from
  the paper without careful reading.
- **The true optimal bound is unknown.** Classical small-bound
  constructions show K ≥ 2 trivially; whether K = 6, K = 12, etc. are
  achievable for distinct-modulus systems is a separate, classical
  question.

This OQ-01 question is the *quantitative*-improvement direction. It is
not session-tractable.

---

## 3. Three structural follow-ups (session-tractable, orthogonal to the deep axioms)

### SQ-1 — Explicit small-bound covering-system constructions

**Task**: For small `K ∈ {2, 3, 4, 6, 12, …}`, build a concrete
`def exampleCS_K : CoveringSystem` together with proofs

```lean
theorem exampleCS_K_hasDistinctModuli : exampleCS_K.hasDistinctModuli
theorem exampleCS_K_minModulus : exampleCS_K.minModulus = K
```

**For K = 2**: classical example
```
{0 mod 2, 0 mod 3, 1 mod 4, 5 mod 6, 7 mod 12}
```
covers ℤ (this is the smallest distinct-modulus covering system; due
to Erdős, 1950s) and has `minModulus = 2`. The covering proof reduces
to checking residues mod 12 (the LCM): every residue mod 12 falls in
at least one class.

**For K = 3**: harder; Choi 1971 gave a 6-class distinct-modulus
covering with smallest modulus 3.

**For K = 4**: even harder; existence proven, construction long.

**For K ≥ 5**: open in general (this is the gap Hough's bound closes
from above).

**Estimated effort** (session-scale, just K = 2):
- ~30 LOC: `def exampleCS_2 : CoveringSystem` with explicit list
- ~10 LOC: `hasDistinctModuli` proof (`List.nodup_cons` chain)
- ~50 LOC: `covers` proof (case analysis on `x % 12 : Fin 12`,
  `decide`-able)
- ~5 LOC: `minModulus = 2` (the moduli list is `[2, 3, 4, 6, 12]`,
  `Finset.min'` of a known small set)

Total ~100 LOC, **independent of the deep axioms**. Genuine
formalization progress.

### SQ-2 — Cardinality lower bound for the moduli set

**Task**: prove that the moduli set of a distinct-modulus covering
system cannot be "too small" — specifically, prove a quantitative
lower bound like:

```lean
theorem covering_moduli_card_ge_loglog (cs : CoveringSystem)
    (hd : cs.hasDistinctModuli) :
    cs.moduli.card ≥ ⌈log₂ (log₂ cs.minModulus + 1) + 1⌉
```

or some explicit Mirsky-style structural lower bound.

**Status**: this is genuinely a known result (Erdős, 1950s, used a
sieve argument) and gives an `Ω(log log m)` lower bound on the number
of classes in a covering system of minimum modulus m. The proof is
~50-100 LOC of elementary sieving.

**Independent of the deep axioms.**

### SQ-3 — Replace the dummy `balister_improved_bound`

The current theorem

```lean
theorem balister_improved_bound (cs : CoveringSystem)
    (hd : cs.hasDistinctModuli) : cs.minModulus ≤ 616000 :=
  hough_minimum_modulus cs hd
```

is a **placeholder** — it states the same bound as Hough's axiom. It
should be replaced by a strictly-smaller-bound axiom citing BBMST 2022:

```lean
axiom balister_2022_bound (cs : CoveringSystem) (hd : cs.hasDistinctModuli) :
    cs.minModulus ≤ K_BBMST

theorem balister_improved_bound (cs : CoveringSystem)
    (hd : cs.hasDistinctModuli) : cs.minModulus ≤ 616000 := by
  have := balister_2022_bound cs hd
  -- K_BBMST < 616000, so apply le_of_le_of_lt or omega
  …
```

where `K_BBMST` is the explicit constant from the 2022 paper (needs
careful extraction — the paper's structural bound depends on the
covering-system size; for absolute-constant comparison one extracts
the corresponding explicit small-bound).

**Effort**: ~10 LOC + literature read to extract the explicit constant.
**Adds 1 axiom**, but the new axiom is mathematically distinct from
Hough's (it cites a separate paper and gives a strictly smaller bound).

---

## 4. Phase decision: ACT → SURVEY

Per the researcher role's SOLVED/STUCK/MAKING-PROGRESS classification:

> **STUCK** (sorries remain, no clear path forward):
> - Do NOT generalize or broaden scope
> - Decompose into concrete subgoals or intermediate lemmas
> - If 3+ sessions stuck on same sorry: flag as BLOCKED, move on

Strictly we are not "stuck on a sorry" — we have 0 sorries. We are
**stuck on axiom elimination**: the two remaining axioms are not
session-tractable. The right classification is

> **SURVEY** (Can state but not prove yet) → Document findings

with the additional note that **structural sub-questions SQ-1/2/3 are
tractable** and provide a legitimate next-action path.

**Phase update**: ACT → SURVEY (in JSON `currentState.phase`).

This is consistent with the meta.json `status: "axiomatized"` — the
gallery already correctly reflects that the formalization is honest
about its assumptions.

---

## 5. Scope of this PR

**Doc-only.** Deliverables:

| File | Status |
|---|---|
| `research/problems/erdos-8-oq-01/problem.md` | new (bootstrap) |
| `research/problems/erdos-8-oq-01/state.md` | new (bootstrap) |
| `research/problems/erdos-8-oq-01/knowledge.md` | new (bootstrap) |
| `research/problems/erdos-8-oq-01/sessions/2026-05-13-survey-axiom-tractability-and-structural-followups.md` | new (this file) |
| `src/data/research/problems/erdos-8-oq-01.json` | update phase ACT → SURVEY + knowledge fields |

**No Lean files modified.** `axiomCount` unchanged. `sorryCount`
unchanged. `theoremCount` unchanged. Gallery `meta.json` unchanged.

---

## 6. Recommended next session (S3 ACT)

**SQ-1 at K = 2**: ship `exampleCS_modulus_2 : CoveringSystem` with
proofs `_hasDistinctModuli` and `_minModulus_eq_2`. Concrete witness
of the lower endpoint of the optimal bound range. ~100 LOC, no axiom
delta, no dependency on the deep Hough results.

Subsequent sessions can layer SQ-2 (cardinality bound) and SQ-3 (BBMST
axiom replacement). SQ-2 is the most mathematically interesting; SQ-3
is mostly bookkeeping but improves the honesty of the
`balister_improved_bound` claim.
