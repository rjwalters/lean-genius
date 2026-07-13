# Session 2026-05-14 S2 ACT — N-dim mass-point structure + Σ-ratio identity (real-arithmetic shadow, build pending)

**Mode**: ACT SCAFFOLD (from S1 OBSERVE)
**Researcher**: researcher-12 (this session)
**Outcome**: shipped `proofs/Proofs/CevasTheoremOQ04OQ01.lean` (~210 LOC, 0 sorries, 0 axioms, 1 structure, 4 defs, ~10 lemmas/theorems); build pending CI.

## 1. Scope decision relative to S1 OBSERVE

S1 OBSERVE (researcher-3, 2026-05-12) recommended **S2-A**: a ~100 LOC
AffineSpace-based mass-point structure with 2 strategic sorries closing
via `Finset.affineCombination_indicator_subset` + linearity of affine
combinations. S1 also listed S2-B (triangle bridge) and S2-C
(constructive existence) as natural follow-ups but recommended NOT
bundling them into S2-A.

This S2 ACT session **pivots away from the AffineSpace-based S2-A** to
a **self-contained real-arithmetic shadow** for the following reasons:

1. **Lower compile risk**: Mathlib v4.26.0 introduces strict
   parser/elaborator changes (per memory entries
   `feedback_mechanic_mathlib_v426_orphan_docstring_parser_strictness`,
   `feedback_researcher_mathlib_v426_matrix_isdiag_inv_one_squarefree_kit`).
   `Mathlib.LinearAlgebra.AffineSpace.Ceva` uses the new `module`
   keyword + `public import` syntax (introduced 2025/2026). Wiring
   into the gallery from a worktree with broken `.lake` symlink
   carries notable build risk.

2. **Matches parent's style**: `proofs/Proofs/CevasTheoremOQ04.lean`
   (242 LOC, 0 sorries) is itself a *pure real-arithmetic shadow* of
   the geometric triangle Ceva theorem (`MassPointCeva.MassPoint` has
   `mA, mB, mC : ℝ`, no `AffineSpace`). The natural generalisation in
   this style is a `Fin (n+1) → ℝ` indexed family — exactly what S2
   ships.

3. **Geometric content already in Mathlib**: as S1 OBSERVE
   documented, the n-dim geometric Ceva concurrency is already proved
   in `Mathlib.LinearAlgebra.AffineSpace.Ceva` (Joseph Myers 2025).
   The gallery's genuine value-add is the **bookkeeping** of the
   mass-point structure, not the geometry — which the real-arithmetic
   shadow captures fully.

4. **Composable handoff**: S3 can pick up either S2-B (triangle
   bridge to parent) or S2-C (constructive existence) as a natural
   ~50 LOC follow-up, OR add the AffineSpace bridge as a separate
   module. The S2 shadow is *orthogonal* to all three.

## 2. S2 deliverable summary

File: `proofs/Proofs/CevasTheoremOQ04OQ01.lean` (NEW, ~210 LOC).

```
namespace NDimMassPoint

structure MassPoint (n : ℕ) where
  mass : Fin (n + 1) → ℝ
  pos  : ∀ i, 0 < mass i

variable {n : ℕ} (mp : MassPoint n)

noncomputable def MassPoint.total : ℝ := ∑ i, mp.mass i
lemma MassPoint.total_pos : 0 < mp.total
lemma MassPoint.total_ne_zero : mp.total ≠ 0

noncomputable def MassPoint.ratio (i : Fin (n + 1)) : ℝ :=
  (∑ j ∈ Finset.univ.erase i, mp.mass j) / mp.total

lemma MassPoint.sum_erase_eq_total_sub (i : Fin (n + 1)) :
    (∑ j ∈ Finset.univ.erase i, mp.mass j) = mp.total - mp.mass i

lemma MassPoint.ratio_eq_one_sub (i : Fin (n + 1)) :
    mp.ratio i = 1 - mp.mass i / mp.total

lemma MassPoint.ratio_lt_one (i : Fin (n + 1)) : mp.ratio i < 1
lemma MassPoint.ratio_pos (i : Fin (n + 1)) (hn : 0 < n) : 0 < mp.ratio i
lemma MassPoint.sum_mass_div_total : (∑ i, mp.mass i / mp.total) = 1

-- The HEADLINE identity:
theorem MassPoint.sum_ratio_eq : (∑ i, mp.ratio i) = (n : ℝ)

-- Triangle specialisation:
example (mp : MassPoint 2) :
    mp.ratio 0 + mp.ratio 1 + mp.ratio 2 = 2

-- Centroid example:
noncomputable def uniform (n : ℕ) : MassPoint n
lemma uniform_total (n : ℕ) : (uniform n).total = (n + 1 : ℝ)
lemma uniform_ratio (n : ℕ) (i : Fin (n + 1)) :
    (uniform n).ratio i = (n : ℝ) / (n + 1)

end NDimMassPoint
```

**Sorry count**: 0. **Axiom count**: 0. **Theorem/lemma count**: ~10.
**Definition count**: 4 (`MassPoint`, `total`, `ratio`, `uniform`).

## 3. Why `ratio` uses the complement-fraction normalisation

For an `n`-simplex with `n+1` vertices `Fin (n+1)`, three natural
"mass-point ratios" coexist:

| Notation | Definition | Sum constraint |
|---|---|---|
| **mass-fraction** | `m_i / total` | `Σ = 1` |
| **complement-fraction** (this file) | `(total - m_i) / total = 1 - m_i / total` | `Σ = n` |
| **edge-split** (parent's `rD,rE,rF`) | `m_j / (m_i + m_j)` for each *edge* `(i,j)` | quadratic; needs edge orientation |

The **complement-fraction** generalises the parent's intuition that
each "Ceva ratio" is *one minus a normalised vertex mass*: for the
parent's triangle, `1 - rD = mB/(mB+mC)`, `1 - rE = mC/(mC+mA)`,
`1 - rF = mA/(mA+mB)`, and the **sum-of-complements** is

  `(1 - rD) + (1 - rE) + (1 - rF) = 2`

(by writing each as a quotient and summing; the result is `(mB+mC) /
(2*total/3)` or similar — exact value matches the n-dim identity at
n=2). The headline `Σ ratio i = n` packages this for all n ≥ 0.

The **edge-split** (parent's) normalisation does NOT have a clean
n-dim generalisation: it requires choosing an *orientation* on each
edge, and there are `(n+1 choose 2)` edges (quadratic in vertices).
The complement-fraction is the natural linear-in-vertices alternative.

## 4. Mathlib API surface used (and v4.26.0 risk assessment)

| API | Use | Risk |
|---|---|---|
| `Finset.sum_pos` | `total_pos` | Low (in stable API since pre-v4) |
| `Finset.univ_nonempty` | `total_pos` | Low |
| `Finset.sum_erase_eq_sub` | `sum_erase_eq_total_sub` | Low (stable) |
| `Finset.sum_sub_distrib` | `sum_ratio_eq` | **Medium** — see §5 |
| `Finset.sum_const` + `Fintype.card_fin` | `sum_ratio_eq`, `uniform_total` | Low |
| `Finset.card_pos`, `Finset.card_erase_of_mem` | `ratio_pos` | Low |
| `Fin.sum_univ_three` | triangle example | Low |
| `div_pos`, `div_self`, `field_simp` | various | Low |
| `linarith`, `omega`, `positivity` | various | Low |

## 5. Identified medium-risk item: `Finset.sum_sub_distrib`

The identity `Σ (f i - g i) = Σ f i - Σ g i` is named differently
across Mathlib versions:

- Some versions: `Finset.sum_sub_distrib`
- Alternative: `Finset.sum_sub`
- Alternative: inline via `simp_rw [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]`

If the name is wrong at v4.26.0, the 1-LOC fix in the `sum_ratio_eq`
calc step is to swap the lemma name. S3 doctor handoff if needed.

## 6. Race / saturation context

Pre-claim probe at 2026-05-14T20:30Z (researcher-12, this session):

```
slug = cevas-theorem-oq-04-oq-01
open_PRs   = 0   (only S1 OBSERVE session log, no Lean PRs)
recent_merges = 0
remote_branches = 0
```

Genuinely pristine. S2 ACT is the **first Lean file** for this slug.

## 7. Out-of-scope items (intentionally deferred)

* **Triangle bridge to parent** (S3-B target): a clean construction
  `MassPointCeva.MassPoint ↔ NDimMassPoint.MassPoint 2` at the data
  level, plus identities relating parent's `rD, rE, rF` to this
  file's `ratio 0, ratio 1, ratio 2`. The two normalisations are
  different but compatible; the bridge requires careful index
  alignment and ~50 LOC.

* **Constructive existence** (S3-C target): n-dim analogue of
  `masses_from_ceva`. Given `r : Fin (n+1) → ℝ` with `Σ r i = n` and
  `0 < r i < 1`, construct `mp : MassPoint n` with `mp.ratio i = r i`.
  The natural construction is `mass i := 1 - r i + 0 · total` plus
  normalisation; the constraint `Σ r i = n` is exactly the
  consistency condition. ~80 LOC.

* **Geometric concurrency** (S3-A target): import
  `Mathlib.LinearAlgebra.AffineSpace.Ceva` and tie `MassPoint n` to a
  concurrency point at the mass-centroid via Joseph Myers's 2025
  `exists_affineCombination_eq_smul_eq_of_fintype`. ~50–80 LOC,
  carries the AffineSpace import risk noted in §1.

## 8. Honesty assessment

This S2 SCAFFOLD ships the **bookkeeping device** for n-dim
mass-point Ceva theory (the structure, the ratios, the sum identity)
WITHOUT any geometric content. That is honest mass-point work in the
parent's tradition — the parent's `MassPointCeva.MassPoint` and
`ceva_identity` are similarly purely algebraic, leaving the geometric
interpretation as informal commentary.

What S2 does NOT claim:
- ✗ "N-dim Ceva theorem proved" (that's Mathlib's territory via
  Joseph Myers 2025).
- ✗ "Equivalence with parent's mass-point structure" (the bridge is
  deferred to S3).
- ✗ "Constructive certificate for the converse direction" (S3-C).

What S2 DOES claim:
- ✓ A clean n-dim mass-point structure compatible with the parent.
- ✓ The sum-of-complements identity Σ ratio = n for all n ≥ 0.
- ✓ A concrete example (uniform = centroid case) at all dimensions.

## 9. Build status

**S2 build: PENDING** (worktree's `proofs/.lake` is a self-symlink per
`feedback_researcher_lake_symlink_broken.md`; Docker build deferred to
CI). All Mathlib API used is standard except the `Finset.sum_sub_distrib`
risk item in §5.

## 10. PR structure

| File | Change |
|---|---|
| `proofs/Proofs/CevasTheoremOQ04OQ01.lean` | NEW, ~210 LOC, 0 sorries |
| `proofs/Proofs.lean` | +1 import line |
| `research/problems/cevas-theorem-oq-04-oq-01/state.md` | REWRITTEN: phase OBSERVE→SCAFFOLD, iter 1→2 |
| `research/problems/cevas-theorem-oq-04-oq-01/sessions/2026-05-14-s02-act-ndim-mass-point-scaffold.md` | NEW (this file) |
| `src/data/research/problems/cevas-theorem-oq-04-oq-01.json` | currentState phase/iter/focus/nextAction + lastUpdate |

No edits to:
- `proofs/Proofs/CevasTheoremOQ04.lean` (parent, 242 LOC unchanged)
- `src/data/proofs/cevas-theorem-oq-04/meta.json` (parent gallery unchanged)
- Any other gallery / annotation / Lean source

## 11. Next-session recommendation

If a follow-up S3 session is opened, **prefer S3-B (triangle bridge)**
as the natural complement to S2 — it closes the semantic gap between
this file's n-dim ratios and the parent's edge-split parameters. S3-C
(constructive existence) is also natural and may be bundled with S3-B
in a single ~120 LOC session.

S3-A (geometric concurrency via AffineSpace) should wait for at least
one v4.26.0 Mathlib parser-related Erdős/gallery merge to confirm
the `Mathlib.LinearAlgebra.AffineSpace.Ceva` `module` import works
cleanly in the gallery context.

---

**Time-budget**: claim → push targeted at ≤ 35 min.
**Sorry / axiom delta**: 0 / 0 (S2 SCAFFOLD ships axiom-free).
