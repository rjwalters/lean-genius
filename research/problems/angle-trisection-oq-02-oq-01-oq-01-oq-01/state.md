# Current State

**Phase**: S3 ACT — false axiom removed; file now axiom-free (researcher-2, 2026-06-12), Docker build-verified
**Since**: 2026-04-26 (NEW stub) → 2026-06-05 (S1 OBSERVE) → 2026-06-09 (S2 STATE-SYNC) → 2026-06-12 (S3 ACT axiom removal)
**Iteration**: 4

## S3 ACT (2026-06-12, researcher-2) — delete the false axiom `insep_gal_trivial`

**Mode**: ACT (Lean bodies change; Docker build-verified).

**Outcome**: The file `AngleTrisectionOQ02OQ01OQ01OQ01.lean` is now **axiom-free**
(`axiomCount: 1 → 0`, 0 sorries). The mathematically-false axiom `insep_gal_trivial`
("inseparable irreducible ⇒ |Gal| = 1") and its false-axiom-backed consequence
`natDeg_notDvd_gal_of_insep` were **deleted** and replaced by the honest, axiom-free
obstruction:

- `sub_pow_char_pow_eq` — char-`p` Frobenius identity `(a-b)^(p^n) = a^(p^n) - b^(p^n)`.
- `algEquiv_eq_refl_of_isPurelyInseparable` — every F-automorphism of a purely
  inseparable extension is the identity.
- `gal_card_one_of_purelyInseparable_splitting` — purely-inseparable splitting field
  ⇒ |Gal| = 1 (the correct replacement; the descendant's counterexample `X⁴+X²+a`
  over `F₂(a)` shows mere inseparability of `f` does NOT suffice).
- `natDeg_notDvd_gal_of_purelyInseparable_splitting` — the honest non-divisibility.

These three theorems + the helper lemma were **ported** from the OQ-01 descendant
`AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean`, which cannot be imported here (it imports
this file → cyclic). The descendant was rebuilt to confirm no regression.

**Build**: `docker-build.sh Proofs.AngleTrisectionOQ02OQ01OQ01OQ01` clean (7745 jobs);
descendant `…OQ01` also clean (7746 jobs, pre-existing unusedSimpArgs warnings only).

**Gallery**: `meta.json` updated — `status: axiomatized → verified`, `badge: axiom →
verified`, `axiomCount: 1 → 0`, `theoremCount: 5 → 8`, `lineCount: 197 → 237`,
`assumptions` rewritten, stale annotations corrected.

**Lean delta**: +3 theorems +1 lemma; −1 axiom; −1 (false) theorem; 0 sorries.

## S2 STATE-SYNC (2026-06-09, researcher-5) — integrity correction for `insep_gal_trivial`

**Mode**: STATE-SYNC (doc-only; no Lean bodies change).

**Outcome**: Updated the `insep_gal_trivial` axiom docstring, the parent file's Summary
section, and the gallery `meta.json` `assumptions` field to accurately reflect that the
axiom is **mathematically false** as stated. Prior documentation framed it as "true but
unformalized," which is misleading: the OQ-01 descendant proved a counterexample
(X⁴+X²+a over F₂(a): irreducible inseparable, |Gal|=2) and supplied the correct
replacement `gal_card_one_of_purelyInseparable_splitting` (purely-inseparable splitting
field hypothesis, 0 axioms, 0 sorries).

### What landed

- `proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01.lean` — axiom docstring rewritten
  with explicit "MATHEMATICALLY FALSE as stated" warning, pointer to the OQ-01
  counterexample, and the honest correct statement. File Summary table footer updated.
  Added "Integrity Note (S2 STATE-SYNC 2026-06-09)" section. Line count 166 → 197.
- `src/data/proofs/angle-trisection-oq-02-oq-01-oq-01-oq-01/meta.json` — `assumptions`
  field rewritten to flag the falsity, point at the descendant's correct theorem, and
  note that the axiom is retained as a placeholder so `natDeg_notDvd_gal_of_insep`
  type-checks. `lineCount` 166 → 197.
- `state.md` (this file) — phase OBSERVE → STATE-SYNC; iteration 2 → 3.

### Why this matters

The axiomCount field of meta.json was honest (1 axiom declared), but the surrounding
documentation gave the false impression the axiom encoded a true mathematical fact
awaiting formalization. The descendant work (May 2026) made it clear the axiom is
false in general. Without this STATE-SYNC, a reader of the parent entry alone would
walk away believing `insep_gal_trivial` is provable in principle — a credibility hit.

### Lean delta

- 0 new theorems
- 0 sorry deltas
- 0 axiom deltas (axiom retained for downstream type-checking; statement unchanged
  even though now flagged as false)
- 0 Docker build needed (comment-only edits in Lean file)

### Next ACT direction (deferred to a future iteration)

Replace `insep_gal_trivial` with `gal_card_one_of_purelyInseparable_splitting` and
weaken `natDeg_notDvd_gal_of_insep` to take `[IsPurelyInseparable F f.SplittingField]`
as hypothesis. This requires (a) porting the descendant's correct theorem proof
(~30 LOC: `sub_pow_char_pow_eq` + `algEquiv_eq_refl_of_isPurelyInseparable`) into
the parent (the descendant can't import-back without cyclic dependency), or
(b) deleting `natDeg_notDvd_gal_of_insep` from the parent and re-stating it in the
descendant. Either path needs a Docker build; estimate 100-150 LOC churn.

---

## S1 OBSERVE (2026-06-05, researcher-1) — formal statement + decomposition

## S1 OBSERVE (2026-06-05, researcher-1) — formal statement + decomposition

**Mode**: OBSERVE (doc-only; no Lean changes).

**Outcome**: Replaced the auto-generated stub `problem.md` with a fully-fleshed
formal statement, mathematical context (Wantzel over perfect fields +
inseparable counterexample at $p = 2$), S2-S7 decomposition, Mathlib
infrastructure map, and risk notes. The leaf was previously a `NEW`-phase
stub with only the seeker's one-line note "Does the theorem extend beyond
CharZero? Separability is the key hypothesis."

### What landed

- `problem.md` — fully fleshed S1 OBSERVE memo (~300 lines), including:
  - Two flavours of the question (algebraic-tower vs Galois-theoretic).
  - The "perfect-field" specialisation (S2-S3 ACT target).
  - The inseparable counterexample at $K = \mathbb{F}_2(t)$, $\alpha = \sqrt{t}$
    (S5 ACT target).
  - Lean target signatures for `IsConstructibleOver`,
    `wantzel_over_perfect_field`, and `inseparable_counterexample`.
  - S2-S7 decomposition with line-count estimates.
  - Mathlib v4.26.0 infrastructure map with gaps flagged
    (especially: 2-group ⇒ index-2 normal subgroup chain for S4).
- `state.md` (this file) — phase NEW → OBSERVE.

### Mathematical content

The question asks whether Wantzel's classical compass-and-straightedge
constructibility characterisation
($\alpha$ constructible $\iff [\mathbb{Q}(\alpha):\mathbb{Q}]$ is a power of 2,
or equivalently the Galois closure is a 2-group) generalises to base fields
of arbitrary characteristic.

**Resolution sketch (from the textbook literature, Lang VI §1, Stewart §17)**:

- **Perfect base fields**: the characterisation extends unchanged. Proof
  transfers directly: tower-of-quadratics ⇒ $[K(\alpha):K] = 2^n$ is
  multiplicativity of rank in towers (characteristic-free); the converse uses
  Galois closure + 2-group induction, which needs separability (provided by
  perfectness).
- **Inseparable case**: the characterisation **fails**. Counterexample:
  $K = \mathbb{F}_2(t)$, $\alpha = \sqrt{t}$ (a root of $x^2 - t$ in
  $\overline{K}$). Then $[K(\alpha):K] = 2$ (a power of 2) but $\alpha$ does
  not lie in a quadratic Galois extension of $K$ — the extension is purely
  inseparable and has trivial automorphism group.

So the OQ has a known answer: **yes** for perfect fields; **no** for
fields with inseparable algebraic extensions. The novelty here is the
**Lean formalisation**.

### Counts after S1 OBSERVE

| File | Lines | Theorems | Sorries | Axioms |
|------|-------|----------|---------|--------|
| `problem.md` | ~300 | (N/A — markdown) | — | — |
| `state.md` (this file) | ~80 | — | — | — |

No Lean file yet. The S2 ACT target is
`proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01.lean` with the
`IsConstructibleOver` definition + sanity-check boundary cases.

## Active Approach

The S1 OBSERVE memo (in `problem.md`) recommends:

1. **S2 ACT**: define `IsConstructibleOver K α` as "$\alpha$ lies in the top
   of a tower of quadratic extensions of $K$" (avoiding the geometric
   compass-and-straightedge primitive). Sanity-check boundary cases. ~30 LOC.

2. **S3 ACT**: prove the easy direction "constructible $\Rightarrow$ rank is
   $2^n$" — works for any base field (no perfectness needed). Imitates the
   root gallery entry's argument by induction on the tower length. ~40-60 LOC.

3. **S4 ACT**: prove the converse "rank is $2^n$ $\Rightarrow$ constructible"
   under perfectness. The deep step is "2-group $\Rightarrow$ chain of
   normal subgroups of index 2", which gives a Galois-correspondence chain of
   intermediate fields. ~80-120 LOC; the most likely Mathlib-gap candidate.

4. **S5 ACT**: formalise the inseparable counterexample at $K = \mathbb{F}_2(t)$.
   ~50-80 LOC; the `RatFunc + AlgebraicClosure` infrastructure is the
   bottleneck.

5. **S6 ACT (optional)**: derive the classical $\mathbb{Q}$-Wantzel as a
   corollary at $K = \mathbb{Q}$. ~10-20 LOC.

6. **S7**: gallery integration with `status: "formalized"` if S2-S5 ship
   without axioms; `"axiomatized"` if S4 needs an axiom for the 2-group
   chain or S5 hits `RatFunc` infrastructure gaps.

## Blockers

None for S1 OBSERVE (doc-only). For future iterations:

- **`IsConstructibleOver` definition (S2 ACT)**: the choice between
  tower-form and field-degree-form is consequential. S2 ACT memo or PR
  should pin the design choice before writing the skeleton.
- **Mathlib's `PerfectField` API (S4 ACT)**: present but with limited
  downstream support; most Galois-theoretic results are stated as
  `[Algebra.IsSeparable K L]` rather than `[PerfectField K]`. ~20-50 LOC
  of glue may be needed.
- **2-group chain lemma (S4 ACT)**: uncertain whether Mathlib has the
  specific "every 2-group has a normal subgroup of index 2" lemma in a form
  directly usable here. May need a short derivation from `IsPGroup`.
- **`RatFunc + AlgebraicClosure` (S5 ACT)**: rough edges; the inseparable
  counterexample may take longer than the math content would suggest.

## Next Action

**S2 ACT — define `IsConstructibleOver` and ship the Lean skeleton**:

```lean
-- proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01.lean (new)
import Mathlib
import Proofs.AngleTrisection

namespace WantzelGeneralisation

variable {K : Type*} [Field K]

/-- Constructibility over an abstract base field K: α lies in the top of a
    tower of quadratic extensions of K inside its algebraic closure. -/
def IsConstructibleOver (α : AlgebraicClosure K) : Prop :=
  ∃ (n : ℕ) (chain : Fin (n+1) → IntermediateField K (AlgebraicClosure K)),
    chain 0 = ⊥ ∧
    α ∈ chain n ∧
    ∀ i : Fin n, Module.rank (chain i.castSucc) (chain i.succ) = 2

-- + S2 boundary cases (rational elements, base-field elements, etc.)

end WantzelGeneralisation
```

Expected ~30-50 Lean lines, 0 sorries, 0 axioms.

**Alternative S2 ACT (heavier)**: bundle the field-degree-form definition
alongside the tower form, prove their equivalence over perfect fields as
S2 ACT's headline (rather than splitting S3 + S4). This compresses the
decomposition but makes S2 ACT a 100-150 LOC PR.

**Recommended**: ship the lighter tower-form definition + boundary cases as
S2 ACT, defer the field-degree-form equivalence to S3 + S4.

## Honesty

S1 OBSERVE is a **pure survey**. It produces:

- 0 new Lean theorems
- 0 sorry deltas
- 0 axiom deltas
- 1 fully-fleshed `problem.md` (replacing the auto-generated stub)
- 1 `state.md` update (phase NEW → OBSERVE)

The mathematical content (Wantzel over perfect fields + inseparable
counterexample) is **not novel** — it's textbook Galois theory. The S1
contribution is the precise Lean target statements, the S2-S7 decomposition,
and the Mathlib gap analysis. The S2 ACT will be the first Lean iteration
to ship code; the deepest open Lean step is S4 (2-group induction).

The future Lean entry will likely be `status: "axiomatized"` (since the
inseparable counterexample at $\mathbb{F}_2(t)$ may need axiomatised
`RatFunc + AlgebraicClosure` infrastructure), but `"formalized"` is achievable
if S5 stays within current Mathlib capabilities.
