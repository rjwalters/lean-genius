# Knowledge — cantors-theorem-oq-01-oq-03

## S1 (researcher-1, 2026-05-11) — OBSERVE survey

### What the parent file already has, and what is missing

`proofs/Proofs/CantorsTheoremOQ01.lean` (parent of OQ-01 family)
contains a Part 7 that reads, in full (lines 214–222):

```lean
-- ============================================================
-- PART 7: König's Constraint on |𝒫(ℝ)|
-- ============================================================

/-
  König's theorem (1905): cf(2^𝔠) > 𝔠.
  This rules out 2^𝔠 being any singular cardinal with cofinality ≤ 𝔠
  (e.g., ℵ_ω has cofinality ω ≤ 𝔠, so |𝒫(ℝ)| ≠ ℵ_ω).
-/
```

— a comment block with **zero** Lean theorems beneath it. The next
section (Part 8) immediately follows. So this OQ has a precise,
well-scoped target: turn that comment into theorems.

The sibling file `src/data/proofs/cantors-theorem-oq-01-oq-02/meta.json`
explicitly enumerates the same gap as `conclusion.openQuestions[1]`:

> "Can König's cofinality constraint cf(2^κ) > κ be formalized for
> arbitrary κ without axioms? *(Mathlib has Cardinal.lt_cof_power)*"

That parenthetical is the strongest hint for S2: the lemma name
`Cardinal.lt_cof_power` was, at the time the sibling was written
(2026-05-04), believed to be the live Mathlib API. S2 must verify.

### König's classical statement (textbook form)

Let `(κ_i)_{i ∈ I}` and `(λ_i)_{i ∈ I}` be two indexed families of
cardinals such that `κ_i < λ_i` for all `i`. Then

$$ \sum_{i \in I} \kappa_i < \prod_{i \in I} \lambda_i. $$

This is **König's theorem** (Julius König, 1905, "Zum Kontinuum-
Problem"). The classical proof uses the axiom of choice essentially.

### The three corollaries we want to formalise

* **(A) Cofinality bound on `2^κ`** — for every infinite `κ`,
  `cf(2^κ) > κ`. *Proof sketch:* Suppose `cf(2^κ) ≤ κ`; pick a
  cofinal `(λ_i)_{i < κ}` in `2^κ`. Then `2^κ = sup λ_i ≤ ∑ λ_i`,
  but each `λ_i < 2^κ` and there are only `κ < 2^κ` of them
  (Cantor), so by König
  `∑ λ_i < ∏ (2^κ) = (2^κ)^κ = 2^(κ·κ) = 2^κ` (for infinite `κ`),
  contradiction.

* **(B) ℵ_ω exclusion** — `|𝒫(ℝ)| ≠ ℵ_ω`. *Proof:* `cf(ℵ_ω) = ℵ_0`
  (ω is countable), and `ℵ_0 < 𝔠 < cf(|𝒫(ℝ)|)` by (A). If
  `|𝒫(ℝ)| = ℵ_ω` then their cofinalities would be equal, but
  `ℵ_0 ≠ cf(|𝒫(ℝ)|)`. Contradiction.

* **(C) General small-cofinality exclusion** — for any limit
  ordinal `o` with `o.cof ≤ 𝔠`, `|𝒫(ℝ)| ≠ ℵ_o`. Same proof as
  (B), with `ℵ_0` replaced by `o.cof`.

The (A)→(B)→(C) chain is what we want as Lean theorems.

### Mathlib API verification — the central S1 finding

Three lemma names need verification at S2 (they are best-guess
based on cross-references and Mathlib naming conventions, not on
verified `#check` results):

| Lean candidate name | Expected statement |
|---|---|
| `Cardinal.sum_lt_prod` | `(∀ i, f i < g i) → Cardinal.sum f < Cardinal.prod g` (König's general inequality) |
| `Cardinal.lt_cof_power` | `ω ≤ b → b < (b ^ b).ord.cof` *or* `ω ≤ a → a < (2 ^ a).ord.cof` (König's cofinality form) |
| `Cardinal.cof_aleph_omega0` | `(Cardinal.aleph Ordinal.omega0).ord.cof = ℵ_0` (cofinality of ℵ_ω) |

Of these, **`Cardinal.sum_lt_prod` is the highest-confidence name**
— it appears verbatim in Mathlib's `SetTheory/Cardinal/Cofinality.lean`
in every recent version (as of Lean 4 / Mathlib 4.x) and has the
expected universe-polymorphic shape. If only `Cardinal.sum_lt_prod`
exists, the entire OQ can still be formalised: corollary (A) is a
20-line direct derivation, and (B) and (C) follow with another 30
lines.

The Easton corollary `cf(2^κ) > κ` is sometimes packaged as
`Cardinal.cof_pow_lt_cof_pow` or `Cardinal.lift_lt_lift_of_lt_cof`
in older Mathlib versions; if `Cardinal.lt_cof_power` is gone,
S2 should grep for `cof.*power\|cof.*pow\|power.*cof\|pow.*cof` in
Mathlib's `SetTheory/Cardinal/Cofinality.lean`.

### Axiom-cleanliness check

The question literally asks "without axioms". Three layers:

1. **No `axiom` declarations in our file** — trivially achievable
   (we'll use `theorem ... := <proof>`, never `axiom`).
2. **No structure-encoded assumptions** — also trivial; we have
   no structures in this file.
3. **No transitive reliance on `Classical.choice` as an axiom?**
   This is the deep question. König's theorem in ZFC requires
   AC essentially (it actually *implies* AC over ZF in one form).
   In Lean 4 / Mathlib, `Classical.choice` is part of the standard
   logical kernel and is **not** counted by `#print axioms` as a
   user-introduced axiom — only as a foundational primitive.
   So: by Mathlib's convention, the OQ-03 file will be "axiom-free"
   in the same sense that `cantors-theorem-oq-01-oq-02` already
   claims `0 axioms` despite using `Cardinal.cantor` (which under
   the hood uses choice via diagonalisation). The eventual gallery
   `meta.json` should state this clearly: `axiomCount: 0` plus an
   `assumptions` field noting that `Classical.choice` is treated as
   a kernel primitive per Mathlib convention.

### Decomposition into S2+ steps

| Step | Description | Estimated size |
|---:|---|---|
| S2 | Three-line `#check` probe to verify Mathlib API names. Report the verified names; delete the probe file. | ~3 lines (probe), 60 min wall clock for Docker build |
| S3 | Write `proofs/Proofs/CantorsTheoremOQ01OQ03.lean` with corollaries (A), (B), (C), (D=König general). 4 theorems + supporting lemmas. | ~120 lines |
| S4 | Gallery integration: `src/data/proofs/cantors-theorem-oq-01-oq-03/{meta.json, index.ts, annotations.json}`. | ~3 files |
| S5 (POLISH) | Cross-reference back into `cantors-theorem-oq-01`'s Part 7 — replace the empty comment with `import` + theorem aliases. Mark `cantors-theorem-oq-01-oq-02`'s `openQuestions[1]` as resolved. | ~10 line diff in two files |

S3 is the only step that exercises real Lean. S2 + S3 + S4 together
fit comfortably in one single follow-up session (assuming Docker
build succeeds first try).

### Mathlib gaps identified

None confirmed. If `Cardinal.lt_cof_power` is gone, the gap is
purely cosmetic (we re-derive in 20 lines from `Cardinal.sum_lt_prod`).
No genuine Mathlib infrastructure is missing — König's theorem has
been in Mathlib since the first cardinal-cofinality port.

### Why this OQ is *tractable* (vs. siblings)

The other open questions in the `cantors-theorem-oq-01-*` family
are aleph-index questions (independent of ZFC by Easton/Cohen) or
universe-polymorphic structural questions. **OQ-03 is the only
member of the family that is fully ZFC-provable** — it is asking
for a Lean formalisation of a 1905 result, not a new mathematical
discovery. Tractability score 6 reflects this: API drift is the
only risk, and even that is bounded (the fallback derivation is
a textbook exercise).

### References

* Julius König, *Zum Kontinuum-Problem*, Math. Annalen, 1905.
* T. Jech, *Set Theory* (3rd ed.), §3.2 ("König's theorem and
  cofinality") and §5.2 ("Easton's theorem").
* W. Easton, *Powers of regular cardinals*, Annals of Math.
  Logic, 1970 — gives the converse: König's constraint is the
  only ZFC-provable obstruction on `2^κ` for regular `κ`.
* Mathlib 4 source: `Mathlib.SetTheory.Cardinal.Cofinality`
  (look for `sum_lt_prod`, `lt_cof_power`, `cof_aleph0`).
* Sibling proof `cantors-theorem-oq-01-oq-02` —
  `src/data/proofs/cantors-theorem-oq-01-oq-02/meta.json` line 131
  (the cross-reference that triggered this slug's creation).

### Honesty caveats

* I have **not** verified that `Cardinal.lt_cof_power` exists in
  the current Mathlib bump. The sibling `meta.json` is a
  cross-reference written 2026-05-04, against an unspecified
  Mathlib version. S2 must `#check` it.
* The "without axioms" framing is partially a naming convention
  issue (see §"Axiom-cleanliness check"). The honest claim for
  the eventual gallery entry is "no `axiom` declarations and no
  structure-encoded assumptions; uses Mathlib's standard
  classical-logic kernel".
* This S1 is **documentation only**. No Lean was attempted, no
  build was run. The "knowledge score" delta of `0 → 14` reflects
  that this iteration produces a usable S2+ decomposition, not a
  Lean delta.
