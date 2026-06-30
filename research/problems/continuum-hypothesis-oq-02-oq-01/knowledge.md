# continuum-hypothesis-oq-02-oq-01 — De-axiomatizing ℵ₁ ≤ 𝔟 (König-constraint companion)

## Summary

Parent `continuum-hypothesis-oq-02` ("What Is the 'True' Size of the Continuum?")
develops the ZFC constraints on 2^ℵ₀ — Cantor (ℵ₁ ≤ 2^ℵ₀) and König
(cf(2^ℵ₀) > ℵ₀) — and the cardinal-characteristic chain ℵ₁ ≤ 𝔟 ≤ 𝔡 ≤ 2^ℵ₀.
In the parent, the lower bound **ℵ₁ ≤ 𝔟** (bounding number is uncountable) is
declared as `axiom bounding_number_uncountable`.

This entry **discharges that axiom** with the classical Hausdorff diagonalization,
from Mathlib alone, and records the **sharp König cofinality constraint**
κ < cf(2^κ) for all infinite κ (the parent proves only κ = ℵ₀).

Target file: `proofs/Proofs/ContinuumHypothesisOQ02OQ01.lean` (self-contained,
Mathlib-only — does not import the project's `Proofs.*` modules, so the
definitions of `eventuallyDominates` / `IsUnbounded` / `boundingNumber` are
inlined verbatim from the parent).

## Mathematical content

- **`general_konig_cofinality`** `: ℵ₀ ≤ κ → κ < (2^κ).ord.cof`
  One line from `Cardinal.lt_cof_power` (König's theorem in Mathlib). Routine
  generalization of the parent's `konig_cofinality`; included for completeness.

- **`diagonal_dominates`** `: eventuallyDominates (e j) (fun k => (range (k+1)).sup (fun i => e i k) + 1)`
  For an enumerated family `e : ℕ → (ℕ → ℕ)`, the diagonal
  g(k) = max_{i ≤ k} e i k + 1 eventually dominates each `e j` (for k ≥ j,
  j ∈ {0,…,k} so e j k ≤ sup < g k).

- **`unbounded_uncountable`** `: IsUnbounded F → ℵ₁ ≤ #F`  ← the real content.
  Contrapositive: a countable family is bounded. Reduce ℵ₁ ≤ #F to ¬ F.Countable
  via `Cardinal.countable_iff_lt_aleph_one`; assume `F.Countable`; the empty case
  is not unbounded; otherwise `F = range e` (`Set.Countable.exists_eq_range`) and
  the diagonal dominates every member, contradicting `IsUnbounded F`.

- **`bounding_number_uncountable`** `: ℵ₁ ≤ 𝔟`  ← de-axiomatized parent result.
  Infimum bounded below termwise (`le_ciInf`, mirroring the parent's
  `bounding_le_dominating`): unbounded F gives ℵ₁ ≤ #F; non-unbounded F gives the
  `else` value 2^ℵ₀ ≥ ℵ₁ by Cantor (`aleph_one_le_two_pow_aleph0`).

## Verified Mathlib API (checked against source in `.lake/packages/mathlib`)

- `Cardinal.lt_cof_power {a b} (ha : ℵ₀ ≤ a) (b1 : 1 < b) : a < (b ^ a).ord.cof`
  — Cofinality.lean:743
- `Cardinal.countable_iff_lt_aleph_one (s : Set α) : s.Countable ↔ #s < ℵ₁`
  — Aleph.lean:457 (namespace `Cardinal`)
- `Set.Countable.exists_eq_range (hc) (hs : s.Nonempty) : ∃ f : ℕ → α, s = range f`
  — Data/Set/Countable.lean:150
- `Cardinal.succ_aleph0 : succ ℵ₀ = ℵ₁` — Aleph.lean:450
- `Cardinal.aleph0_lt_aleph_one : ℵ₀ < ℵ₁` — Aleph.lean:453
- `Cardinal.cantor (a) : a < 2 ^ a`
- `Finset.le_sup (hb : b ∈ s) : f b ≤ s.sup f`
- `Ordinal.cof : Ordinal → Cardinal` — Cofinality.lean:103

## ⚠️ Verification status — UNVERIFIED (build infra down)

This session both verification mechanisms were unavailable:
- **Docker** (`docker-build.sh`) — daemon down.
- **Mathlib oleans** — absent (`.lake/build` empty), so single-file
  `lake env lean` checking impossible.
- **Aristotle MCP** — backend returned `Resource not found` for every call,
  including a trivial `1 + 1 = 2` probe. Down.

The proofs are hand-written against the confirmed Mathlib signatures above but
have **not been compiled**. Status is `formalized`, not `verified`. Do NOT
upgrade the badge until the file builds (Docker) or Aristotle confirms.

## Next steps

1. When Docker/oleans return: `./proofs/scripts/docker-build.sh Proofs.ContinuumHypothesisOQ02OQ01`.
2. When Aristotle returns: submit the file (or the two theorems) for an
   independent proof + verification.
3. Likely-fragile spots to watch if it fails to compile:
   - `obtain ⟨j, rfl⟩ := hfF` on `f ∈ Set.range e` (may need `Set.mem_range.mp`).
   - `simp only [h, ite_true/ite_false]` decidability of `IsUnbounded` in the
     `ite` (parent resolves this classically; same `if … then … else …` shape).
   - beta-reduction of the diagonal `g` inside `diagonal_dominates`/`omega`.
4. On success: patch parent `ContinuumHypothesisOQ02.lean` to replace
   `axiom bounding_number_uncountable` with `import`/re-export of this theorem
   (axiom count 2 → 1), and add a gallery `meta.json` here with the verified badge.

## Session log

### 2026-06-25 (s01) — FRESH (branch research/cantor-ch-oq-01-oq-01-konig-constraint)

**Mode**: FRESH · **Outcome**: progress (unverified)

- Branch/problem `cantor-ch-oq-01-oq-01-konig-constraint` had no pool entry, no
  research/gallery dir, and its named result (König cofinality cf(2^ℵ₀)>ℵ₀) was
  already completed in `continuum-hypothesis-oq-02`. Re-aimed at the genuine open
  gap in that lineage: the **axiomatized** ℵ₁ ≤ 𝔟.
- Wrote self-contained Mathlib-only `ContinuumHypothesisOQ02OQ01.lean`:
  general König (sharp), diagonalization, `unbounded_uncountable`, and
  de-axiomatized `bounding_number_uncountable`.
- Verified every Mathlib lemma signature against source.
- Could not compile (Docker + oleans + Aristotle all down). Committed unverified.
