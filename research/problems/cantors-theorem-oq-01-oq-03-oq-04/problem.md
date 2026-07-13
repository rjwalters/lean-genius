# Problem: General cofinality exclusion `cf(|𝒫(ℝ)|) ≠ κ` for `κ ≤ 𝔠`

## Statement

### Plain Language

The parent file `CantorsTheoremOQ01OQ03.lean` proved the canonical
corollary

> `cf_powerSet_real_ne_aleph0 : (#(Set ℝ)).ord.cof ≠ ℵ₀`

as one of its seven main theorems. This rules out one specific
cardinal (`κ = ℵ₀`) as the cofinality of `|𝒫(ℝ)|`. The natural
generalisation — recorded as the parent's `conclusion.openQuestions[3]`:

> "Generalize the cf ≠ ℵ₀ corollary to cf ≠ κ for any specific κ ≤ 𝔠
> — straightforward by analogous reasoning, but worth recording as
> named theorems."

is the present OQ-04 slug. The goal is to:

1. State and prove the **general** lemma `cf(|𝒫(ℝ)|) ≠ κ` for every
   cardinal `κ ≤ 𝔠`,
2. Derive named specialisations at `κ = ℵ₀` (re-deriving the parent's
   corollary via the general form), `κ = 𝔠` (boundary case), `κ = ℵ_α`
   (aleph-indexed family, with the side hypothesis `ℵ_α ≤ 𝔠`), and
   `κ = ℶ_α` (beth-indexed family, similarly),
3. Bundle the general form together with the four specialisations
   as a single resolution theorem `oq01oq03oq04_resolution`.

### Formal Statement

```lean
-- (1) General exclusion
theorem cf_powerSet_real_ne_of_le_continuum
    {κ : Cardinal.{0}} (hκ : κ ≤ (𝔠 : Cardinal.{0})) :
    (#(Set ℝ) : Cardinal.{0}).ord.cof ≠ κ

-- (2) ℵ₀ specialisation (re-derived from the general form)
theorem cf_powerSet_real_ne_aleph0_general :
    (#(Set ℝ) : Cardinal.{0}).ord.cof ≠ ℵ₀

-- (3) 𝔠 specialisation
theorem cf_powerSet_real_ne_continuum :
    (#(Set ℝ) : Cardinal.{0}).ord.cof ≠ (𝔠 : Cardinal.{0})

-- (4) Aleph specialisation
theorem cf_powerSet_real_ne_aleph_of_aleph_le_continuum
    {α : Ordinal.{0}} (hα : (Cardinal.aleph α : Cardinal.{0}) ≤ 𝔠) :
    (#(Set ℝ) : Cardinal.{0}).ord.cof ≠ Cardinal.aleph α

-- (5) Beth specialisation
theorem cf_powerSet_real_ne_beth_of_beth_le_continuum
    {α : Ordinal.{0}} (hα : (Cardinal.beth α : Cardinal.{0}) ≤ 𝔠) :
    (#(Set ℝ) : Cardinal.{0}).ord.cof ≠ Cardinal.beth α
```

Proof template for (1):

```lean
intro h
have h1 : (𝔠 : Cardinal.{0}) < κ := h ▸ CantorsTheoremOQ01OQ03.cf_powerSet_real_gt_continuum
exact absurd (h1.trans_le hκ) (lt_irrefl _)
```

Theorems (2)–(5) are one-liners invoking (1) with the appropriate
cardinal hypothesis.

## Classification

```yaml
tier: B
significance: 6
tractability: 7
tags:
  - set-theory
  - cardinal-arithmetic
  - cofinality
  - konig-theorem
  - power-set
  - research
  - seeker-selected
```

**Significance**: 6/10 — Closes the parent's `openQuestions[3]` and
completes the family of below-continuum cofinality exclusions. Useful
as a named lemma for downstream consumers (Easton-style independence
proofs, cardinal arithmetic surveys).

**Tractability**: 7/10 — One-line proof from the parent's strict
inequality. The main complexity is in the universe-0 polymorphism of
the `Cardinal.{0}` parameters and the implicit-argument syntax of the
bundle theorem.

## Why This Matters

1. **Closes a parent-flagged open question** — The parent file's
   `openQuestions[3]` explicitly listed this generalisation as a
   "worth recording as named theorems" follow-up. Recording the named
   lemma family closes the gap between commentary and citable theorem.

2. **Family-of-corollaries pattern** — Every parent inequality of the
   form `c < cf(#X)` automatically yields the family of disequalities
   `{cf(#X) ≠ κ : κ ≤ c}`. By naming the general lemma, downstream
   proofs cite it directly rather than re-deriving the disequation
   each time.

3. **The κ = 𝔠 boundary case is new** — The parent file proved the
   strict inequality `𝔠 < cf(|𝒫(ℝ)|)` but did not separately state
   the disequational form `cf(|𝒫(ℝ)|) ≠ 𝔠`. The boundary case
   closes this small gap.

4. **Pairs naturally with Easton's theorem** — The general exclusion
   proved here is the dual of Easton's consistency result: Easton
   says "every regular cardinal > 𝔠 is consistent as cof(|𝒫(ℝ)|)",
   we say "nothing ≤ 𝔠 works". Together they give the complete
   ZFC-provable picture of which cofinalities `|𝒫(ℝ)|` can have.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `cantors-theorem-oq-01-oq-03` | **Parent**: proves `𝔠 < cf(|𝒫(ℝ)|)` (`cf_powerSet_real_gt_continuum`) — the input strict inequality. |
| `cantors-theorem-oq-01` | **Grandparent**: establishes `|𝒫(ℝ)| = 2^𝔠 = ℶ₂`. |
| `cantor-diagonalization-oq-01-oq-01-oq-02-oq-01` | **Dual (Easton)**: the consistency side of the complete-ZFC picture. |
| `cantors-theorem-oq-01-oq-02` | **Sibling**: applies the same Mathlib König constraint at related levels of the beth tower. |
| `continuum-hypothesis-oq-02` | **Related**: uses `Cardinal.lt_cof_power` (parent of the cofinality bound) for the `cf(2^ℵ₀) > ℵ₀` specialisation. |
