# Problem: König's constraint on |𝒫(ℝ)| in Lean 4

## Statement

### Plain Language

The parent gallery proof `cantors-theorem-oq-01` (`|𝒫(ℝ)| = ℶ₂`)
contains an explicitly empty Part 7 ("König's Constraint on |𝒫(ℝ)|",
file `proofs/Proofs/CantorsTheoremOQ01.lean` lines 214–222) that
states the cofinality bound

> **König's theorem (1905)** — `cf(2^𝔠) > 𝔠`

informally in a comment but proves no Lean theorem. The sibling proof
`cantors-theorem-oq-01-oq-02` then explicitly enumerates this gap as
an open question (its `conclusion.openQuestions[1]`):

> Can König's cofinality constraint cf(2^κ) > κ be formalized for
> arbitrary κ without axioms? *(Mathlib has Cardinal.lt_cof_power)*

The OQ-03 child claimed by this slug is the natural follow-up: fill
that empty Part 7 with axiom-free Lean theorems that

1. state König's cofinality constraint `cf(2^𝔠) > 𝔠` and prove it
   from Mathlib's `Cardinal.lt_cof_power` (or whatever its current
   name is — see §"Mathlib API verification" in `knowledge.md`),
2. derive the canonical aleph-exclusion corollary
   `|𝒫(ℝ)| ≠ ℵ_ω` (since `cf(ℵ_ω) = ℵ_0 < 𝔠 < cf(|𝒫(ℝ)|)`),
3. generalise the corollary to "any limit ordinal `λ` with
   `cf(λ) ≤ 𝔠`", which is the precise content of König's constraint
   on the aleph-index of `ℶ₂`,
4. (stretch) state König's general sum-product form
   `(∀ i, κ_i < λ_i) → ∑ κ_i < ∏ λ_i` from `Cardinal.sum_lt_prod`,
   and connect it to the cofinality bound.

### Formal Statement

The four target theorems (Lean 4 statements; bodies pending S2):

```lean
-- (1) König's constraint on |𝒫(ℝ)|.
theorem konig_cof_powerSet_real :
    (𝔠 : Cardinal.{0}) < (#(Set ℝ)).ord.cof

-- (2) The aleph-omega exclusion.
theorem powerSet_real_ne_aleph_omega :
    (#(Set ℝ) : Cardinal.{0}) ≠ Cardinal.aleph Ordinal.omega0

-- (3) Generalized aleph-exclusion (any small-cofinality aleph).
theorem powerSet_real_ne_aleph_of_cof_le_continuum
    {o : Ordinal} (ho : o.IsLimit) (hcof : o.cof ≤ 𝔠) :
    (#(Set ℝ) : Cardinal.{0}) ≠ Cardinal.aleph o

-- (4) König's general inequality (the underlying Mathlib lemma).
theorem konig_sum_lt_prod {ι : Type u} (f g : ι → Cardinal.{u})
    (H : ∀ i, f i < g i) :
    Cardinal.sum f < Cardinal.prod g
```

Theorem (4) is essentially a re-export of `Cardinal.sum_lt_prod`
(if it exists under that name); (1) is its specialisation to a
single-cardinal cofinality bound; (2) and (3) are the canonical
applications that motivate the whole construction.

## Classification

```yaml
tier: B
significance: 6
tractability: 6
tags:
  - set-theory
  - cardinality
  - cofinality
  - konig-theorem
  - beth-numbers
  - continuum-hypothesis
  - foundations
  - seeker-selected
  - gallery-extracted
```

**Significance**: 6/10 — Closes a known gap in the parent's Part 7
and gives the cleanest possible aleph-exclusion theorem for `ℶ₂`.

**Tractability**: 6/10 — The cardinality machinery is fully present
in Mathlib (`Cardinal.lt_cof_power` is referenced in the sibling
proof's open-question list, suggesting it exists). The only risk is
API drift: the exact lemma name may have changed since the sibling
was written. S1 (this iteration) is OBSERVE-only; S2 verifies the
API and writes the file.

## Why This Matters

1. **Closes an explicitly noted gap** — The parent file has an
   empty Part 7 ("PART 7: König's Constraint on |𝒫(ℝ)|") with no
   Lean theorems beneath it. Filling it is a low-risk, high-clarity
   contribution.

2. **Removes the "trivial obstruction" excuse for the aleph-index
   open problem** — Without König's constraint, one might wonder
   whether `|𝒫(ℝ)| = ℵ_ω` is consistent with ZFC. König's theorem
   says no: `|𝒫(ℝ)|` cannot be any cardinal of cofinality ≤ `𝔠`.
   Easton's theorem (1970) tells us *this is the only constraint*
   beyond `> ℵ_0` — every other regular cardinal is consistent.
   So König's constraint is the "complete" ZFC obstruction.

3. **Reusable cofinality bounds** — Once `konig_cof_powerSet_real`
   and `powerSet_real_ne_aleph_of_cof_le_continuum` exist, they
   plug directly into the OQ-04 sibling (Easton's theorem
   formalisation, currently a stub) and give the GCH-question
   formalisations more teeth.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `cantors-theorem-oq-01` | Parent: contains the empty Part 7 this OQ aims to fill. |
| `cantors-theorem-oq-01-oq-02` | Sibling: its `openQuestions[1]` is exactly the question of this OQ. |
| `cantor-diagonalization-oq-01-oq-01-oq-02-oq-01` | Easton's theorem stub — consumes the cofinality bound. |
| `cantor-diagonalization-oq-04-oq-01` | Setoid-refinement OQ — uses cardinality machinery from the same Mathlib chapter. |
