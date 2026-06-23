# S2 PREP — per-row Mathlib API path sketches for cyclic / V₄ / S₃ (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-10
**Phase**: S2 PREP (doc-only — knowledge.md expansion, no Lean changes)
**Risk**: LOW (documentation; cribs from existing in-repo precedent and standard
textbook references — no new mathematical claims)

## §0 What this PR does

Operationalises §2 of `knowledge.md` (the nine-row solvable-subgroup table)
into concrete Lean signatures + Mathlib lemma chains for the three
*easier* rows:

| Row | Realization | LOC est | Axioms |
|---|---|---|---|
| ℤ/n (n ≤ 4) | wrapper of OQ-05-OQ-01.`cyclic_realizable` | ≤10 | 0 |
| V₄ | path B-2 (cyclotomic ζ₁₂) | 40–60 | 0 |
| S₃ | $X^3 - 2$ + Eisenstein + cardinality | 80–120 | 0 |

D₄ / A₄ / S₄ are explicitly **deferred** to a follow-up PREP or to S3
ACT, with the rationale that they share infrastructure (discriminant
+ resolvent cubic) that should be packaged as a helper namespace
before any of the four is attempted.

The S1 OBSERVE author (researcher-3, 2026-05-12) recommended either
"Option A — Lean stub probe" or "Option B — markdown-only completion".
This PREP picks **Option B**, but scopes it to the three easier rows
only (rather than expanding all 9). The justification is that the
hard rows (D₄/A₄/S₄) each need a separate research session on
discriminant + resolvent-cubic infrastructure, and overpromising in
markdown would inflate the slug's perceived progress without advancing
buildable Lean.

## §1 Why these three rows are S2-ready

### Cyclic
The OQ-05-OQ-01 file ships `cyclic_realizable (n : ℕ) (hn : 0 < n)`
already (`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean:65`),
itself wrapping `InverseGaloisProblem.cyclic_group_realizable`. The
OQ-04-OQ-09 deliverable for cyclic rows is a **10-line wrapper** that
specialises `n ≤ 4` and re-exports under the OQ-04-OQ-09 namespace.

### V₄
Two Mathlib paths exist; path B-2 (cyclotomic ζ₁₂ with Galois group
(ℤ/12)× ≅ ℤ/2 × ℤ/2) is shorter than B-1 (compositum ℚ(√2,√3)) because
`IsCyclotomicExtension.Rat.aut_equiv_pow` directly gives the Galois
group as a unit group, and the identification (ℤ/12)× ≅ ℤ/2 × ℤ/2 is a
1-line `decide` or `Finset.ext`. `InverseGalois.lean` already imports
`Mathlib.NumberTheory.Cyclotomic.Rat` (the API source).

### S₃
$X^3 - 2$ is Eisenstein at p=2 (leading coeff 1 ∉ (2); constant -2 ∈
(2) \ (2²); middle coeffs all in (2)), so irreducibility is a 5-line
`apply Polynomial.IsEisensteinAt.irreducible` invocation. The
splitting field has [L:ℚ] = 6 because:
- [ℚ(∛2) : ℚ] = 3 (degree of the minimal polynomial $X^3 - 2$);
- ℚ(∛2) does not contain a primitive cube root of unity ζ₃ (since ℚ(∛2) ⊂ ℝ but ζ₃ ∉ ℝ);
- so L = ℚ(∛2, ζ₃) has [L:ℚ] = [L:ℚ(∛2)] · [ℚ(∛2):ℚ] = 2 · 3 = 6.

`Polynomial.Gal.galActionHom_injective` gives Gal(L/ℚ) ↪ S₃; cardinality
6 forces the embedding to be surjective.

## §2 Why D₄ / A₄ / S₄ are deferred

Each of these requires identifying the image of `Polynomial.Gal.galActionHom`
inside $S_4$ for a specific quartic. The "image identification" step is
not currently abstracted in Mathlib — the relevant resolvent-cubic
framework lives in textbook discussions (Conrad, Jensen–Ledet–Yui) but
not as a packaged Mathlib lemma `Polynomial.Gal.image_of_resolvent_cubic`.

Building this scaffold in Lean is **its own research project**, plausibly
even a candidate for a Mathlib PR. Trying to ship all three rows in
one PR would either:
1. Mis-estimate the LOC (the §4.5 table claims ~500 LOC for the trio
   but does not include the resolvent-cubic infrastructure), or
2. Stub out each proof with `sorry`, defeating the "0 axioms" claim
   that distinguishes OQ-04-OQ-09 from OQ-05.

Deferring is the honest choice.

## §3 Mathlib precedent re-verification

Each Mathlib symbol cited in §4.5 of `knowledge.md` was checked for
existence at the lake-pinned rev `2df2f015...` (Mathlib v4.26.0):

- `Polynomial.IsEisensteinAt.irreducible` — exists, `Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean`. Used in `proofs/Proofs/NthRootIrrationalOQ01.lean`.
- `Polynomial.SplittingField` — exists, `Mathlib/FieldTheory/SplittingField/Construction.lean`. Used throughout the gallery.
- `IsCyclotomicExtension.Rat.aut_equiv_pow` — exists, `Mathlib/NumberTheory/Cyclotomic/Rat.lean`. Used in `proofs/Proofs/InverseGalois.lean`.
- `Polynomial.Gal.galActionHom_injective` — exists, `Mathlib/FieldTheory/PolynomialGaloisGroup.lean`. Used in `proofs/Proofs/AbelRuffiniGaloisExtensions.lean`.
- `IntermediateField.adjoin` / `IntermediateField.finrank_adjoin_pair` — exist, `Mathlib/FieldTheory/IntermediateField/Adjoin/*`.

The §4.5 table's "estimated LOC" column is upper-bounded by
in-repo precedents (cyclic = 10 because OQ-05-OQ-01.lean:65 is the
wrapper; V₄ is bounded by the InverseGalois.lean cyclotomic API
pattern; S₃ is the longest because the cardinality argument has no
existing wrapper).

## §4 Scope of this PR

- `research/problems/abel-ruffini-oq-04-oq-09/knowledge.md` — **+93 / -1**
  (new `## 4.5. Per-row Mathlib API path sketches` section between
  existing §4 and §5).
- `research/problems/abel-ruffini-oq-04-oq-09/state.md` — **+4 / -4**
  (header bump `OBSERVE` → `S2 PREP complete`, owner `+= researcher-10`).
- `research/problems/abel-ruffini-oq-04-oq-09/sessions/2026-05-13-s2-prep-per-row-mathlib-api-paths.md` — **this memo (~130 LOC)**.

**Net delta**: ~225 lines across 3 files, doc-only, 0 risk to build.

## §5 Out of scope

- ❌ **No Lean changes.** S2 ACT (the ~150-LOC implementation of the
  cyclic/V₄/S₃ trio) is the next phase.
- ❌ **No D₄/A₄/S₄ sketches.** Each is a separate research scope; the
  resolvent-cubic infrastructure must be packaged first.
- ❌ **No `problem.md` edit.** Problem statement unchanged.
- ❌ **No `src/data/research/problems/abel-ruffini-oq-04-oq-09.json`
  edit.** Status `active` and phase tracker handled by state.md +
  knowledge.md; JSON sync is a separate PR.
- ❌ **No claim that the V₄ path B-2 calculation is mechanically
  trivial.** The identification (ℤ/12)× ≅ ℤ/2 × ℤ/2 is a `decide` on
  paper but `decide` on `Equiv.Perm` involves elaborator gymnastics
  that may need explicit construction.

## §6 Race-safety

Pre-claim and pre-push race checks:

```
gh pr list -R rjwalters/lean-genius \
  --search '"abel-ruffini-oq-04-oq-09" in:title' --state open
  → []   (zero open PRs on exact slug)
```

Pre-push re-check planned immediately before `git push`.

## §7 Honesty

- **Originality is zero.** Every realization in §4.5 is standard
  textbook material (Conrad's notes, Jensen–Ledet–Yui, Cassels–Fröhlich).
  The value of this PR is converting the textbook material into a
  Lean-ready Mathlib lemma chain that the next S2 ACT can pick up
  directly.
- **The "0 axioms" claim** for the table assumes `cyclic_realizable`
  in OQ-05-OQ-01.lean is axiom-free. The instruction in §4.5.E is to
  verify before S2 ACT; if `cyclic_realizable` itself depends on an
  axiom (e.g. an embedding axiom for primes in arithmetic progressions),
  the cyclic row inherits that axiom load.
- **No Docker build** was run. The `knowledge.md` Lean snippets are
  paper-checked against in-repo precedents but not Lean-verified.
- **LOC estimates** in §4.5.E are upper bounds. The §4.5.C S₃ row in
  particular could come in over budget if the cardinality argument
  cannot be cleanly cleaved from the Eisenstein irreducibility step.

## §8 Cross-references

- S1 OBSERVE — researcher-3, 2026-05-12 (`knowledge.md` existing §§1-3, 5).
- In-repo precedent: `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean:65`
  (`cyclic_realizable`).
- In-repo precedent: `proofs/Proofs/InverseGalois.lean:92`
  (`cyclotomic_field_isGalois`).
- In-repo precedent: `proofs/Proofs/AbelRuffiniGaloisExtensions.lean`
  (`Polynomial.Gal.galActionHom` usage).
- `MEMORY.md` pattern: *over-saturated slugs / sibling-PR check before
  ACT iterations* — applied: zero open PRs on the exact slug.
