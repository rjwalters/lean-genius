# Knowledge Base: angle-trisection-oq-02-oq-01-oq-02-oq-03

Full Wantzel–Galois constructibility theorem via Mathlib Galois correspondence
and 2-group structure — the **sufficiency** direction.

---

## Problem Understanding

Goal: the deep half of the Wantzel–Galois biconditional,

> if `Gal(splitting field of minpoly ℚ α)` is a 2-group, then `α` is
> constructible (lies in a tower of quadratic extensions).

The gallery **already contains** the necessity half and all of the surrounding
scaffolding. The precise open frontier is the single `sorry`:

- `AngleTrisectionOQ02OQ04OQ01.galois_two_group_implies_tower`
  (`proofs/Proofs/AngleTrisectionOQ02OQ04OQ01.lean:240`)
  `IsPGroup 2 (minpoly ℚ α).Gal → ConstructibleViaTower α`

and its converse `tower_implies_galois_two_group` (`:263`). The combined
`tower_iff_galois_two_group` (`:281`) is `⟨converse, this⟩`, so proving this
sorry closes the sufficiency direction of the whole equivalence.

### What is already PROVED in the gallery (do not redo)

In `AngleTrisectionOQ02OQ04OQ01.lean` (compiles, 0 axioms except the 2 sorries):

- `QuadraticTower ℚ ℝ K n` — inductive tower of degree-2 steps, phrased over the
  **base** field (`finrank ℚ L = 2 · finrank ℚ K`) to dodge the missing
  `Module ↥K ↥L` instance.
- `ConstructibleViaTower α := ∃ K n, QuadraticTower ℚ ℝ K n ∧ α ∈ K`.
- `quadratic_tower_degree` : tower of height `n` ⟹ `finrank ℚ K = 2^n`.
- `tower_ideg_pow_two` : `ConstructibleViaTower α ⟹ [ℚ(α):ℚ] = 2^m`.
- **`exists_index_two_subgroup`** (`:162`): every non-trivial finite 2-group has
  a subgroup of index 2 — proved via `Sylow.exists_subgroup_card_pow_prime` +
  `Subgroup.card_mul_index`. **This is the atom the tower construction iterates.**
- `two_group_subgroup` (`= IsPGroup.to_subgroup`), `two_group_solvable`,
  `two_group_card_pow_two`.

In siblings (necessity side, already done — the obstruction half):
- `AngleTrisectionOQ02OQ01OQ03.galois_pgroup_implies_degree_is_pow_p`
  (p-group Gal ⟹ degree is a power of p), via `natDegree_dvd_card_gal` +
  `IsPGroup.iff_card`.
- `AngleTrisectionOQ02OQ01OQ02OQ02.*` — the arithmetic core
  (`not_isPowTwo_of_odd_prime_dvd`) shared by the degree side and the group side.

---

## Insights

### I1 — The problem reduces to ONE pure-group-theory lemma + Galois-correspondence glue

`galois_two_group_implies_tower` decomposes cleanly into three pieces:

- **(L1, pure group theory — TRACTABLE NOW, ~60 lines).**
  `exists_index_two_chain`: a finite 2-group `G` admits a descending chain of
  subgroups `⊤ = H₀ ⊋ H₁ ⊋ … ⊋ Hₙ = ⊥` with `[Hᵢ : Hᵢ₊₁] = 2` for all `i`
  (equivalently `Nat.card Hᵢ = 2 · Nat.card Hᵢ₊₁`).
  *Proof*: strong induction on `Nat.card G`. If `G` is trivial the chain is the
  singleton; otherwise `exists_index_two_subgroup` (ALREADY PROVED) peels off an
  index-2 subgroup `H`, which is again a 2-group (`IsPGroup.to_subgroup`) of half
  the order, so the induction hypothesis gives a chain inside `H`; prepend `⊤`.
  Every lemma this needs is attested as compiling in the corpus. **This is the
  "2-group structure" the problem title names, and it is the correct immediate
  increment.**

- **(L2, Galois correspondence — ~150 lines of attested API).**
  Let `E` be the splitting field and `G = Gal(E/ℚ)` with `IsGalois ℚ E`. The
  fixed fields of the L1 chain give an ascending field tower
  `ℚ = fixedField H₀ ⊆ fixedField H₁ ⊆ … ⊆ fixedField Hₙ = E`.
  Each step is quadratic **over the base**, exactly the gallery's
  `QuadraticTower.step` shape:
  `finrank ℚ (fixedField Hᵢ) = [G : Hᵢ] = |G| / |Hᵢ|`, and since `|Hᵢ|` halves at
  each step (`[Hᵢ:Hᵢ₊₁] = 2`), `finrank ℚ (fixedField Hᵢ₊₁) = 2 · finrank ℚ (fixedField Hᵢ)`.
  Core lemma: `IntermediateField.finrank_fixedField_eq_card` (attested, 7 uses;
  gives `finrank (fixedField H) E = Nat.card H`), combined with the tower law
  `finrank_bot_mul_relfinrank` (attested) to move to base-relative degrees.
  The bijection is `IsGalois.intermediateFieldEquivSubgroup` (attested, 5 uses) —
  **note: `problem.md` cites `IntermediateField.orderIsoOfGal`; the corpus-verified
  name is `IsGalois.intermediateFieldEquivSubgroup` / `…EquivSubgroup'`.**

- **(L3, membership bridge).** `α` is a root of `minpoly ℚ α`, which splits in `E`,
  so `α ∈ E = fixedField Hₙ`, the top of the tower ⟹ `ConstructibleViaTower α`.

### I2 — The REAL blocker is `Polynomial.Gal` ↔ `IntermediateField.fixingSubgroup` glue

The file itself flags this (`:304`, ❌ item 1). Mathlib keeps two Galois-group
notions apart: `Polynomial.Gal p := p.SplittingField ≃ₐ[ℚ] p.SplittingField`
(the group in the statement) versus the intermediate-field / `fixingSubgroup`
machinery over the concrete extension `E = p.SplittingField`. Bridging them —
establishing `IsGalois ℚ p.SplittingField` and identifying `p.Gal` with
`E ≃ₐ[ℚ] E` so the correspondence API applies — is ~100 lines of engineering, not
deep mathematics. **This glue, not any missing theorem, is the bottleneck.**

### I3 — Why the sorry is genuinely hard: the tower must live in ℂ, not ℝ (STATED SUBTLETY)

`galois_two_group_implies_tower` is phrased with `α : ℝ` and
`ConstructibleViaTower α` over `IntermediateField ℚ ℝ`. But the fixed-field tower
of I1–I2 is built from the **Galois closure `E`**, which is in general a
non-real subfield of `ℂ` (a real constructible `α` can have a complex Galois
closure — e.g. `[ℚ(α):ℚ] = 4` with dihedral closure of order 8). The subgroup
chain therefore yields a tower of quadratic extensions **inside ℂ**, not inside
ℝ. So the clean Galois-theoretic argument proves the **ℂ-valued** statement; the
gallery's ℝ-valued `ConstructibleViaTower` needs an additional real-descent step
(a real constructible number does lie in a tower of *real* quadratic extensions
by the planar-intersection argument, but that tower is **not** the fixed-field
tower of the closure). This mismatch is a concrete reason the sorry is stuck and
is estimated at ~500 lines.

**Recommendation:** prove sufficiency first in the natural ℂ setting —
`galois_two_group_implies_tower_C (α : ℂ) : IsPGroup 2 (minpoly ℚ α).Gal → ConstructibleViaTower_ℂ α`
with `QuadraticTower ℚ ℂ` — where L1+L2+L3 close it directly. Treat the ℝ-descent
as a separately-scoped follow-up rather than conflating it with the group-theory
core.

---

## Proof Blueprint (executable once the build/Aristotle blackout lifts)

```
-- L1  (pure group theory; build on the already-proved exists_index_two_subgroup)
theorem exists_index_two_chain {G : Type*} [Group G] [Fintype G]
    (hG : IsPGroup 2 G) :
    ∃ (n : ℕ) (H : Fin (n + 1) → Subgroup G),
      H 0 = ⊤ ∧ H (Fin.last n) = ⊥ ∧
      (∀ i : Fin n, H i.succ ≤ H i.castSucc) ∧
      (∀ i : Fin n, Nat.card (H i.castSucc) = 2 * Nat.card (H i.succ))
  -- strong induction on Nat.card G; peel index-2 subgroup, recurse on it.

-- L2  fixed-field tower (needs IsGalois ℚ E and the Gal↔fixingSubgroup bridge, I2)
--     step degree via IntermediateField.finrank_fixedField_eq_card + finrank_bot_mul_relfinrank.

-- L3  α ∈ E = fixedField ⊥  (root splits in splitting field) ⟹ ConstructibleViaTower_ℂ α.
```

Verified-available Mathlib/corpus API (all attested in compiling `proofs/Proofs/*.lean`):
`IsPGroup.iff_card`, `IsPGroup.to_subgroup`, `IsPGroup.isNilpotent`,
`Sylow.exists_subgroup_card_pow_prime`, `Subgroup.card_mul_index`,
`Subgroup.index_eq_card`, `IntermediateField.finrank_fixedField_eq_card`,
`IntermediateField.finrank_bot_mul_relfinrank`,
`IsGalois.intermediateFieldEquivSubgroup`, `IsGalois.card_aut_eq_finrank`,
`IsGalois.fixedField_fixingSubgroup`, `natDegree_dvd_card_gal`.

---

## Dead Ends / Cautions

- Do **not** re-prove `exists_index_two_subgroup`, `quadratic_tower_degree`, or
  the arithmetic obstruction — all already in the gallery.
- Do **not** commit a new `proofs/Proofs/*.lean` under the current
  Docker+Aristotle blackout: the lakefile globs `Proofs/`, so any file that fails
  to compile breaks the **entire** gallery build. L1 must be build-verified
  before it is committed.
- The `α : ℝ` phrasing (I3) is the trap: attempting L2 directly into
  `IntermediateField ℚ ℝ` will not close because the closure is complex.

---

## Dead Ends

[none disproved yet — see Cautions above]

---

## Session Log

### Session 2026-07-04 (Session 1, researcher-6) — ORIENT

**Mode**: FRESH  **Outcome**: ORIENT blueprint (build-independent; blackout)

Localized the target to the exact open sorry `galois_two_group_implies_tower`,
inventoried the substantial existing scaffolding (QuadraticTower, index-2 subgroup
lemma), decomposed sufficiency into L1 (pure group-theory chain) + L2 (fixed-field
tower) + L3 (membership), statically verified every cited Mathlib name against the
compiling corpus, identified the `Polynomial.Gal`↔`fixingSubgroup` glue as the real
bottleneck (I2), and surfaced the ℝ-vs-ℂ tower subtlety (I3) that explains why the
sorry is hard — with a concrete corrective (prove the ℂ version first). Next
increment: `exists_index_two_chain` (L1), fully tractable, deferred to a
build-capable session. Docker (containerd blob I/O error) and Aristotle (404) both
down, so no Lean was compiled or committed.
