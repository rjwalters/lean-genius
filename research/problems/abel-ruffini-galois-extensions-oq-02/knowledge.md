# Knowledge Base: abel-ruffini-galois-extensions-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

**Goal:** Prove the Galois Correspondence Theorem (Subfields ↔ Subgroups) — the
Fundamental Theorem of Galois Theory — for a finite Galois extension `E / F`.

The correspondence is the inclusion-reversing bijection between intermediate fields
`F ⊆ K ⊆ E` and subgroups of the Galois group `Gal(E/F) = E ≃ₐ[F] E`, via
`K ↦ K.fixingSubgroup` and `H ↦ fixedField H`.

---

## Insights

- **The core theorem is already in Mathlib.** `IsGalois.intermediateFieldEquivSubgroup`
  (`Mathlib/FieldTheory/Galois/Basic.lean`) is the order isomorphism
  `IntermediateField F E ≃o (Subgroup (E ≃ₐ[F] E))ᵒᵈ`, with both round trips
  (`IsGalois.fixedField_fixingSubgroup`, `IntermediateField.fixingSubgroup_fixedField`),
  the degree dictionary upper half (`card_fixingSubgroup_eq_finrank`), and the full normal
  refinement (`normalAutEquivQuotient`, `of_fixedField_normal_subgroup`). So a verbatim
  re-export would be busywork.
- **Value-add chosen:** a consolidated "dictionary" entry that packages the core theorem
  AND derives the consequences that make it usable, several of which are not single
  Mathlib lemmas:
  - `le_iff_fixingSubgroup_le` — order-reversal as a clean iff (from the antitone maps +
    round trips).
  - `intermediateFieldEquivSubgroup'` / `card_intermediateField_eq_card_subgroup` — the
    order-forgetting bijection and the count equality (# intermediate fields = # subgroups).
  - `finrank_eq_index_fixingSubgroup` — `[K:F] = K.fixingSubgroup.index`, assembled from
    the tower law (`Module.finrank_mul_finrank`), `card_aut_eq_finrank`, the upper-half
    dictionary, and `Subgroup.index_mul_card` by cancelling the common factor `[E:K]`.
  - endpoints `fixingSubgroup_bot/top`, `fixedField_bot/top`.
  - `normalQuotientEquiv` — named quotient iso for normal H.
- **Concrete link to OQ-01:** the splitting field of `q = X⁵ − 4X + 2` is Galois over ℚ
  (`IsGalois.of_separable_splitting_field q_separable`), and OQ-01 identifies its Galois
  group with S₅, so `quintic_card_intermediateField_eq_card_subgroup` instantiates the
  count bijection on a concrete unsolvable quintic.

## Key Mathlib API (verified present in v4.26 source)

- `IsGalois.intermediateFieldEquivSubgroup [FiniteDimensional F E] [IsGalois F E]`
- `IsGalois.fixedField_fixingSubgroup`, `IntermediateField.fixingSubgroup_fixedField`
- `IntermediateField.fixingSubgroup_le`, `fixedField_le`, `fixingSubgroup_bot/top`
- `IsGalois.fixedField_top`, `card_fixingSubgroup_eq_finrank`, `card_aut_eq_finrank`
- `Module.finrank_mul_finrank`, `Module.finrank_pos`, `Subgroup.index_mul_card`
- `IsGalois.normalAutEquivQuotient`, `IsGalois.of_fixedField_normal_subgroup`
- `IsGalois.of_separable_splitting_field`

## Dead Ends

- Enumerating the actual lattice of intermediate fields for a concrete extension is hard
  in Lean (IntermediateField is not decidably enumerable), so the concrete payoff is the
  count bijection rather than an explicit lattice diagram.

---

## Sessions

### Session 2026-06-26 (Session 1) — FRESH

**Mode:** FRESH
**Outcome:** progress (proof written, build verification pending infra)

#### What I Did
- Claimed fresh problem `abel-ruffini-galois-extensions-oq-02` (EMPTY tier; no prior
  proof file, gallery dir, or knowledge).
- Read the full Mathlib `FieldTheory/Galois/Basic.lean` to confirm the FTGT API.
- Wrote `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ02.lean` (201 lines, 10 theorems,
  3 defs, 1 instance, 0 sorry, 0 axiom): the consolidated Galois-correspondence
  dictionary + the OQ-01 quintic instantiation.
- Created gallery entry `src/data/proofs/abel-ruffini-galois-extensions-oq-02/`
  (meta.json + annotations.json).

#### Key Findings
- The FTGT is fully in Mathlib; the genuine contribution is the consolidated packaging
  plus the derived corollaries (order-reversal iff, count bijection, the index half of
  the degree dictionary, named quotient iso) and the concrete S₅ link.

#### Build Status — UNVERIFIED (infra blocker)
- `docker-build.sh` failed twice (10 min apart) with a Mathlib-cache permission error:
  `/root/.cache/mathlib/*.ltar: Permission denied (os error 13)` → `leantar failed with
  error code 1`, before reaching compilation of the new file. All 6 concurrent build
  containers were affected — a host-level shared-cache/`/root/.cache` ownership problem,
  not a proof error.
- Every cited Mathlib declaration was confirmed present in the pinned v4.26 source.
- PR opened as a **draft** so the deployer does not auto-merge before the build passes.

#### Next Steps
- Re-run `./proofs/scripts/docker-build.sh Proofs.AbelRuffiniGaloisExtensionsOQ02` once
  the cache-permission infra is restored; fix any residual syntax (likely candidates:
  `Module.finrank_mul_finrank F K E` arg coercion, the rw chain in
  `finrank_eq_index_fixingSubgroup`, `OrderDual.ofDual` as an `Equiv`).
- If green, flip the PR out of draft and drop the `buildStatus` caveat from meta.json.
- Follow-up: transport the subgroup count across OQ-01's `galEquivS5` to get the exact
  number of intermediate fields of the X⁵ − 4X + 2 splitting field (= # subgroups of S₅).
