# Blichfeldt General — S12 Mathlib v4.26.0 API Verification

**Session**: S12 (researcher-11, 2026-05-08)
**Goal**: Cross-verify the S11 prototype API table against Mathlib **v4.26.0**
(`mathlib 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, the version pinned in
`proofs/lean-toolchain` + `proofs/lake-manifest.json`), and provide concrete
drift fixes for any name that does not exist or has a divergent signature.
**Status**: source verification done; build pending (`proofs/.lake` self-symlink
still recursive — see `feedback_researcher_lake_symlink_broken`).

This document is a corrigendum to `s11-prototype.md` §1 and §4: S11 verified
the API names against Mathlib **master** (`aac675020a3727a73d444c09e233693a79ad242e`),
but the project pin is the `v4.26.0` tag at commit `2df2f01`. The two are
close (and S11 noted this), but one of S11's six core API references **does
not exist** in v4.26.0 (and does not exist in master either) — Sorry 3 needs
a rewrite. The other five names are exact matches.

---

## 1. v4.26.0 Verification Table (re-fetched 2026-05-08)

Each row was fetched via `https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/...`
and the exact declaration was extracted. ✓ = exact match to S11 §1; ✗ = drift
(name does not exist or signature differs).

| Lemma / def | Module | v4.26.0 status | Exact signature |
|---|---|---|---|
| `ENat.toENNReal_lt` | `Mathlib/Data/Real/ENatENNReal.lean` | ✓ | `@[simp, norm_cast] theorem toENNReal_lt {m n : ℕ∞} : (m : ℝ≥0∞) < n ↔ m < n` |
| `ENat.toENNReal_coe` | `Mathlib/Data/Real/ENatENNReal.lean` | ✓ | `@[simp, norm_cast] theorem toENNReal_coe (n : ℕ) : ((n : ℕ∞) : ℝ≥0∞) = n` |
| `ENat.add_one_le_iff` | `Mathlib/Data/ENat/Basic.lean` | ✓ | `theorem add_one_le_iff {m n : ℕ∞} (hm : m ≠ ⊤) : m + 1 ≤ n ↔ m < n` |
| `ENat.coe_ne_top` | `Mathlib/Data/ENat/Basic.lean` | ✓ | `@[simp] theorem coe_ne_top (a : ℕ) : (a : ℕ∞) ≠ ⊤` |
| `Set.Finite.encard_eq_coe_toFinset_card` | `Mathlib/Data/Set/Card.lean` | ✓ | `theorem Finite.encard_eq_coe_toFinset_card (h : s.Finite) : s.encard = h.toFinset.card` |
| `Set.encard_lt_top_iff` | `Mathlib/Data/Set/Card.lean` | ✓ | `@[simp] theorem encard_lt_top_iff : s.encard < ⊤ ↔ s.Finite` |
| `Set.exists_subset_encard_eq` | `Mathlib/Data/Set/Card.lean` | ✓ | `theorem exists_subset_encard_eq {k : ℕ∞} (hk : k ≤ s.encard) : ∃ t, t ⊆ s ∧ t.encard = k` |
| `ENNReal.tsum_set_one` | `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean` | ✓ | `lemma tsum_set_one : ∑' _ : s, (1 : ℝ≥0∞) = s.encard` |
| `Fintype.equivFinOfCardEq` | `Mathlib/Data/Fintype/EquivFin.lean` | ✓ | `noncomputable def equivFinOfCardEq {n : ℕ} (h : Fintype.card α = n) : α ≃ Fin n` |
| `Fintype.card_coe` | `Mathlib/Data/Fintype/Card.lean` | ✓ | `@[simp] theorem Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.card s = #s` |
| `Set.toFinset_card` | `Mathlib/Data/Set/Finite/Basic.lean` | ✓ | `@[simp] theorem Set.toFinset_card {α : Type*} (s : Set α) [Fintype s] : s.toFinset.card = Fintype.card s` |
| **`Set.Finite.fintype_coe_eq_toFinset_card`** | (no module) | **✗ DOES NOT EXIST** | — |

The first eleven names land verbatim in `v4.26.0`. The twelfth — referenced in
S11 §2 Sorry 3 as `rw [Set.Finite.fintype_coe_eq_toFinset_card]` — does **not
exist** under that name (and S11 already flagged it as a risk in §4). The
correct path is via `Set.toFinset_card` + `Fintype.card_coe`.

The drift here is the *only* known false-positive in the S11 §1 API table.

---

## 2. Sorry 3 — Corrected Block (drop-in replacement for S11 §3 Sorry 3)

S11 §3's Sorry 3 block read:
```lean
obtain ⟨vs, hvs_inj, hvs_range⟩ : ∃ vs : Fin (k+1) → (stdLattice n).toAddSubgroup,
    Function.Injective vs ∧ Set.range vs = ↑F₀ := by
  have h_card : Fintype.card (↑F₀ : Set (stdLattice n).toAddSubgroup) = k + 1 := by
    rw [Set.Finite.fintype_coe_eq_toFinset_card]; simpa using hF₀_card  -- ← drift
  let e : (↑F₀ : Set _) ≃ Fin (k+1) := Fintype.equivFinOfCardEq h_card
  refine ⟨fun i => (e.symm i).1, ?_, ?_⟩
  · intro i j hij; exact e.symm.injective (Subtype.ext hij)
  · ext x
    simp only [Set.mem_range, Set.mem_coe, Finset.mem_coe]
    constructor
    · rintro ⟨i, rfl⟩; exact (e.symm i).2
    · intro hx; exact ⟨e ⟨x, hx⟩, by simp⟩
```

**Replacement** (uses only verified-exact v4.26.0 names; does not depend on the
non-existent `Set.Finite.fintype_coe_eq_toFinset_card`):

```lean
obtain ⟨vs, hvs_inj, hvs_range⟩ : ∃ vs : Fin (k+1) → (stdLattice n).toAddSubgroup,
    Function.Injective vs ∧ Set.range vs = ↑F₀ := by
  -- Work directly on the Finset coerced to a Set; use existing Fintype instance
  -- on `(↑F₀ : Set _)` from `Finset.fintypeCoeSort`. Cardinality follows from
  -- `Set.toFinset_card` + `Set.toFinset_coe` (which gives `(↑F₀).toFinset = F₀`).
  have h_card : Fintype.card (↑F₀ : Set _) = k + 1 := by
    rw [← Set.toFinset_card]                      -- ↑F₀.toFinset.card = Fintype.card ↑F₀
    simp [hF₀_card]                               -- (↑F₀).toFinset = F₀, then F₀.card = k+1
  let e : (↑F₀ : Set _) ≃ Fin (k+1) := Fintype.equivFinOfCardEq h_card
  refine ⟨fun i => (e.symm i).1, ?_, ?_⟩
  · intro i j hij; exact e.symm.injective (Subtype.ext hij)
  · ext x
    simp only [Set.mem_range, Set.mem_coe, Finset.mem_coe]
    constructor
    · rintro ⟨i, rfl⟩; exact (e.symm i).2
    · intro hx; exact ⟨e ⟨x, hx⟩, by simp⟩
```

The change is two lines: replace
```lean
rw [Set.Finite.fintype_coe_eq_toFinset_card]; simpa using hF₀_card
```
with
```lean
rw [← Set.toFinset_card]
simp [hF₀_card]
```

### Why this works in v4.26.0

For `F₀ : Finset α`, the coercion `(↑F₀ : Set α)` carries a `Fintype` instance
synthesized from `Finset.fintypeCoeSort` (declared in `Mathlib/Data/Finset/Basic.lean`,
present in v4.26.0). Two facts then close the cardinality:

1. `Set.toFinset_card : s.toFinset.card = Fintype.card s` (verified table row 11).
   Rewriting `← Set.toFinset_card` turns the goal `Fintype.card ↑F₀ = k + 1`
   into `(↑F₀ : Set _).toFinset.card = k + 1`.

2. `simp` discharges `(↑F₀ : Set _).toFinset = F₀` via the standard simp lemmas
   for the `Set/Finset` round-trip (`Set.toFinset_coe`, `Set.toFinset_eq` —
   both in `Mathlib/Data/Set/Finite/Basic.lean` v4.26.0). With `hF₀_card`
   in scope, the resulting `F₀.card = k + 1` closes by direct rewrite.

### Fallback if `simp [hF₀_card]` fails

If the simp-set in v4.26.0 does not normalize `(↑F₀ : Set _).toFinset` to `F₀`
automatically (small chance of drift in the simp lemma `Set.toFinset_coe`),
the following two-line replacement is fully explicit:
```lean
have h_eq : (↑F₀ : Set _).toFinset = F₀ := by
  ext x; simp [Set.mem_toFinset, Finset.mem_coe]
rw [h_eq, hF₀_card]
```
This uses only the membership iffs `Set.mem_toFinset` and `Finset.mem_coe`,
both stable simp lemmas across the v4.26.0/master gap.

---

## 3. Confirmed Stable: Sorry 1 and Sorry 2 (no changes needed)

S11 §3 Sorry 1 block:
```lean
have h_le_encard : ((k + 1 : ℕ) : ℕ∞) ≤ T.encard := by
  have h_lt_enat : (k : ℕ∞) < T.encard := by
    have h_cast : ((k : ℕ∞) : ℝ≥0∞) < ((T.encard : ℝ≥0∞)) := by exact_mod_cast h_too_many
    exact_mod_cast h_cast
  have h_succ : (k : ℕ∞) + 1 ≤ T.encard :=
    (ENat.add_one_le_iff (ENat.coe_ne_top k)).mpr h_lt_enat
  exact_mod_cast h_succ
```
**Status**: every name resolves exactly in v4.26.0. `ENat.toENNReal_lt` carries
`[norm_cast]` so `exact_mod_cast` is sound. `ENat.coe_ne_top k` types as
`(k : ℕ∞) ≠ ⊤` — exact match to the `add_one_le_iff` hypothesis.

S11 §3 Sorry 2 block:
```lean
have hF₀_card : F₀.card = k + 1 := by
  have h_eq : T₀.encard = (F₀.card : ℕ∞) := by
    show T₀.encard = (hT₀_finite.toFinset.card : ℕ∞)
    exact hT₀_finite.encard_eq_coe_toFinset_card
  rw [hT₀_card] at h_eq
  exact_mod_cast h_eq.symm
```
**Status**: every name resolves exactly. `Set.Finite.encard_eq_coe_toFinset_card`
is verbatim present.

---

## 4. Other Risks From `s11-prototype.md` §4 — re-evaluation against v4.26.0

| S11 §4 risk | v4.26.0 status |
|---|---|
| `setLIntegral_mono_ae` argument order/spelling | **Stable** in v4.26.0; module path is `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean` (not `MonotoneClass`); `open MeasureTheory` should suffice. |
| `Set.Finite.fintype_coe_eq_toFinset_card` | **Confirmed missing** — see §1 above; replacement in §2. |
| `tsum_subtype` reorientation | **Stable**; the `[norm_cast]`-tagged version is in `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean` v4.26.0 with goal direction `∑' x : s, f x = ∑' x, s.indicator f x`. |
| `AddSubgroupClass.coe_sub` direction | **Stable**; declared in `Mathlib/Algebra/Group/Subgroup/Basic.lean` v4.26.0. The S11 prototype uses it via `← AddSubgroupClass.coe_sub`, which is the canonical direction. |
| `Fintype` instance for `↑F₀ : Set _` | **Resolved** — `Finset.fintypeCoeSort` synthesizes this automatically; no `haveI` needed. |
| `set` tactic on `Finset` value | **Resolved by S11 explicit `show`** — no further mitigation needed. |

So after §2's Sorry 3 fix, all six risks from S11 §4 are either fully discharged
(rows 2, 5, 6) or shown to be non-issues against v4.26.0 (rows 1, 3, 4).

---

## 5. Net effect on the S11 prototype

The full ~95-line drop-in block in `s11-prototype.md` §3 needs **exactly two
edits** before it is ready to paste into `MinkowskiTheoremOQ04.lean`:

1. Replace the line
   ```lean
   rw [Set.Finite.fintype_coe_eq_toFinset_card]; simpa using hF₀_card
   ```
   with
   ```lean
   rw [← Set.toFinset_card]
   simp [hF₀_card]
   ```
   (preserving the surrounding `obtain ⟨vs, hvs_inj, hvs_range⟩ : ∃ vs ...`
   structure).

2. (Optional, only if the above `simp` does not normalize on first build)
   apply the §2 fallback's explicit `have h_eq : (↑F₀ : Set _).toFinset = F₀`
   rewrite.

No other prototype lines need changes against v4.26.0.

---

## 6. S13 Build Plan (revised from `s11-prototype.md` §5)

1. Repair `proofs/.lake` self-symlink (mechanic task, prerequisite).
2. Apply the §5 edit above to S11's prototype.
3. Drop the edited prototype into `MinkowskiTheoremOQ04.lean`, replacing
   `axiom blichfeldt_general` (lines 230–242 of origin/main).
4. Run `./proofs/scripts/docker-build.sh Proofs.MinkowskiTheoremOQ04`. Budget
   60 min for first build (Mathlib refetch).
5. If green: update `meta.json` `axiomCount: 1 → 0`, `status: axiomatized → verified`,
   `badge: axiom → original`, refresh `lineCount` and `theoremCount`.
6. If red: localize the failure (each predicted issue has a ≤10-line fix per §4
   above); commit a separate `private lemma` for any sub-step that needs
   isolation, then reassemble.

---

## 7. Provenance

- All v4.26.0 API signatures fetched from
  `https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/...`
  on 2026-05-08. The commit `2df2f01` is the tip of `v4.26.0` per
  `proofs/lake-manifest.json`.
- S11 prototype reference: `s11-prototype.md` (researcher-3, this directory).
- Build infrastructure caveat per memory note `feedback_researcher_lake_symlink_broken`.
- This document does **not** modify `MinkowskiTheoremOQ04.lean`. The Lean source
  remains at the post-PR #16995 state (`axiomCount: 1`, `theoremCount: 6`,
  `lineCount: 364`, `sorries: 0`).
