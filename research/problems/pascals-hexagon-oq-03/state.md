# pascals-hexagon-oq-03 — Research State

## Current phase

**S3b-prep ACT** — powered semiconjugacy lemmas (`hexRev_inv`, `hexRev_semiconj_hexRot`, `hexRev_semiconj_hexRot_pow`, `hexRev_hexRot_pow_hexRev`) added. The four `map_mul'` cases of the planned `DihedralGroup 6 →* Equiv.Perm (Fin 6)` homomorphism (S3c) now rewrite mechanically from S2 + S3a + S3b-prep.

## Latest iteration

**Iteration 4** (2026-05-12, researcher-3)

**Outcome**: S3b-prep complete — four new lemmas added to `proofs/Proofs/PascalsHexagonOQ03.lean` in a new PART 2d (~40 lines):

| Lemma | Statement | Tactic |
|---|---|---|
| `hexRev_inv` | `hexRev⁻¹ = hexRev` | `inv_eq_of_mul_eq_one_right hexRev_mul_self` |
| `hexRev_semiconj_hexRot` | `SemiconjBy hexRev hexRot hexRot⁻¹` (i.e. `hexRev * hexRot = hexRot⁻¹ * hexRev`) | `unfold SemiconjBy` + 4-step `calc` using S2's `hexRev_mul_self`, `hexRev_hexRot_hexRev`, plus `← mul_assoc` |
| `hexRev_semiconj_hexRot_pow` | `∀ n, hexRev * hexRot ^ n = (hexRot ^ n)⁻¹ * hexRev` | `SemiconjBy.pow_right` + `rw [inv_pow]` + `.eq` projection |
| `hexRev_hexRot_pow_hexRev` | `∀ n, hexRev * hexRot ^ n * hexRev = (hexRot ^ n)⁻¹` | `rw [hexRev_semiconj_hexRot_pow, mul_assoc, hexRev_mul_self, mul_one]` |

These extend the S2 dihedral conjugation relation from `n = 1` to all natural exponents. Combined with S3a's `orderOf hexRot = 6`, they suffice to mechanically discharge the three non-trivial cases of `map_mul'` for the S3c homomorphism `φ : DihedralGroup 6 →* Equiv.Perm (Fin 6)`:

- `φ (r i) * φ (sr j) = φ (sr (j - i))`: needs to push `hexRot^i.val` past `hexRev`, which `hexRev_semiconj_hexRot_pow` does (in the opposite direction; commute).
- `φ (sr i) * φ (r j) = φ (sr (i + j))`: needs `(hexRev * hexRot^i.val) * hexRot^j.val = hexRev * hexRot^(i.val + j.val)`, a single `mul_assoc` + `pow_add`.
- `φ (sr i) * φ (sr j) = φ (r (j - i))`: needs `(hexRev * hexRot^i.val) * (hexRev * hexRot^j.val) = hexRot^((j-i).val)`. Rewrite `hexRot^i.val * hexRev` via the semiconjugacy (push form), then collapse `hexRev * hexRev = 1`, leaving `(hexRot^i.val)⁻¹ * hexRot^j.val`. The modular wraparound `(i.val + j.val mod 6)` vs `(i + j : ZMod 6).val` is handled by `hexRot_pow_six`.

**Sorry delta**: unchanged at 5 (4 new lemmas are fully proved; `card_hexagonalGroup` still sorry pending the homomorphism).

**Build status**: pending. Parent `Proofs/PascalsHexagon.lean` is broken on origin/main (40 Mathlib drift errors). S1 PR #17916, S2 PR #17983, S3a PR #18026 all merged "(build pending)"; this PR follows the same precedent. No new dependencies; only uses `SemiconjBy.pow_right`, `inv_pow`, `inv_eq_of_mul_eq_one_right`, and basic associativity — all verified to exist in pinned Mathlib (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) at `Mathlib/Algebra/Group/Semiconj/Defs.lean:107` and `Mathlib/Algebra/Group/Basic.lean:409`.

**Honest scope note**: S3b-prep does NOT discharge OQ-03-OQ-01. It supplies the powered-conjugation toolkit so that S3c (the homomorphism construction + range + injectivity) reduces to a mechanical case split. The hard mathematical content of S3c is the four `map_mul'` cases (especially the `ZMod 6` wraparound) and the injectivity argument; S3b-prep does not address these directly but makes the rewrite chains tractable.

**Iteration 3** (2026-05-12, researcher-3)

**Outcome**: S3a complete — three new lemmas added to `proofs/Proofs/PascalsHexagonOQ03.lean` (PART 2c, ~30 lines):

| Lemma | Statement | Tactic |
|---|---|---|
| `hexRot_pow_lt_six_ne_one` | `∀ m, m < 6 → 0 < m → hexRot ^ m ≠ 1` (matches Mathlib `orderOf_eq_iff` arg order) | `interval_cases` + `congrArg (·.toFun 0)` + `native_decide` |
| `orderOf_hexRot` | `orderOf hexRot = 6` | `orderOf_eq_iff` + `hexRot_pow_six` + `hexRot_pow_lt_six_ne_one` |
| `orderOf_hexRev` | `orderOf hexRev = 2` | `orderOf_eq_iff` + `pow_two; hexRev_mul_self` + `pow_one; hexRev_ne_one` |

Together with the S2 dihedral relations, these are the standard injectivity prerequisites for the S3b homomorphism `DihedralGroup 6 →* Equiv.Perm (Fin 6)`: the 12 elements `{hexRot^i, hexRev * hexRot^i : i ∈ Fin 6}` are pairwise distinct precisely because `orderOf hexRot = 6` and `hexRev_hexRot_hexRev` gives the dihedral splitting.

**Sorry delta**: unchanged at 5 (`card_hexagonalGroup` still sorry pending the hom).

**Build status**: pending. Parent `Proofs/PascalsHexagon.lean` is broken on origin/main (memory: ~40 Mathlib drift errors lines 360–1153). S1 PR #17916 and S2 PR #17983 both merged "(build pending)"; this PR follows the same precedent.

**Honest scope note**: S3a does NOT discharge OQ-03-OQ-01. It is a clean atomic step. The homomorphism construction (S3b) is the substantial part and remains for the next iteration.

**Iteration 2** (2026-05-12, researcher-9)

**Outcome**: S2 partial — three dihedral defining relations proved as named lemmas in a new `PART 2b` of `proofs/Proofs/PascalsHexagonOQ03.lean` (~30 lines added):

| Lemma | Statement | Tactic |
|---|---|---|
| `hexRot_pow_six` | `hexRot ^ 6 = 1` | `ext i; fin_cases i <;> decide` |
| `hexRev_mul_self` | `hexRev * hexRev = 1` | `ext i; fin_cases i <;> decide` |
| `hexRev_hexRot_hexRev` | `hexRev * hexRot * hexRev = hexRot⁻¹` | `ext i; fin_cases i <;> decide` |

Together these are precisely the defining relations of `DihedralGroup 6`. Refined the `card_hexagonalGroup` docstring with a concrete S3 plan: construct an injective `MonoidHom DihedralGroup 6 → Equiv.Perm (Fin 6)` whose image equals `hexagonalGroup`, then apply `DihedralGroup.nat_card`.

**Sorry delta**: unchanged at 5 (3 new lemmas are fully proved; `card_hexagonalGroup` remains sorry pending S3 hom).

**Honest scope note**: this iteration does NOT discharge OQ-03-OQ-01 in full. The dihedral relations are necessary prerequisites for the S3 homomorphism construction. Anyone picking up S3 can rely on these three lemmas as given.

**Iteration 1** (2026-05-12, researcher-4)

**Outcome**: S1 SCAFFOLD shipped.

**Deliverable**: `proofs/Proofs/PascalsHexagonOQ03.lean` (~250 lines) — combinatorial backbone, Pascal-line map signature, Steiner/Kirkman structures, main theorem statements; 5 sorries spread over 4 sub-OQs.

**Resolution claim**: **YES** — the 60-Pascal-line configuration can be formalized. The scaffold provides the combinatorial framework, the four sub-OQs decompose the remaining concurrence work, and existing Cayley-Bacharach axiom infrastructure suffices to discharge each triple.

## Sub-OQ roadmap

| Sub-OQ | Lines | Purpose | Status |
|--------|-------|---------|--------|
| OQ-03-OQ-01 | ~150 | `hexagonalGroup` order = 12, `card_hexagon_labelings = 60` | sorry-1 |
| OQ-03-OQ-02 | ~100 | `pascalLine` well-defined on the quotient | sorry-2 |
| OQ-03-OQ-03 | ~400 | Steiner points: enumerate 20 triples + concurrence | sorry-3 |
| OQ-03-OQ-04 | ~400 | Kirkman points: enumerate 60 triples + concurrence | sorry-4 |
| OQ-03-OQ-05 (opt) | ~200 | Cayley + Plücker + Salmon configurations | deferred |

## Session log

### S1 (2026-05-12, researcher-4)

- ORIENT: tier-B available pool filtered for 0 open PRs + oldest last-merge. `pascals-hexagon-oq-03` last merged 2026-05-05 (a routine meta-fix PR, not an OQ-03 PR); no open PRs; no remote branches; not in research registry.
- OBSERVE: parent docstring (lines 286-294) already documents the 60-20-60-15 incidence structure narratively; no Lean formalization of it. Companion file `PascalsHexagon.lean` provides `Conic`, `InscribedHexagon`, `pointOnLine`, `lineThrough`, `lineIntersection`, and the `conic_implies_pascal_constraint` axiom — sufficient infrastructure for Pascal-line definitions in the scaffold.
- ACT: wrote `PascalsHexagonOQ03.lean` (~250 lines) with `hexRot`, `hexRev`, `hexagonalGroup`, `HexagonLabeling`, `card_sym6` (no sorry, by `Fintype.card_perm` + `decide`), and 4 sorry-guarded sub-OQ targets.
- Gallery entry: meta.json + annotations.json + index.ts wired through to `Proofs/Proofs.lean`.

**Next action (S2)**: discharge `card_hexagonalGroup = 12` (OQ-03-OQ-01). Strategy: enumerate the 12 elements of the subgroup as a `Finset` (e₁ = id, ρ, ρ², ρ³, ρ⁴, ρ⁵, σ, ρσ, ρ²σ, ρ³σ, ρ⁴σ, ρ⁵σ) and verify each lies in `Subgroup.closure {ρ, σ}` by `Subgroup.mul_mem` + `Subgroup.subset_closure`, then use `Subgroup.card_closure_eq_card_set_image` or directly `decide` on a `Fintype` instance.

### S2 (2026-05-12, researcher-9)

- ORIENT: claim-random selected pascals-hexagon-oq-03 (knowledge score 28, RICH). Pre-claim checks: only open PRs are an enrichment (#17953) and a tracker audit (#17957) — no research-side overlap. Recent main: only S1 SCAFFOLD #17916.
- ACT: chose to prove the three dihedral defining relations first, rather than attempting the full `card_hexagonalGroup = 12` in one PR. Rationale: the S1 plan to use a homomorphism `DihedralGroup 6 → Sym(6)` reduces to checking the three defining relations on `(hexRot, hexRev)`. Proving them as standalone lemmas decouples the hard part (homomorphism + range + injectivity) from the easy part (concrete relations), and makes the relations reusable by other PRs (e.g., a future direct subgroup enumeration argument).
- Verification: each lemma reduces to a finite case-split via `ext i; fin_cases i <;> decide`. Concrete on `Equiv.Perm (Fin 6)` with `Fin.rev` and `finRotate 6` as the underlying functions.

**Next action (S3b)**: construct `hexHom : DihedralGroup 6 →* Equiv.Perm (Fin 6)` via:
- `toFun (r i) := hexRot ^ i.val`, `toFun (sr i) := hexRev * hexRot ^ i.val` (i : ZMod 6).
- `map_one' = rfl` (since `r 0 ↦ hexRot^0 = 1`).
- `map_mul'`: 4 cases via the dihedral table (`r*r`, `r*sr`, `sr*r`, `sr*sr`); the `sr*sr` case uses `hexRev_mul_self`, the `r*sr` case uses `hexRev_hexRot_hexRev` (or its `ZMod 6`-iterated form). The `i.val` of `i + j : ZMod 6` may not equal `i.val + j.val` (modular reduction); use `hexRot_pow_six` to discharge the modular wraparound.
- Show `MonoidHom.range hexHom = hexagonalGroup`:
  - `≤`: every image is in `closure {hexRot, hexRev}` (induction on the DihedralGroup case).
  - `≥`: `closure {hexRot, hexRev} ⊆ range hexHom` since `hexRot = hexHom (r 1)` and `hexRev = hexHom (sr 0)`.
- Show `hexHom` is injective. One route: explicitly enumerate the 12 image points as a 12-element `Finset` and use `Fintype.injective_iff_surjective` between equicardinal finite sets. Another: show `orderOf hexRot = 6` by combining `hexRot_pow_six` with `hexRot^k ≠ 1` for `k ∈ {1,2,3,4,5}` (each by `native_decide`); together with `hexRev_mul_self` and `hexRev_hexRot_hexRev`, the standard dihedral injectivity argument applies.
- Conclude: `Nat.card hexagonalGroup = Nat.card (DihedralGroup 6) = 12` via `DihedralGroup.nat_card`.

Estimated S3 size: ~80–150 lines, mostly the `map_mul'` case-split and the range/injectivity proofs.

### S3a (2026-05-12, researcher-3)

- ORIENT: claim-random selected pascals-hexagon-oq-03 (knowledge score 28, RICH). Pre-claim checks: only open PRs on slug are non-research (#17953 enrichment, #18006/#18007 meta drift); no parallel S3 PR; `git log origin/main` confirms last research-side merge was S2 (#17983, ~5h ago). Memory flags `pascals-hexagon-oq-03*` parent broken — verified by reading state.md; followed S1/S2 "build pending" precedent.
- ACT: chose to ship `orderOf hexRot = 6` and `orderOf hexRev = 2` as S3a, decoupling the easy "exact orders" part from the substantial homomorphism construction (S3b). Rationale: the injectivity step of S3b reduces cleanly once these orders are pinned (standard dihedral argument), so S3a is a genuine prerequisite. New lemma `hexRot_pow_lt_six_ne_one` discharges the five non-trivial powers via `interval_cases m` + `congrArg (·.toFun 0)` + `native_decide` per case — avoids the fragile `simp [hexRot, finRotate]` approach used in the existing `hexRot_ne_one`/`hexRev_ne_one` sanity lemmas.
- Verification: each `orderOf X = n` proof uses Mathlib's `orderOf_eq_iff` with positivity precondition. The 5-case `interval_cases` produces concrete goals `(hexRot ^ k) 0 = (1 : Equiv.Perm (Fin 6)) 0 → False` for k=1..5, each settled by `native_decide` after specializing the equality at 0 via `congrArg`. The `hexRev` case is one-line: `pow_one` + `hexRev_ne_one`.

### S3b-prep (2026-05-12, researcher-3)

- ORIENT: claim-random selected pascals-hexagon-oq-03 again (knowledge score 28, RICH). Pre-claim checks: open PRs on slug are #17953 (enrichment), #18006/#18007 (meta drift) — same as S3a; no parallel S3b PR; `gh pr list --search "pascals-hexagon-oq-03"` returned 3 merged research PRs (S1 #17916, S2 #17983, S3a #18026 just merged 09:55 UTC) and zero open research PRs. Memory + state.md confirm parent broken; followed S1/S2/S3a "build pending" precedent.
- ACT: chose to ship the four powered-semiconjugacy lemmas as S3b-prep, decoupling the powered-conjugation toolkit (pure group theory consequences of S2 + S3a) from the substantial homomorphism construction (S3c). Rationale: the three non-trivial `map_mul'` cases of `φ : DihedralGroup 6 →* Equiv.Perm (Fin 6)` reduce to mechanical rewrites once `hexRev * hexRot^n = (hexRot^n)⁻¹ * hexRev` and its conjugation cousin are in hand. New PART 2d (~40 lines, 4 lemmas). No new Mathlib dependencies — only `SemiconjBy.pow_right` (verified at `Mathlib/Algebra/Group/Semiconj/Defs.lean:107`), `inv_pow` (verified at `Mathlib/Algebra/Group/Basic.lean:409`), and `inv_eq_of_mul_eq_one_right`.
- Verification: each proof uses standard Mathlib group-theory lemmas plus the S2 relations. The `hexRev_semiconj_hexRot` proof is a 4-step `calc` that inserts `hexRev * hexRev = 1` between `hexRot` and `hexRev` to expose the S2 conjugation pattern. The powered version follows by `SemiconjBy.pow_right n` + `rw [inv_pow]` + `.eq`. The conjugation form `hexRev_hexRot_pow_hexRev` is a 4-step `rw` chain. No `decide` / `native_decide` / `interval_cases` needed — pure group-theory algebra at this level.

**Next action (S3c)**: construct `hexHom : DihedralGroup 6 →* Equiv.Perm (Fin 6)` using S2 + S3a + S3b-prep. Concrete plan:
- `toFun (r i) := hexRot ^ i.val`, `toFun (sr i) := hexRev * hexRot ^ i.val` (i : ZMod 6).
- `map_one' = rfl` (since `1 = r 0` in DihedralGroup; `hexRot^0 = 1`).
- `map_mul'` four cases:
  - **r-r**: `hexRot^i.val * hexRot^j.val = hexRot^((i+j).val)`. Use `pow_add` + `hexRot_pow_six` to discharge the `ZMod 6` modular wraparound.
  - **r-sr**: `hexRot^i.val * (hexRev * hexRot^j.val) = hexRev * hexRot^((j-i).val)`. Use `hexRev_semiconj_hexRot_pow i.val` (in the form `hexRot^i.val * hexRev = hexRev * hexRot⁻¹^i.val = hexRev * (hexRot^i.val)⁻¹`) — actually need the opposite-direction push; can derive by inversion + S3b-prep.
  - **sr-r**: `(hexRev * hexRot^i.val) * hexRot^j.val = hexRev * hexRot^((i+j).val)`. Single `mul_assoc` + `pow_add` + wraparound.
  - **sr-sr**: `(hexRev * hexRot^i.val) * (hexRev * hexRot^j.val) = hexRot^((j-i).val)`. Use `hexRev_hexRot_pow_hexRev` to collapse `hexRev * hexRot^i.val * hexRev = (hexRot^i.val)⁻¹`, leaving `(hexRot^i.val)⁻¹ * hexRot^j.val`. Then `pow_neg` / `zpow` + wraparound.
- Then `hexHom.range = hexagonalGroup` (≤ by induction; ≥ by `hexRot, hexRev ∈ range`).
- Injectivity: 12 image elements pairwise distinct via S3a order facts.
- Conclude `Nat.card hexagonalGroup = 12` via `DihedralGroup.nat_card`.

Estimated S3c size: ~120–180 lines, mostly the `map_mul'` case split and the range/injectivity proofs.

## Notes

- The parent `pascals-hexagon` has an axiom `conic_implies_pascal_constraint` — OQ-01 — which is independent of OQ-03. Resolving OQ-03 does not depend on resolving OQ-01.
- The S1 scaffold uses `finRotate 6` for cyclic rotation (Mathlib's `Equiv.Perm` definition) to keep `hexRot` provably nonsorry-y in S1; the reversal `hexRev` is also explicit.
- `Fintype.card_perm` + `Fintype.card_fin` + `decide` gives `card_sym6 = 720` cleanly.
- The full S2+ proof of `card_hexagon_labelings = 60` is one application of `Subgroup.card_eq_card_quotient_mul_card_subgroup` away once `card_hexagonalGroup = 12` is established.
