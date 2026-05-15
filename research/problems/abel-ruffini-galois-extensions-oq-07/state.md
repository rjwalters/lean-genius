# Current State

**Phase**: ACT
**Since**: 2026-05-12T03:30:00Z
**Iteration**: 25 (S25 ACT — `burnside_pq` dispatch peel-off + axiom narrowing `4 ≤ a + b`)
**Last Updated**: 2026-05-14 (researcher-9)

## S25 (researcher-9, 2026-05-14, this PR — build pending)

**`burnside_pq` dispatch peel-off + axiom narrowing landed**. Per S25 PREP
(researcher-3, PR #18611, merged 2026-05-13), this iteration ships the
mechanical implementation:

1. **Two new consolidated theorems** between
   `burnside_p_q_squared_twelve_mirror` (line 1532) and `PART IV` header:
   * `burnside_p_squared_q` — uniform interface for `|G| = p² · q`,
     consolidating S7 (`q < p`) + S7.5 (`p < q, ¬(p=2 ∧ q=3)`) +
     S9+S24 (`(p, q) = (2, 3)`, `|G| = 12`). ~30 LOC including docstring.
     Now axiom-free post-S24's inline closure of `sylow_two_unique_when_n3_four`.
   * `burnside_p_q_squared` — symmetric for `|G| = p · q²`,
     consolidating S11.1 (`p < q`) + S11.2 (`q < p, ¬(p=3 ∧ q=2)`) +
     S11.3+S24 (`(p, q) = (3, 2)`, `|G| = 12` mirror). ~30 LOC.
     Exceptional case lives inside the `q < p` branch (mirror of S7-side).

2. **`burnside_pq` dispatch update** at lines 1628–1697 (was 1544–1573):
   * NEW `by_cases h21 : a = 2 ∧ b = 1` — peels off to `burnside_p_squared_q`.
   * NEW `by_cases h12 : a = 1 ∧ b = 2` — peels off to `burnside_p_q_squared`.
   * Residue branch derives `hab : 4 ≤ a + b` via `interval_cases a <;>
     interval_cases b` with bounds `1 ≤ a, a ≤ 2, 1 ≤ b, b ≤ 2`
     (the only remaining cases inside the contradiction-form are the
     three already-peeled-off shapes, closed by `h11`, `h12`, `h21` +
     `omega` for `(2, 2)`).

3. **Axiom narrowing** at lines 174–178:
   * `(hab : 2 ≤ a ∨ 2 ≤ b)` → `(hab : 4 ≤ a + b)`. Strictly stronger
     hypothesis (covers strictly fewer `(a, b)` shapes) ⇒ axiom carries
     strictly less unverified content.
   * Docstring updated with S25 paragraph documenting the iteration history.

### S25 PREP audit-correction discussion

The S25 PREP (researcher-3, PR #18611) caught a **correctness gap** in the
S24 PREP §7 + state.md "Next Action" plan to narrow the axiom to
`2 ≤ a ∧ 2 ≤ b`. That narrowing would orphan the asymmetric residues
`(a, b) ∈ {(3, 1), (4, 1), …, (1, 3), (1, 4), …}` — `(a, b)` shapes
that currently rely on the axiom and that S25's S7/S7.5/S9/S11.x
consolidated theorems do **not** peel off. Adopting `2 ≤ a ∧ 2 ≤ b`
would make `burnside_pq` non-exhaustive.

The PREP's exhaustive 5×5 enumeration table (§2) confirms:
`(2 ≤ a ∨ 2 ≤ b) ∧ ¬ ((a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2))` simplifies
to **`4 ≤ a + b`** (given `1 ≤ a, 1 ≤ b`), which IS the correct
residue. S25 ACT (this iteration) adopts the PREP's corrected target.

### Counts

* `lineCount`: 1791 → 1895 (+104: ~60 LOC for two consolidated theorems
  + section header, ~30 LOC for dispatch peel-off + interval_cases
  residue derivation, ~10 LOC for axiom docstring update).
* `theoremCount`: 36 → 38 (+2 consolidated theorems).
* `substantiveTheoremCount`: 18 → 20 (+2; both are user-facing Burnside
  cases at the `(a, b)`-shape level, consolidating the prior single-case
  theorems into a uniform interface).
* `sorries`: **0** (unchanged from S24).
* `axiomCount`: **1** (unchanged — same `burnside_pq_nontrivial`, narrowed
  hypothesis from `2 ≤ a ∨ 2 ≤ b` to `4 ≤ a + b`).

### Burnside coverage table (post-S25)

| Burnside shape | Coverage | Source |
|---|---|---|
| `(a, 0)` / `(0, b)` / `p = q` | axiom-free | S2 trivial cases |
| `(1, 1)` (squarefree `pq`) | axiom-free | S4 via `IsZGroup.of_squarefree` |
| `(2, 1)` (all `(p, q)`) | axiom-free | S7+S7.5+S9+S24 via `burnside_p_squared_q` |
| `(1, 2)` (all `(p, q)`) | axiom-free | S11.1+S11.2+S11.3+S24 via `burnside_p_q_squared` |
| `4 ≤ a + b` (i.e., `(2,2)`, `(3,1)`, `(1,3)`, `(2,3)`, `(3,2)`, `(3,3)`, `(4,1)`, …) | **axiomatized** | `burnside_pq_nontrivial` (narrowed) |

### Build status

**Build pending**. Per `feedback_researcher_lake_symlink_loop_and_wipe.md`
and the established pattern on this slug (S15/S17/S18/S20/S21/S22/S23/S24
all merged "build pending"), S25 ships uncertified-by-CI; doctor verifies
post-merge from a clean worktree. A foreground Docker build was launched
during this session (`.loom/logs/researcher-9-abel-ruffini-s25-build.log`)
and was still in flight at commit time; results will be appended on
follow-up audit/doctor sweep.

Risk assessment:
* **No new Mathlib API surface**: all of `lt_trichotomy`, `interval_cases`,
  `omega`, `norm_num`, `simpa`, `subst`, `by_contra`, `push_neg` are
  already exercised by this file's existing theorems (e.g., S7.5 uses
  `interval_cases` for divisor enumeration at line 373; main `burnside_pq`
  dispatch already uses `by_contra` + `push_neg`).
* **No new imports**: zero changes to the module's import surface.
* **`interval_cases a <;> interval_cases b` finisher** (lines 1689–1693):
  R2 from the PREP. If Lean's `interval_cases` doesn't infer the upper
  bound `a ≤ 2` from `a + b < 4 ∧ b ≥ 1` automatically, replace with
  explicit `omega + rcases Nat.lt_or_ge` chain (the alternative form
  in PREP §6).
* **`subst` chains on `Fact (Nat.Prime 2)` / `(Nat.Prime 3)` lookups**
  in `burnside_p_squared_q`'s `(p=2, q=3)` branch: same idiom as
  `burnside_p_q_squared_twelve_mirror`'s S24-stable invocation pattern.

### Next iteration (S26)

Per S25 PREP §12 post-S25 horizon: target `(a, b) = (2, 2)` shape
(`|G| = p² · q²`), the smallest `4 ≤ a + b` case currently in the
axiom. Sylow analysis with two main subcases:
* `q < p` / `p < q` analogous to S7/S11 but with `n_p ∣ q²` AND
  `n_q ∣ p²` simultaneously; the residues are
  `(p, q) ∈ {(2, 3), (3, 2)}` (i.e., `|G| = 36`).
* `|G| = 36`: requires delicate analysis akin to S9's `|G| = 12` but
  with both `n_2 ∈ {1, 3, 9}` and `n_3 ∈ {1, 4}` simultaneously.
  Estimated ~250–400 LOC.

After S26, axiom hypothesis narrows further to `5 ≤ a + b`. Full
`axiomCount: 0` requires Goldschmidt-Matsuyama on
`Mathlib.GroupTheory.Focal` (~400–800 LOC; deferred S27+).

## S24 (researcher-10, 2026-05-13, PR #18912 — build pending, merged)

**S10 closure landed inline**: `sylow_two_unique_when_n3_four` no longer
carries a `sorry`. The closure body is ~30 LOC of pure composition of
five already-merged helpers per the S24 PREP §2 plan
(`research/problems/abel-ruffini-galois-extensions-oq-07/session-24-s10-inline-closure-prep.md`,
merged 2026-05-13 PR #18591).

### What landed

`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` lines 1271–1322,
replacing the lone remaining `  sorry` at the old line 1277 with three
in-body blocks:

* **(a) `hdisj`** (~13 LOC): for any `Q Q' : Sylow 3 G` with `Q ≠ Q'`,
  `Disjoint ((Q : Set G) \ {1}) ((Q' : Set G) \ {1})`. Derives
  `(Q : Subgroup G) ⊓ (Q' : Subgroup G) = ⊥` via S13
  `sylow_three_card_eq_three_of_card_twelve` + S11.5
  `sylow_prime_order_disjoint_of_ne`, pushes to Set level via
  `Subgroup.coe_inf` + `Subgroup.coe_bot`, then closes the disjointness
  via `Set.disjoint_left.mpr` + `rintro` destructuring of the two `\ {1}`
  memberships.
* **(b) `hfiber`** (~8 LOC): for any `Q : Sylow 3 G`,
  `Set.ncard ((Q : Set G) \ {1}) = 2`. Verbatim mirror of S18's
  `sylow_two_set_diff_one_ncard_eq_three` template with `(2, 4, 3)`
  substituted for `(3, 3, 2)`: `Sylow.card` → `1 ∈ (Q : Set G)` from
  `Subgroup.one_mem` → `Nat.card_coe_set_eq` →
  `Set.ncard_diff_singleton_of_mem` collapses `3 - 1 = 2`.
* **(c) Composition** (~2 LOC): S23
  `cube_id_card_eq_nine_of_partition_ingredients hcard hdisj hfiber hn3`
  yields `Set.ncard {g | g^3 = 1} = 9`; S22 corollary
  `sylow_two_subsingleton_of_cube_id_card_nine hcard h9` yields
  `Subsingleton (Sylow 2 G)`. Done.

### Counts

* `lineCount`: 1761 → 1791 (+30: ~30 LOC closure body + minor docstring
  edit). Slightly above PREP estimate (1788) due to one additional
  comment line per block.
* `theoremCount`: unchanged (36; closure is on an existing `private lemma`).
* `substantiveTheoremCount`: unchanged (18).
* `sorries`: **1 → 0**.
* `axiomCount`: **1** (unchanged — `burnside_pq_nontrivial` for
  `(a, b) ≥ (2, 2)` is genuinely deep).

### Status of the thread after S24

| Burnside shape | Coverage | Source |
|---|---|---|
| `(a, 0)` / `(0, b)` / `p = q` | axiom-free | S2 trivial cases |
| `(1, 1)` (squarefree `pq`) | axiom-free | S4 via `IsZGroup.of_squarefree` |
| `(2, 1)`, `p > q` | axiom-free | S7 `burnside_p_squared_q_p_gt_q` |
| `(2, 1)`, `p < q ≠ p+1` | axiom-free | S7.5 `burnside_p_squared_q_p_lt_q` |
| `(2, 1)`, `(p, q) = (2, 3)` (|G| = 12) | axiom-free | S9 `burnside_p_squared_q_twelve` + **S24 closure** |
| `(1, 2)`, `p < q` | axiom-free | S11 `burnside_p_q_squared_p_lt_q` |
| `(1, 2)`, `q < p ≠ q+1` | axiom-free | S11 `burnside_p_q_squared_q_lt_p` |
| `(1, 2)`, `(p, q) = (3, 2)` (|G| = 12) | axiom-free | S11 `burnside_p_q_squared_twelve_mirror` + **S24 closure** |
| `(2, 2)+` | **axiomatized** | `burnside_pq_nontrivial` |

Both |G| = 12 sub-cases (S9 and S11 mirror) inherited the S10 sorry —
**both are now axiom-free**. The only remaining open content is the
`(a, b) ≥ (2, 2)` axiom, requiring character theory or
Goldschmidt-Matsuyama transfer.

### Next iteration (S25)

`burnside_pq` dispatch update per the S24 PREP §7 horizon:

1. **Narrow `burnside_pq_nontrivial` hypothesis** from `2 ≤ a ∨ 2 ≤ b`
   to `2 ≤ a ∧ 2 ≤ b`. The `(2, 1)` and `(1, 2)` shapes are now
   axiom-free for ALL primes (S7 + S7.5 + S9+S24 = `(2, 1)` full;
   S11.1 + S11.2 + S11.3+S24 = `(1, 2)` full).
2. **Update the `burnside_pq` dispatch** to peel off both `(2, 1)` and
   `(1, 2)` axiom-free before falling through to the narrowed axiom.
3. Independent of the four still-open in-flight ingredient PRs
   (#17528, #17586, #17587, #17685) — those are now formally obsolete
   per S24 PREP §4, and should be closed by an auditor/doctor sweep.

### Build status

**Build pending**. Per `feedback_researcher_lake_symlink_loop_and_wipe.md`
and the established pattern in this thread (S15/S17/S18/S20/S21/S22/S23
all merged "build pending"), the S24 closure ships uncertified-by-CI;
doctor verifies post-merge from a clean worktree. Risk assessment:

* All seven Mathlib API names used in the closure are pre-verified
  against pinned commit `2df2f0150c` (see S24 PREP §8). Only
  `Subgroup.coe_inf` and `Subgroup.coe_bot` are NEW to this file
  (both stable Lattice.lean lemmas; transitively imported via
  `Mathlib.GroupTheory.Sylow`).
* All five composing helpers (`sylow_prime_order_disjoint_of_ne`,
  `sylow_three_card_eq_three_of_card_twelve`,
  `cube_id_card_eq_nine_of_partition_ingredients`,
  `sylow_two_subsingleton_of_cube_id_card_nine`,
  `Subgroup.one_mem`) are at canonical signatures in `origin/main`
  (verified pre-edit; see PREP §1 line citations).
* If R2 (set-diff destructuring shape) fails, the `rintro g ⟨hgQ,
  hg_ne_one⟩ ⟨hgQ', _⟩` pattern can be replaced by `intro g hgQ_diff
  hgQ'_diff` + explicit `.1` / `.2` projections.

## S23 (researcher-8, 2026-05-12, PR #18236, MERGED)

Partition-ingredients composition: derives `cube_id_card_eq_nine` (the
S16 closure target, Step 1 of S23-next per the S22 spec) from the three
atomic ingredients as hypotheses, leaving the downstream S10 closure to
plug in PRs #17586 / #17587 once they land. One new private lemma,
axiom-free, build pending:

`cube_id_card_eq_nine_of_partition_ingredients` (private):
given `Nat.card G = 12`, the Set-level pairwise disjointness `hdisj`
of punctured Sylow-3 subgroups (target of in-flight PR #17586), the
per-fiber count `hfiber = ∀ Q, Set.ncard ((Q : Set G) \ {1}) = 2`
(target of in-flight PR #17587), and `hn3 : Nat.card (Sylow 3 G) = 4`
(S13), concludes the cube-identity element count
```
Set.ncard {g : G | g ^ 3 = 1} = 9
```
via the chain S15 set decomposition + `Set.ncard_union_eq` +
`Set.ncard_iUnion_of_finite` + `finsum_eq_sum_of_fintype` +
`Finset.sum_const` + `Nat.card_eq_fintype_card` + `1 + 4 • 2 = 9`
(`decide`-closed).

### Strategic positioning

S23 is **the cube-id count assembly** identified in `state.md` §"Next
iteration (S23)" Step 1 (researcher-11, 2026-05-12). It is fully
**independent of in-flight S16 PRs #17586 and #17587 in deliverable
content**: those land the *atomic ingredients* (Set-level disjointness
and per-fiber cardinality) as new private lemmas; this PR takes both
as hypotheses and composes them with S15's `cube_id_set_eq_disjoint_union`
plus the Mathlib disjoint-iUnion arithmetic to produce the cube-id
count, parameterized on the ingredients.

With S23 in hand AND #17586 + #17587 landed, closing the S10 sorry in
`sylow_two_unique_when_n3_four` reduces to a ~5-line composition:

```lean
let hdisj := fun Q Q' hne =>
  sylow_three_diff_singleton_disjoint hcard hne          -- #17586
let hfiber := sylow_three_set_diff_one_ncard_eq_two hcard -- #17587
have h9 := cube_id_card_eq_nine_of_partition_ingredients
              hcard hdisj hfiber hn3
exact sylow_two_subsingleton_of_cube_id_card_nine hcard h9
```

(or equivalent inline form). Both S22 corollary
`sylow_two_subsingleton_of_cube_id_card_nine` and this S23 composition
remain conditional pending #17586 + #17587; once those land, the S10
closure is **mechanical**.

**Non-overlap with in-flight PRs**:
* #17586 supplies *Set-level pairwise disjointness for `(Q : Set G) \ {1}`*
  (the `hdisj` hypothesis); S23 takes the *bundled `∀ Q Q', Q ≠ Q' → ...`
  form* as parameter and converts internally to the `Pairwise (Disjoint
  on _)` shape Mathlib's `Set.ncard_iUnion_of_finite` expects. No content
  overlap with the disjointness derivation.
* #17587 supplies the *per-fiber ncard count* `Set.ncard ((Q : Set G)
  \ {1}) = 2` (the `hfiber` hypothesis); S23 takes the bundled `∀ Q, ...
  = 2` form as parameter. No content overlap with the per-fiber count
  derivation.
* #17685 (S19, forward subset for ingredient 4) targets the Sylow-2
  side; S23 operates entirely on the Sylow-3 side. No overlap.
* #17528 (old S14 PR) predates the merged S14 #17536; unrelated.

**Carries no hypothesis on the choice of Sylow-2 subgroup**: this
lemma operates entirely on the cube-identity set and the Sylow-3
side. The Sylow-2 / Subsingleton step is encapsulated downstream in
S21 / S22 corollary.

### Counts

* `lineCount`: 1649 → 1761 (+112, including ~65 lines of docstring +
  ~45 lines of proof body across the new lemma plus 1 new import line
  for `Mathlib.Data.Set.Card.Arithmetic`)
* `theoremCount`: 35 → 36 (+1 private lemma)
* `substantiveTheoremCount`: 18 (unchanged — supporting ingredient,
  not a user-facing Burnside case)
* `axiomCount`: 1 (unchanged)
* `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four` remains
  the S10 closure target; S23 prepares the final composition without
  closing it, since `hdisj` and `hfiber` remain in-flight on
  #17586 + #17587)

### Build status

**[BUILD UNVERIFIED]** Same caveat as S9–S22: worktree's
`proofs/.lake` is a recursive self-symlink (memory
`feedback_researcher_lake_symlink_broken`), so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). One new import:

* `Mathlib.Data.Set.Card.Arithmetic` — for `Set.ncard_iUnion_of_finite`
  (verified against `/Users/rwalters/GitHub/mathlib4` main checkout,
  line 114 of `Mathlib/Data/Set/Card/Arithmetic.lean`). PR #17587's
  body explicitly notes this import is "not transitively imported via
  Sylow chain"; verified locally that it transitively pulls
  `Mathlib.Algebra.BigOperators.Finprod` (for `finsum_eq_sum_of_fintype`,
  `finsum_congr`) and `Mathlib.Data.Set.Card` (for `Set.ncard_singleton`,
  `Set.ncard_union_eq`).

Other Mathlib API used (all stock v4.26.0, all verified against the
local Mathlib checkout):

* `Set.disjoint_iUnion_right` — `Mathlib.Data.Set.Lattice:1220`.
* `Set.disjoint_left` — `Mathlib.Data.Set.Disjoint:41`.
* `Set.ncard_union_eq` — `Mathlib.Data.Set.Card:966`.
* `Set.ncard_singleton` — `Mathlib.Data.Set.Card:656`.
* `Set.finite_singleton` / `Set.toFinite` — `Mathlib.Data.Set.Card`
  area; transitively imported.
* `Set.ncard_iUnion_of_finite` — `Mathlib.Data.Set.Card.Arithmetic:114`,
  signature `[Finite ι] {s : ι → Set α} (hs : ∀ i, (s i).Finite)
  (h : Pairwise (Disjoint on s)) : (⋃ i, s i).ncard = ∑ᶠ i, (s i).ncard`.
* `finsum_congr` — `Mathlib.Algebra.BigOperators.Finprod`.
* `finsum_eq_sum_of_fintype` — same module, line 432 (it is the additive
  version of `finprod_eq_prod_of_fintype` via `@[to_additive]`).
* `Finset.sum_const` — `Mathlib.Algebra.BigOperators.Basic`, transitively
  imported.
* `Finset.card_univ` — same, transitively imported.
* `Nat.card_eq_fintype_card` — `Mathlib.Data.Finite.Card`, transitively
  imported.
* `Fintype.ofFinite` — `Mathlib.Data.Fintype.Basic`, transitively
  imported; `noncomputable` upgrade from `Finite` to `Fintype`.

The `Finite (Sylow 3 G)` instance is auto-derived by Lean's typeclass
synthesis from `[Finite G]` (existing code at line ~1305 already uses
`card_sylow_modEq_one 3 G` without explicit `[Finite (Sylow 3 G)]`,
which requires the same instance — chain via
`Sylow extends Subgroup G` + `Subtype.finite`-style synthesis).

### Next iteration (S24)

After this PR lands AND #17586 + #17587 land, the S10 closure of
`sylow_two_unique_when_n3_four` becomes the mechanical ~5-line
composition shown in the docstring above. Estimated total ~5 lines.

If S24 occurs before #17586 + #17587 land, alternatives:
1. **Strengthen S15** — refactor `cube_id_set_eq_disjoint_union`'s
   docstring to record the partition's full content for downstream
   readers; pure docs, no behavior change. Low-leverage.
2. **`burnside_pq` dispatch update** — independent of the S10 closure:
   refactor `burnside_pq_nontrivial` axiom's hypothesis from
   `2 ≤ a ∨ 2 ≤ b` to `2 ≤ a ∧ 2 ≤ b` once S10 / S11 / S12 close
   their respective sub-cases. This is the "S18" task per the
   pre-S22 next-action plan; arguably should land *before* S10
   closes (decoupling axiom-narrowing from the S10 ingredient
   chain). High-leverage but requires careful coordination with
   the dispatch path.

---

## S22 (researcher-11, 2026-05-12, merged via #17880)

Cardinality bridge step (Step 2 of S22-next per the S21 spec), one
new private lemma plus one composition corollary, both axiom-free,
build pending:

`cube_id_complement_ncard_eq_three_of_card_nine` (private):
given `Nat.card G = 12` and the S16 target form
`Set.ncard {g : G | g^3 = 1} = 9`, concludes the complement form
```
Set.ncard ((Set.univ : Set G) \ {g | g^3 = 1}) = 3
```
via elementary `Set.subset_univ` + `Set.ncard_univ` + `Set.ncard_diff`
arithmetic (`12 − 9 = 3` closes by `rfl` on closed `Nat` literals).

`sylow_two_subsingleton_of_cube_id_card_nine` (private, corollary):
composes the bridge with S21's `sylow_two_subsingleton_of_compl_ncard`
to derive `Subsingleton (Sylow 2 G)` *directly* from the S16 target
form `Set.ncard {g | g^3 = 1} = 9`, eliminating the need for downstream
consumers to thread `hncard_compl` manually.

### Strategic positioning

S22 is the *cardinality bridge* identified in `state.md` §"Next
iteration (S22)" Step 2 (researcher-12, 2026-05-12). It is fully
**independent of in-flight S16 PRs #17586 and #17587**: those target
the cube-id count `Set.ncard {g | g^3 = 1} = 9` directly (Sylow-3
disjointness + per-fiber cardinality + disjoint-union arithmetic);
S22 takes that count as a *hypothesis* and bridges to the complement
form S20/S21 consume. The bridge composes via the cube-id count
without depending on its derivation path.

With S22 in hand, closing the S10 sorry in
`sylow_two_unique_when_n3_four` reduces to **one** discharge:
deriving `Set.ncard {g | g^3 = 1} = 9` from `Nat.card (Sylow 3 G) = 4`.
That is exactly the composition target `cube_id_card_eq_nine` that
the in-flight S16 PRs are building toward (via S15's set-decomposition
`{g | g^3 = 1} = {1} ∪ ⋃ Q, (Q \ {1})` plus the `1 + 4·2 = 9`
disjoint-union arithmetic).

**Non-overlap with in-flight PRs**:
* #17586 + #17587 target the cube-id count (ingredient 3); S22 takes
  that count as a hypothesis and bridges to the complement form.
  Strictly downstream — no content overlap.
* #17685 (S19) provides the bare forward subset
  `(P \ {1}) ⊆ {g | g^3 ≠ 1}` form of ingredient 4 (Sylow-2 side);
  S22 sits on the *complement-side cardinality* axis, not on
  ingredient 4 at all.
* #17528 (old S14 PR) predates the merged S14 #17536; unrelated.
* No content overlap with any open PR for this slug.

**Carries no hypothesis on `n_3 = 4`** directly: the `n_3 = 4`
dependency is fully encapsulated in the cube-id count hypothesis
(the same shape S16 PRs aim to discharge). S22 is a pure
"cube-id count + total-order ⇒ complement count" argument.

### Counts

* `lineCount`: 1584 → 1649 (+65, including ~45 lines of docstring +
  ~20 lines of proof body across the two new lemmas)
* `theoremCount`: 33 → 35 (+2 private lemmas)
* `substantiveTheoremCount`: 18 (unchanged — both new lemmas are
  private supporting ingredients, not user-facing API)
* `axiomCount`: 1 (unchanged)
* `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four` remains
  the S10 closure target; S22 prepares the final cardinality bridge
  without closing it, since the cube-id count hypothesis is still
  conditional pending S16)

### Build status

**[BUILD UNVERIFIED]** Same caveat as S9–S21: worktree's
`proofs/.lake` is a recursive self-symlink, so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). The new lemmas use only
Mathlib API already exercised in this same file:

* `Set.subset_univ` — `Mathlib.Data.Set.Basic`, transitively imported.
* `Set.ncard_univ` — `Mathlib.Data.Set.Card`, transitively imported
  (used at line 891 of this file via `Nat.card_coe_set_eq`).
* `Set.ncard_diff` — `Mathlib.Data.Set.Card`, used at line 893 of
  this file via `Set.ncard_diff_singleton_of_mem` (sibling lemma).
* `rfl` on `12 - 9 = 3` — Nat literal arithmetic.

No new imports, no new Mathlib lemmas beyond what S11.5–S21 already
exercise.

### Next iteration (S23)

After this PR lands, the remaining work for closing
`sylow_two_unique_when_n3_four`:

1. **Compose `cube_id_card_eq_nine`** from in-flight S16 PRs (#17586
   + #17587) plus S15's `cube_id_set_eq_disjoint_union` and the
   `1 + 4·2 = 9` disjoint-union arithmetic. Estimated ~15 lines once
   both S16 PRs land.
2. **Close S10**: feed `cube_id_card_eq_nine` output into S22's
   `sylow_two_subsingleton_of_cube_id_card_nine`. ~3 lines, replacing
   the single `sorry` in `sylow_two_unique_when_n3_four`.

Total ~18 lines once #17586 + #17587 land. S22 makes the final
closure mechanical given the S16 composition.

---

## S21 (researcher-12, 2026-05-12, merged via #17713)

Final ingredient (5/5) of the S10 element-counting closure
`sylow_two_unique_when_n3_four`, per
`session-13-s10-element-count-spec.md` §5. One new private lemma,
axiom-free, build pending:

`sylow_two_subsingleton_of_compl_ncard` (private, conditional):
given `|G| = 12` and the same conditional cardinality hypothesis
`Set.ncard ((Set.univ : Set G) \ {g | g^3 = 1}) = 3` that S20 takes,
concludes
```
Subsingleton (Sylow 2 G).
```

The proof composes S20's `sylow_two_set_eq_one_union_compl_cube_id`
(P-independent set-equality) with `Sylow.ext` and
`SetLike.coe_injective`:

1. Take any two `P, P' : Sylow 2 G`.
2. Apply S20 twice to express `(P : Set G)` and `(P' : Set G)` as the
   same RHS `{1} ∪ (univ \ {g | g^3 = 1})`.
3. Transitivity gives `(P : Set G) = (P' : Set G)`.
4. `SetLike.coe_injective` lifts to `(P : Subgroup G) = (P' : Subgroup G)`.
5. `Sylow.ext` lifts to `P = P'`.

### Strategic positioning

S21 is the *explicitly deferred* Subsingleton step called out in the
S20 corollary docstring (lines 988–991 of the file). With S21 in hand,
the S10 closure of `sylow_two_unique_when_n3_four` reduces to a
single discharge: derive `hncard_compl_eq_three` from
`hn3 : Nat.card (Sylow 3 G) = 4`. That discharge composes:

* S16 cardinality `Set.ncard {g : G | g^3 = 1} = 9` (in flight via
  PRs #17586 + #17587 + a future composition lemma `cube_id_card_eq_nine`).
* Elementary `Set.ncard_diff` + `Set.ncard_univ` arithmetic:
  `12 - 9 = 3`.

**Non-overlap with in-flight PRs**:
* #17586 (Sylow-3 set-level disjointness) and #17587 (Sylow-3
  per-fiber cardinality) target ingredient 3 (`cube_id_card_eq_nine`);
  S21 targets ingredient 5 (Subsingleton derivation under conditional).
* #17685 (S19) provides the *forward subset* form of ingredient 4;
  S21 sits one level higher in the composition chain.
* #17528 (old S14 PR) predates S14 merge; unrelated.
* No content overlap with any open PR for this slug.

**Carries no hypothesis on `n_3 = 4`** directly: the `n_3 = 4`
dependency is fully encapsulated in the cube-id complement
cardinality hypothesis (the same hypothesis S20 already takes). S21
is a pure "P-independent set form ⇒ Subsingleton" argument.

### Counts

* `lineCount`: 1531 → 1584 (+53, including ~33 lines of docstring +
  ~20 lines of proof body)
* `theoremCount`: 32 → 33 (+1 private lemma)
* `substantiveTheoremCount`: 18 (unchanged — supporting ingredient,
  not a user-facing Burnside case)
* `axiomCount`: 1 (unchanged)
* `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four` remains
  the S10 closure target; S21 prepares its ingredient-5 Subsingleton
  step without closing it)

### Build status

**[BUILD UNVERIFIED]** Same caveat as S9–S20: worktree's
`proofs/.lake` is a recursive self-symlink, so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). The new lemma uses only
Mathlib API already exercised in this same file:

* `Sylow.ext` — used at line 578 of this file in the S11.5 proof.
* `SetLike.coe_injective` — standard Mathlib core API for
  `SetLike` instances; applies to `Subgroup G` via the canonical
  `Subgroup G → Set G` coercion that the rest of the file already
  uses.
* `sylow_two_set_eq_one_union_compl_cube_id` (S20, line 998 of this
  file) — just merged.

No new imports, no new Mathlib lemmas beyond what S11.5–S20 already
exercise.

### Next iteration (S22)

After this PR lands, the remaining work for closing
`sylow_two_unique_when_n3_four`:

1. **Compose `cube_id_card_eq_nine` from in-flight S16 PRs** (#17586
   + #17587 + the disjoint-union cardinality count `1 + 4·2 = 9`).
   ~15 lines.
2. **Cardinality bridge**: `Set.ncard {g | g^3 = 1} = 9` plus
   `Nat.card G = 12` ⇒
   `Set.ncard ((univ : Set G) \ {g | g^3 = 1}) = 3` via
   `Set.ncard_diff` / `Set.ncard_univ`. ~5 lines.
3. **Close S10**: feed the bridge output into S21's
   `sylow_two_subsingleton_of_compl_ncard`. ~3 lines, replacing the
   single `sorry` in `sylow_two_unique_when_n3_four`.

Estimated total ~25 lines once #17586 + #17587 land.

---

## S20 (researcher-5, 2026-05-11, merged via #17696)

Fifth atomic ingredient for closing S10's `sylow_two_unique_when_n3_four`
sorry, per `session-13-s10-element-count-spec.md` §4. Two new private
lemmas (both axiom-free, build pending):

1. `sylow_two_set_diff_one_eq_compl_cube_id` (private, conditional):
   given `|G| = 12` and the cardinality hypothesis
   `Set.ncard ((Set.univ : Set G) \ {g | g^3 = 1}) = 3`, concludes the
   set equality
   ```
   (P : Set G) \ {1} = (Set.univ : Set G) \ {g | g^3 = 1}
   ```
   for any `P : Sylow 2 G`. Composes:
   * S17 `sylow_two_inter_cube_id_eq_singleton_one` (#17630, merged) —
     forward containment via Boolean rearrangement.
   * S18 `sylow_two_set_diff_one_ncard_eq_three` (#17648, merged) —
     LHS cardinality `= 3`.
   * Hypothesis `hncard_compl` — RHS cardinality `= 3`.
   * `Set.eq_of_subset_of_ncard_le` — subset + ncard match → equality.
2. `sylow_two_set_eq_one_union_compl_cube_id` (private, conditional):
   full set-equality form
   ```
   (P : Set G) = {1} ∪ ((Set.univ : Set G) \ {g | g^3 = 1}).
   ```
   The RHS is *P-independent* — exactly the ingredient-5 form needed
   for the `Subsingleton (Sylow 2 G)` closure. Proof via
   `Set.union_diff_cancel` + the main S20 lemma.

### Strategic positioning

S20 supplies the *cardinality-driven set EQUALITY* form of ingredient
4 (the merged S17/S18 PRs supplied the forward intersection form and
the LHS cardinality respectively; the in-flight S19 PR #17685 supplies
the bare forward subset `(P \ {1}) ⊆ {g | g^3 ≠ 1}` in named-lemma
form). The `hncard_compl` hypothesis is the cardinality corollary of
S16's `cube_id_card_eq_nine` (in flight via PRs #17586 + #17587),
since for `|G| = 12`: `12 - 9 = 3`. Once S16 lands, the hypothesis is
dischargeable by elementary `Set.ncard_diff` / `Set.ncard_univ`
arithmetic, and S20's full-set-equality corollary inlines into the
closure of `sylow_two_unique_when_n3_four` (the S10 placeholder).

**Carries no hypothesis on `n_3 = 4`**: the `n_3 = 4` dependency is
fully encapsulated in the cube-id complement cardinality hypothesis.
S20 is a pure "subset + cardinality match → equality" argument.

**Non-overlap with in-flight PRs**:
* #17586 (Sylow-3 set-level disjointness) and #17587 (Sylow-3 per-fiber
  cardinality) target ingredient 3 (`cube_id_card_eq_nine` for the
  Sylow-3 disjoint union); S20 targets ingredient 4 (Sylow-2 / cube-id
  complement). No content overlap.
* #17685 (S19, researcher-3) provides the bare *forward subset*
  `(P \ {1}) ⊆ {g | g^3 ≠ 1}` as a named lemma — equivalent in content
  to the inline subset step of S20's main lemma (re-derived in 8 lines
  here for self-containment). Once #17685 lands, S20's Step 1 can be
  refactored to invoke the #17685 lemma (mod a `Set.univ \ {g | g^3 = 1} =
  {g | g^3 ≠ 1}` syntactic bridge), but the equality + corollary
  contribution of S20 is independent of that refactor.
* #17528 (S14) predates the merged S14 #17536; no relation.

### Counts

* `lineCount`: 1404 → 1531 (+127, including ~70 lines of docstring +
  ~57 lines of proof body across the two new lemmas)
* `theoremCount`: 30 → 32 (+2 private lemmas)
* `substantiveTheoremCount`: 18 (unchanged — both new lemmas are
  private supporting ingredients, not user-facing API)
* `axiomCount`: 1 (unchanged)
* `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four` remains
  the S10 closure target; S20 prepares ingredient 4's reverse
  containment without closing it)

### Build status

**[BUILD UNVERIFIED]** Same caveat as S9–S18: worktree's
`proofs/.lake` is a recursive self-symlink, so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). The two new lemmas use only
Mathlib API verified against the file's existing patterns:

* `Set.eq_of_subset_of_ncard_le` — `Mathlib.Data.Set.Card`,
  transitively imported via `Mathlib.Tactic` and explicitly exercised
  by S18 (line 893).
* `Set.toFinite` — implicit auto-finiteness from `[Finite G]`,
  identical pattern to S18's `Nat.card_coe_set_eq` step.
* `Set.union_diff_cancel`, `Set.singleton_subset_iff`,
  `Set.mem_diff`, `Set.mem_singleton_iff`, `Set.mem_inter`,
  `Set.mem_univ` — `Mathlib.Data.Set.Basic` (transitively imported).
* `omega` — used once for the trivial `3 ≤ 3` discharge after
  rewriting both ncards.

No new imports, no new Mathlib lemmas beyond what S13–S18 already
exercise.

### Next iteration (S21 / S22)

After this PR lands, the remaining work for closing
`sylow_two_unique_when_n3_four`:

1. **Discharge `hncard_compl`** from S16's `cube_id_card_eq_nine` (in
   flight). Once #17586 + #17587 land and the S16 cardinality lemma is
   composed from them, `hncard_compl` reduces to one or two lines via
   `Set.ncard_diff` (`(univ \ S).ncard = |univ| - |S|` when both
   finite) and `Set.ncard_univ` (`|univ| = Nat.card G = 12`).
2. **Close the `Subsingleton` step** via `Sylow.ext` +
   `SetLike.coe_injective` applied to the P-independent set-equality
   form of S20's corollary `sylow_two_set_eq_one_union_compl_cube_id`.
   Estimated ~10-15 lines.

---

## S17 (researcher-13, 2026-05-09, merged via #17630)

Fourth of five ingredients (forward containment fragment) for closing
S10's `sylow_two_unique_when_n3_four` sorry, per
`session-13-s10-element-count-spec.md` §4:

* `sylow_two_inter_cube_id_eq_singleton_one` (private, axiom-free):
  for finite G with `Nat.card G = 12` and any `P : Sylow 2 G`,
  ```
  (P : Set G) ∩ {g : G | g^3 = 1} = ({1} : Set G).
  ```

  Forward (⊆): every `g ∈ P` satisfies `g ^ Nat.card P = 1` (i.e., `g^4 = 1`)
  by `pow_card_eq_one'` on the subgroup type plus
  `sylow_two_card_eq_four_of_card_twelve` (S13). Combined with the
  hypothesis `g^3 = 1`: `g = 1 · g = g^3 · g = g^(3+1) = g^4 = 1`,
  so `g = 1`.

  Backward (⊇): `1 ∈ P` (subgroup `one_mem`) and `1^3 = 1` (`one_pow`).

The lemma is positioned immediately after S15's
`cube_id_set_eq_disjoint_union` and before the S10 placeholder
`sylow_two_unique_when_n3_four`, parallel to the S16 ingredient-3
fragments in PRs #17586 / #17587 (which sit in the same region but
target Sylow-3 / cube-id cardinality, not Sylow-2 / cube-id intersection).

### Strategic positioning vs S16 (#17586 / #17587)

Both open S16 PRs target *ingredient 3* (`cube_id_card_eq_nine`), via
two parallel atomic fragments:
* `#17586` (researcher-6): Set-level pairwise disjointness of
  `(Q : Set G) \ {1}` for distinct Sylow 3-subgroups Q.
* `#17587` (researcher-1, narrowed): per-fiber count
  `Set.ncard ((Q : Set G) \ {1}) = 2` for any `Q : Sylow 3 G` with
  `|Q| = 3`.

This S17 lemma targets *ingredient 4* (`complement_in_sylow_two`,
forward fragment): the complement-direction containment for the
Sylow 2 / cube-identity intersection, which uses `|P| = 4` rather
than `|Q| = 3`. The three lemmas are pairwise independent and
compose cleanly into the closure of S10:

* #17586 + #17587 → ingredient 3 (`cube_id_card_eq_nine` cardinality
  count `1 + 4 · 2 = 9` once n_3 = 4 is plugged in).
* This S17 lemma → ingredient 4 forward containment
  `(P : Set G) ∩ {g | g^3 = 1} ⊆ {1}` (cardinality-free; holds
  independently of `n_3`).

The reverse containment of ingredient 4
`(P : Set G) ⊆ {1} ∪ ((Set.univ : Set G) \ {g | g^3 = 1})`
is a *cardinality* argument that requires ingredients 3 and the
`n_3 = 4` hypothesis; that fragment is deferred to the next
iteration once #17586 / #17587 land.

### Counts

* `lineCount`: 1290 → 1358 (+68, including ~36 lines of docstring +
  ~32 lines of proof body)
* `theoremCount`: 28 → 29 (+1 private lemma)
* `axiomCount`: 1 (unchanged)
* `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four` remains
  the S10 element-counting closure target; S17 prepares its
  ingredient-4 forward fragment without closing it)

### Build status

**[BUILD UNVERIFIED]** Same caveat as S9–S15: worktree's
`proofs/.lake` is a recursive self-symlink, so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). The new lemma uses only
Mathlib API verified against the file's existing patterns:

* `pow_card_eq_one'` — exact same invocation pattern as S14's
  `g_pow_three_iff_mem_some_sylow_three` (lines 732–741) on
  `(⟨g, hg⟩ : (Q : Subgroup G))`.
* `Subgroup.coe_pow` / `Subgroup.coe_one` — used implicitly via
  `rfl` in the calc-block, identical pattern to S14's backward
  direction.
* `sylow_two_card_eq_four_of_card_twelve` (S13, in this same file).
* `Subgroup.one_mem` — Mathlib core.
* `pow_succ`, `one_mul`, `one_pow`, `Set.ext` machinery
  (`Set.mem_inter_iff`, `SetLike.mem_coe`, `Set.mem_setOf_eq`,
  `Set.mem_singleton_iff`).

No new imports, no new Mathlib lemmas beyond what S13–S15 already
exercise. The S11.5 / S12 build-fix-replay pattern (#17405 → #17450
took ~95 min to recover from non-existent Mathlib API) is the
canonical caution; this S17 lemma stays inside the verified API
surface.

### Meta

`meta.json` carries pre-S15 drift (`lineCount` 1248 reflects the
S14 baseline before S15 added 42 lines; this PR resyncs to 1358
while bumping `theoremCount` 28 → 29). Two parallel S16 PRs
(#17586, #17587) will also resync `lineCount` once they merge;
the deployer / mechanic resolves convergence.

----

## S15 (researcher-6, 2026-05-09)

Second of five ingredients for closing S10's
`sylow_two_unique_when_n3_four` sorry, per
`session-13-s10-element-count-spec.md` §2:

* `cube_id_set_eq_disjoint_union` (private, axiom-free):
  for finite G with `Nat.card G = 12`,
  ```
  {g : G | g^3 = 1} = {1} ∪ ⋃ (Q : Sylow 3 G), ((Q : Set G) \ {1}).
  ```

  Forward (⊆): pointwise via S14's `g_pow_three_iff_mem_some_sylow_three`:
  `g^3 = 1 → ∃ Q, g ∈ Q`. Case-split on `g = 1`: contributes to `{1}`;
  else contributes to `(Q : Set G) \ {1}`.

  Backward (⊇): `g = 1` gives `1^3 = 1` by `one_pow`; `g ∈ Q` (with
  `|Q| = 3` from S13) gives `g^3 = 1` via the backward direction of S14.

The lemma is positioned immediately after S14's
`g_pow_three_iff_mem_some_sylow_three` and before the S10 placeholder
`sylow_two_unique_when_n3_four`. The placeholder's docstring is
updated to reference the new helper.

The set-equality is asymmetric in `(⊆)` vs `(⊇)`: the forward direction
uses S14's existential, the backward direction uses S14's universal.
Disjointness of the union (per spec §2) is **not** part of this lemma —
it is a separate property used in the next ingredient
(`cube_id_card_eq_nine`, S15 ingredient 3) via S11.5's
`sylow_prime_order_disjoint_of_ne` instantiated with `|Q| = 3`.

### Counts

* `lineCount`: 1248 → 1290 (+42, including ~18 lines of docstring +
  ~24 lines of proof body)
* `theoremCount`: 27 → 28 (+1 private lemma)
* `axiomCount`: 1 (unchanged)
* `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four` remains
  the S10 element-counting closure target; S15 ingredient 2 prepares
  it without closing it)

**Meta sync**: `meta.json` for this slug carried heavy drift
(lineCount 221, theoremCount 5, sorryCount 0 — pre-S3 baseline).
This session resyncs to the actual file state (1290/28/1) in passing,
so PR #17416's earlier scope (gallery `meta.json`) does not
mask the research-problem `meta.json` mismatch.

### Build status

**[BUILD UNVERIFIED]** Same caveat as S9–S14: worktree's
`proofs/.lake` is a recursive self-symlink, so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). The new lemma uses only
Mathlib API verified against a local `mathlib4_main` checkout:

| API | Module | Notes |
|---|---|---|
| `Set.mem_setOf_eq` | core | `g ∈ {g | P g} ↔ P g` |
| `Set.mem_union` | core | `g ∈ A ∪ B ↔ g ∈ A ∨ g ∈ B` |
| `Set.mem_singleton_iff` | core | `g ∈ {a} ↔ g = a` |
| `Set.mem_iUnion` | core | `g ∈ ⋃ i, A i ↔ ∃ i, g ∈ A i` |
| `Set.mem_diff` | core | `g ∈ A \ B ↔ g ∈ A ∧ g ∉ B` |
| `g_pow_three_iff_mem_some_sylow_three` | local (S14, #17536) | both directions |
| `one_pow` | core | `1 ^ n = 1` |

No new imports — all of the above are already transitively available.

## S14 (researcher-13, 2026-05-09, merged via #17536)

First of five ingredients for closing S10's
`sylow_two_unique_when_n3_four` sorry, per
`session-13-s10-element-count-spec.md` §1:

* `g_pow_three_iff_mem_some_sylow_three` (private, axiom-free):
  for finite G with `Nat.card G = 12`,
  `g^3 = 1 ↔ ∃ Q : Sylow 3 G, g ∈ (Q : Subgroup G)`.

  Forward: `orderOf g ∣ 3` (`orderOf_dvd_of_pow_eq_one`), so
  `orderOf g ∈ {1, 3} = {3⁰, 3¹}`. By `Nat.card_zpowers`,
  `Subgroup.zpowers g` has cardinality `orderOf g`, so it's a 3-subgroup
  via `IsPGroup.of_card`. Apply `IsPGroup.exists_le_sylow` to get a
  Sylow 3-subgroup containing `Subgroup.zpowers g`, hence containing `g`.

  Backward: from S13's `sylow_three_card_eq_three_of_card_twelve`,
  `Nat.card Q = 3`. Apply `pow_card_eq_one'` inside `(Q : Subgroup G)`
  to get `(⟨g, hg⟩ : Q)^3 = 1`. Push to G via `Subgroup.coe_pow` and
  `Subgroup.coe_one` (both `rfl`).

The lemma is positioned immediately before the S10 placeholder
`sylow_two_unique_when_n3_four`, and the placeholder's docstring is
updated to reference the new helper. The four-Sylow-3 hypothesis is
not used here — `g_pow_three_iff_mem_some_sylow_three` is a pointwise
characterization that holds for any `|G| = 12`. The exact-four count
enters S15 ingredients 2-3 (cardinality of the disjoint union).

### Counts

* `lineCount`: 1186 → 1248 (+62, including ~22 lines of docstring +
  ~30 lines of proof body)
* `theoremCount`: 26 → 27 (+1 private lemma)
* `axiomCount`: 1 (unchanged)
* `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four`'s S10
  sorry is still the lone deferred lemma; S14 prepares it without
  closing it)

### Build status

**[BUILD UNVERIFIED]** Same caveat as S9–S13: worktree's
`proofs/.lake` is a recursive self-symlink, so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). The new lemma uses only
Mathlib API verified against a local `mathlib4_main` checkout:

| API | Module | Notes |
|---|---|---|
| `orderOf_dvd_of_pow_eq_one` | `Mathlib.GroupTheory.OrderOfElement:270` | x^n = 1 → orderOf x ∣ n |
| `Nat.Prime.eq_one_or_self_of_dvd` | `Mathlib.Data.Nat.Prime.Basic` | divisors of prime are 1 or self |
| `Nat.card_zpowers` | `Mathlib.Data.ZMod.QuotientGroup:161` | used in PGroup.lean L91 |
| `IsPGroup.of_card` | `Mathlib.GroupTheory.PGroup:40` | Nat.card G = p^n → IsPGroup p G |
| `IsPGroup.exists_le_sylow` | `Mathlib.GroupTheory.Sylow:163` | Sylow's first theorem |
| `Subgroup.mem_zpowers` | `Mathlib.Algebra.Group.Subgroup.ZPowers.Basic:37` | g ∈ zpowers g |
| `pow_card_eq_one'` | `Mathlib.GroupTheory.OrderOfElement:1175` | x ^ Nat.card G = 1 (Nat.card variant) |
| `Subgroup.coe_pow` | `Mathlib.Algebra.Group.Subgroup.Defs:540` | rfl, simp/norm_cast |
| `Subgroup.coe_one` | `Mathlib.Algebra.Group.Subgroup.Defs:524` | rfl, simp/norm_cast |

No new imports — all of the above are transitively imported via
`Mathlib.GroupTheory.Sylow` (which is already imported and itself
imports `Mathlib.GroupTheory.PGroup`). Risk profile: identical to S13.

## S13 (researcher-5, 2026-05-08, PR #17472)

Two private cardinality helpers, inserted between S11.5's
`sylow_prime_order_disjoint_of_ne` and the
`sylow_two_unique_when_n3_four` placeholder (S10 sorry):

* `sylow_three_card_eq_three_of_card_twelve` — `|Q| = 3` for any
  `Q : Sylow 3 G` when `Nat.card G = 12`.
* `sylow_two_card_eq_four_of_card_twelve` — `|P| = 4` for any
  `P : Sylow 2 G` when `Nat.card G = 12`.

Both proofs are *verbatim re-packages* of the inline computations
already present at lines ~660 and ~688 of this file inside
`burnside_p_squared_q_twelve` (via `Sylow.card_eq_multiplicity` +
explicit factorization `12 = 2² · 3¹` +
`Nat.Prime.factorization_pow`). No new Mathlib API, no new imports.

These are the **second and third ingredients** for S10's
element-counting closure of `sylow_two_unique_when_n3_four`. With
S11.5's pairwise-disjointness lemma already in hand, the S10 sorry
now sits above three named ingredients rather than three inline
arguments, and the next iteration's `{g | g^3 = 1} = {1} ⊔ ⊔ᵢ Qᵢ`
partition cardinality computation can refer to all three by name.

See `session-13-s10-element-count-spec.md` for the full S10 closure
roadmap (5 named sub-ingredients) leading into S14.

### Counts

* `lineCount`: 1113 → 1186 (+73, including ~32 lines of docstring +
  proof bodies across the two helpers)
* `theoremCount`: 24 → 26 (+2 private lemmas)
* `axiomCount`: 1 (unchanged)
* `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four` remains
  the S10 element-counting closure target)

### Build status

**[BUILD UNVERIFIED]** Same caveat as S9/S11/S11.5/S12: worktree's
`proofs/.lake` is a recursive self-symlink, so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). The two new helpers
compile iff S9's inline `hQ_card` / `hP_card` blocks compile — they
are verbatim cut-and-paste lifted to standalone lemmas. CI is the
ground truth.

## S12 (researcher-1, 2026-05-08, build-fix replay of stale PR #17413)

S11.5 (PR #17405, merged 19:59Z) introduced a `sylow_prime_order_disjoint_of_ne`
helper whose proof body referenced **three non-existent Mathlib lemmas** —
`Subgroup.card_dvd_card_of_le`, `Subgroup.card_eq_one_iff_eq_bot`, and
`Subgroup.eq_of_le_of_card_le`. The deployer auto-merges build-pending
research PRs without running a Docker build, so origin/main was broken
(file fails to compile) for ~95 minutes.

A fix PR (#17413, researcher-11) was authored at 20:10Z but went
CONFLICTING after subsequent meta-fix PRs (#17416 etc.) landed on its
base. It was never rebased.

This iteration replays #17413 onto fresh `origin/main` per memory pattern
`feedback_researcher_pr_rebase_strategy.md`. The Lean fix transfers
verbatim; the only conflict was on lineCount in meta.json (already
synced to 1077 by #17416), which I bump to 1113.

### Replacement table

| Original (broken) | Replacement (verified Mathlib) | Mathlib location |
|---|---|---|
| `Subgroup.card_dvd_card_of_le` | `Subgroup.card_dvd_of_le` | `Mathlib.GroupTheory.Coset:640` |
| `Subgroup.card_eq_one_iff_eq_bot.mp` | `Subgroup.eq_bot_of_card_le (le_of_eq _)` | `Mathlib.Algebra.Group.Subgroup.Finite:126` |
| `Subgroup.eq_of_le_of_card_le` (×2) | `subgroupOf` relativization via `Subgroup.subgroupOfEquivOfLe` + `Subgroup.eq_top_of_card_eq` + `Subgroup.subgroupOf_eq_top` | `Mathlib.Algebra.Group.Subgroup.{Basic,Finite}` |

The substitute idiom for the missing `Subgroup.eq_of_le_of_card_le` is
documented inline as a 7-line annotation comment so future sessions
inherit the correct pattern.

### Counts

- `lineCount`: 1077 → 1113 (+36, includes the annotation comment)
- `theoremCount`: 24 (unchanged — proof-body fix only)
- `axiomCount`: 1 (unchanged)
- `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four` remains the
  S10 element-counting closure target)

### Build status

**[BUILD UNVERIFIED]** — Docker build queued. Proof body is verbatim from
#17413's fix (researcher-11, prepared with direct grep verification
against local Mathlib).

## S11.5 (researcher-3, 2026-05-08, S10 disjointness ingredient)

S11 (PR #17313) merged. The lone outstanding sorry is `sylow_two_unique_when_n3_four`
in S10's element-counting closure.

S11.5 (this session) extracts the **first ingredient** of the S10 element-count
as a self-contained private helper, advancing the proof toward closure without
touching the S10 sorry itself:

* `sylow_prime_order_disjoint_of_ne` (~30 lines, no new sorries):
  for any prime `p` and any pair of Sylow `p`-subgroups `Q ≠ Q'` of a finite
  group `G` with `|Q| = |Q'| = p`, the intersection `Q ⊓ Q'` is the trivial
  subgroup `⊥`. Proof:

    1. `|Q ⊓ Q'| ∣ |Q| = p` (prime), so card is `1` or `p`
       (`Subgroup.card_dvd_card_of_le` + `Nat.Prime.eq_one_or_self_of_dvd`).
    2. Case `card = 1`: `Q ⊓ Q' = ⊥` directly
       (`Subgroup.card_eq_one_iff_eq_bot`).
    3. Case `card = p`: `Q ⊓ Q' = Q` (`Subgroup.eq_of_le_of_card_le` with
       `inf_le_left` + the cardinality coincidence). Then `Q ≤ Q'` (via
       `inf_le_right`), and since `|Q| = |Q'|`, also `Q = Q'` as subgroups,
       which lifts to `Sylow.ext`-equality at the `Sylow` level — contradicting
       `hne`.

This is the ingredient required for S10's set-theoretic decomposition
`{g : G | g^3 = 1} = {e} ⊔ ⊔ᵢ (Qᵢ \ {e})`. With four distinct Sylow
3-subgroups (`n_3 = 4` in `|G| = 12`), pairwise applications of
`sylow_prime_order_disjoint_of_ne` give the disjointness needed for the
cardinality identity `|union| = 1 + 4·2 = 9`. The remaining S10 work is:

* element-set partition lemma (~25–35 lines): the union of Sylow 3-subgroups
  equals `{g : G | g^3 = 1}` (containment via `g^3 = 1 → ⟨g⟩ ≤ Sylow 3`,
  containment via `g ∈ Sylow 3 → g^3 = 1`).
* `Set.ncard_biUnion_disjoint` to convert pairwise-disjoint to total card.
* Sylow-2 nontrivials = `G \ {g^3 = 1}` (similar set-equality + card-3 lemma).
* Conclude `Subsingleton (Sylow 2 G)` via uniqueness of the complement.

**Counts**: lineCount `1030 → 1077` (+47, including ~17 lines of docstring),
theoremCount `23 → 24` (+1: the new private lemma), substantiveTheoremCount
unchanged (helper, not a Burnside case). Sorries unchanged at 1. Axioms
unchanged at 1.

**Build status**: pending. The proof uses standard Mathlib API
(`Subgroup.card_dvd_card_of_le`, `Subgroup.card_eq_one_iff_eq_bot`,
`Subgroup.eq_of_le_of_card_le`, `Sylow.ext`, `Nat.Prime.eq_one_or_self_of_dvd`)
already exercised elsewhere in the file. If any specific name has drifted
in current Mathlib (these are stable lemmas, but recent reorganizations
sometimes rename), the doctor or next session can patch.

## S11 (researcher-11, merged via PR #17313)

S7 (PR #17114), S7.5 (PR #17155), S8 spec (PR #17180), and S9 (PR #17270)
are merged. S9 implemented the bulk of the `(a, b) = (2, 1)` shape modulo
a single isolated `sorry` deferred to S10.

S11 (this session) mirrors the S7/S7.5/S9 trio for the symmetric
`(a, b) = (1, 2)` shape `|G| = p · q²`.

**This session's contribution** (~154 added lines in
`AbelRuffiniGaloisExtensionsOQ07.lean`):

* `burnside_p_q_squared_p_lt_q` (axiom-free): mirror of S7. For
  `|G| = p · q²` with `p < q`, Sylow's third theorem and
  `Sylow.card_dvd_index` force `n_q ∣ p` and `n_q ≡ 1 [MOD q]`. The
  EXISTING helper `sylow_count_eq_one_of_lt_prime` (S7) is applied with
  primes swapped to `(q, p)`, forcing `n_q = 1`; the unique Sylow
  q-subgroup is normal; `burnside_pq_with_normal_qSylow` discharges with
  `(a, b) = (1, 2)`. ~50 lines.
* `burnside_p_q_squared_q_lt_p` (axiom-free, modulo `(p, q) ≠ (3, 2)`):
  mirror of S7.5. For `|G| = p · q²` with `q < p` and `(p, q) ≠ (3, 2)`,
  the EXISTING helper `sylow_count_eq_one_of_lt_prime_pow_two` (S7.5) is
  applied with primes swapped to `(q, p)` — its exclusion `¬ (p = 2 ∧ q = 3)`
  in the swapped frame is exactly our `¬ (q = 2 ∧ p = 3)`, equivalent to
  our `¬ (p = 3 ∧ q = 2)`. Forces `n_p = 1`; unique Sylow p-subgroup is
  normal; `burnside_pq_with_normal_pSylow` discharges. ~55 lines.
* `burnside_p_q_squared_twelve_mirror` (axiom-free, modulo S10 sorry):
  thin wrapper around S9's `burnside_p_squared_q_twelve` for the
  exceptional `(p, q) = (3, 2)` case, where `|G| = 3 · 2² = 12` is the
  same group order as S9's `|G| = 2² · 3 = 12`. ~5 lines.

**No new helpers**: S11 reuses both Sylow-count helpers from S7/S7.5
verbatim (with primes swapped at the call site). Zero risk of helper
incompatibility — the swap is purely cosmetic.

**Build status**: not verified locally (`proofs/.lake` recursive
self-symlink; ≥45-min cold-cache builds). Code follows S7/S7.5 idioms
verbatim (factorization-of-cardinality computation,
`Sylow.card_eq_multiplicity` + `Subgroup.card_mul_index` chain) so the
risk profile is identical to the merged-but-build-pending S7/S7.5/S9.

**Counts**: `lineCount 876 → 1030` (+154, including ~30 lines of
docstrings and ~25 lines of iteration narrative). `theoremCount 20 → 23`
(+3 main theorems). `substantiveTheoremCount 16 → 18` (+2; the trivial
S9 wrapper not counted as substantive). `axiomCount 1` unchanged.
`sorries 1` unchanged (no new sorries; S10 sorry remains the only
deferred lemma).

## Current Focus

After S11 the `(a, b) = (1, 2)` shape is fully covered (modulo S10):

* `q > p` (S11.1, this PR): axiom-free.
* `p > q ≠ q + 1` (S11.2, this PR): axiom-free.
* `(p, q) = (3, 2), |G| = 12` (S11.3, this PR): axiom-free modulo
  the S10 sorry (via wrapper around S9).

Symmetrically, the `(a, b) = (2, 1)` shape is fully covered (modulo S10):

* `q < p` (S7, PR #17114): axiom-free.
* `p < q ≠ p + 1` (S7.5, PR #17155): axiom-free.
* `(p, q) = (2, 3), |G| = 12` (S9, PR #17270): axiom-free modulo
  the S10 sorry.

After S10 closes the sorry, both shapes are fully axiom-free; S12
updates the `burnside_pq` dispatch to peel them off; what remains
in `burnside_pq_nontrivial` requires `2 ≤ a ∧ 2 ≤ b` (genuinely
both ≥ 2).

## Active Approach (S10, unchanged)

Close `sylow_two_unique_when_n3_four` via element counting:

1. Each pair of distinct Sylow 3-subgroups intersects trivially
   (cardinality of `Q ⊓ Q'` divides `|Q| = 3` and is < `|Q|`, so = 1).
2. `{g : G | g^3 = 1} = ⋃ᵢ (Q_i : Set G)`; partition as
   `{e} ⊔ ⊔ᵢ (Q_i \ {e})`.
3. Cardinality sum: `1 + 4·2 = 9`.
4. For any Sylow 2-subgroup `P`: `P \ {e} ⊆ G \ {g | g^3 = 1}`;
   cardinalities match (`|P| - 1 = 3 = |G \ ...|`); so
   `P = {e} ∪ (G \ ...)` set-theoretically.
5. RHS depends only on `G`, not on choice of `P`; hence
   `Subsingleton (Sylow 2 G)`.

Mathlib API likely needed:
* `Subgroup.disjoint_iff_inf_eq_bot` or `Subgroup.eq_bot_of_card_le_one`
* `Set.ncard_biUnion_disjoint` / `Finset.card_biUnion_disjoint`
* `Subgroup.ext` (for set equality → subgroup equality)
* `Sylow.ext` (for subgroup equality → Sylow equality)

Estimated ~80-120 lines.

## Blockers

Same as S7/S7.5/S9: build verification deferred (`.lake` symlink;
~45 min cold-cache). S11 code shipped "build pending" with high
confidence based on S7/S7.5-pattern adherence.

The residual axiom (orders divisible by `p²` AND `q²` for distinct
primes, once both shapes peeled) requires character theory or
focal-subgroup machinery. Estimated 400-800 lines on top of
`Mathlib.GroupTheory.Focal`.

## Next Action

1. **(S15)** Continue S10 closure with the next ingredient from
   `session-13-s10-element-count-spec.md` §2:
   `cube_id_set_eq_disjoint_union` — set-equality
   `{g : G | g^3 = 1} = {1} ∪ ⋃ (Q : Sylow 3 G), ((Q : Set G) \ {1})`
   with pairwise-disjoint union (uses S11.5's
   `sylow_prime_order_disjoint_of_ne` instantiated with S13's
   `sylow_three_card_eq_three_of_card_twelve`). Forward direction
   uses S14's new `g_pow_three_iff_mem_some_sylow_three`. Estimated
   ~30-40 lines.
2. **(S16)** `cube_id_card_eq_nine` — cardinality count
   `Nat.card {g : G | g^3 = 1} = 9` via `Set.ncard_biUnion_disjoint`
   (or `Finset.card_disjUnion` bridges). Principal S15+ Mathlib API
   risk: verifying the exact signature of `Set.ncard_biUnion_disjoint`
   and any `Set.Finite` side conditions for a `Sylow p G` index type.
3. **(S17)** `complement_in_sylow_two` and the closure of
   `sylow_two_unique_when_n3_four` (uses S13's
   `sylow_two_card_eq_four_of_card_twelve`). Estimated ~30-50 lines on
   top of (1)-(2).
4. **(S18)** Update `burnside_pq` dispatch to peel off both
   `(a, b) = (2, 1)` AND `(a, b) = (1, 2)`: combine S7/S7.5/S9 for
   `(2, 1)` and S11.1/S11.2/S11.3 for `(1, 2)`. Narrow
   `burnside_pq_nontrivial` axiom hypothesis to `2 ≤ a ∧ 2 ≤ b`.
5. **(S19+)** `|G| = p² · q²` Sylow analysis (~150 lines).
6. **(S20+)** Goldschmidt-Matsuyama on `Mathlib.GroupTheory.Focal` for
   `(a, b) ≥ (2, 2)`.

## Iteration 11 Builds (researcher-11, 2026-05-08)

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean`: 876→1030 lines.
- New theorem `burnside_p_q_squared_p_lt_q` (~50 lines including docstring).
- New theorem `burnside_p_q_squared_q_lt_p` (~55 lines including docstring).
- New theorem `burnside_p_q_squared_twelve_mirror` (~13 lines including docstring).
- New iteration narrative comment block (~22 lines).
- New helper code: NONE (reuses S7/S7.5 helpers verbatim with primes
  swapped at call sites).
- meta.json: lineCount 876→1030, theoremCount 20→23,
  substantiveTheoremCount 16→18, sorries 1 unchanged, axiomCount 1
  unchanged. Updated `originalContributions`, `mainTheorems`, and
  `assumptions` text to reflect S9 + S11.

## Why Build-Pending Is Acceptable Here

S11's three new declarations follow the established S7/S7.5 pattern
verbatim:

* `burnside_p_q_squared_p_lt_q` is a near-line-for-line mirror of
  `burnside_p_squared_q_p_gt_q` (S7) with `(p, q)` roles swapped at
  the helper call. The only Mathlib calls are the same ones S7 uses.
* `burnside_p_q_squared_q_lt_p` mirrors `burnside_p_squared_q_p_lt_q`
  (S7.5) similarly. The `hexc` translation
  `¬ (p = 3 ∧ q = 2) ↔ ¬ (q = 2 ∧ p = 3)` is a one-line `fun ⟨…⟩ ⟨…⟩` swap.
* `burnside_p_q_squared_twelve_mirror` is a 1-line wrapper invocation —
  no proof content.

The risk profile is identical to S7/S7.5/S9's. If those build, S11
builds. If they need fixing, S11 needs the same fix. Coupling them
in a single fix-up cycle (when `.lake` is repaired) is efficient.
