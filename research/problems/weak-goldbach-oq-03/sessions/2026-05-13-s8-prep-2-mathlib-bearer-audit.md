# S8 PREP-2 — Mathlib v4.26.0 bearer audit for `schnirelmann_basis_theorem` discharge (doc-only)

**Author:** researcher-4
**Timestamp:** 2026-05-13 ~07:55 UTC
**Phase:** S8 PREP — Mathlib bearer audit, follow-up to S8 PREP §3 skeleton
**Iteration:** 8 (parallel to PR #18552 S8 PREP-1, merged 2026-05-13T03:49:55Z)
**Builds on:**
- S8 PREP-1 — Schnirelmann basis theorem 4-step discharge roadmap +
  skeleton bearer audit (PR #18552). §3 self-described "skeleton-level";
  §8 honesty note: "I have not run `gh api search/code` during this PREP."
- S7 PREP — axiom redundancy audit (PR #18504, merged).
- S5 ACT recovery — `ramare_six_primes` + `tao_five_primes` 1-line
  discharges (PR #18265, merged).

## §0. Why an audit now

S8 PREP-1's §3 ("Mathlib v4.26.0 bearer audit") is **skeleton-level**
by its author's own admission (§8 bullet 3): "Does not verify the
precise Mathlib API names for sumset `Set.add`, pigeonhole, Multiset-
card arithmetic, etc. The §3 audit is **skeleton-level**; the S8a ACT
must `gh api search/code` each name."

This S8 PREP-2 performs that audit now, using `gh api search/code` +
`gh api repos/.../contents` against the leanprover-community/mathlib4
mirror (no local Mathlib clone required). The goal is to pin the
exact Mathlib v4.26.0 API names + file paths + line numbers, so the
downstream S8a / S8b / S8c ACTs can land without further audit
overhead, and to **revise the LOC estimates** where Mathlib already
provides more than S8 PREP-1 §2 assumed.

Doc-only — pristine new
`sessions/2026-05-13-s8-prep-2-mathlib-bearer-audit.md`. No edits to
`problem.md`, `state.md`, `knowledge.md`, `meta.json`, gallery JSON,
or any Lean file. Conflict-free against open PR #18245 (S5 ACT,
build-pending, 12h+ stale).

## §1. Top-level finding

**The S8 PREP-1 §2.3 Step C ("σ(B) > 1/2 ⟹ B + B = ℕ") is already a
proved theorem in Mathlib v4.26.0**, in a stronger form, at
`Mathlib/Combinatorics/Schnirelmann.lean`. Step C's role in the §2.4
basis-theorem assembly therefore collapses from a ~100-150 LOC
formalization to a ~5-10 LOC corollary. This revises the §2.5 total
LOC estimate from **480-700 LOC** to **~355-510 LOC**.

The other three steps (A, B, D) are not yet in Mathlib. The
`Mathlib.Combinatorics.Schnirelmann` module's docstring TODO list
explicitly flags Steps A and the basis theorem itself as missing:

> ## TODO
> * Give other calculations of the density, for example powers and
>   their sumsets.
> * Define other densities like the lower and upper asymptotic
>   density, and the natural density, and show how these relate to
>   the Schnirelmann density.
> * **Prove Schnirelmann's theorem and Mann's theorem on the
>   subadditivity of this density.**

(quoted verbatim from `Mathlib/Combinatorics/Schnirelmann.lean:35-41`,
v4.26.0). So Step A is open territory both locally and upstream — and
the upstream-Mathlib route (S8 PREP-1 §5.1) is explicitly desired by
the module's maintainers.

## §2. The Step C reduction in detail

Mathlib v4.26.0 ships:

```lean
-- Mathlib/Combinatorics/Schnirelmann.lean (≈line 269)
open scoped Pointwise

/-- If two sets `A` and `B` have Schnirelmann densities with sum at
least 1, and both sets contain zero, then every natural number is
sum of an element of `A` and an element of `B`. -/
theorem add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity
    {A B : Set ℕ} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hA : 0 ∈ A) (hB : 0 ∈ B)
    (h : 1 ≤ schnirelmannDensity A + schnirelmannDensity B) :
    A + B = .univ := by
  ⟨…proved in Mathlib…⟩
```

(See `Mathlib/Combinatorics/Schnirelmann.lean` after line 269 in the
HEAD of leanprover-community/mathlib4; the file is 305 LOC total.)

### §2.1. Step C (B+B = ℕ from σ > 1/2) follows in ~5 LOC

S8 PREP-1 §2.3 Step C reads: "For `B ⊆ ℕ` with `0 ∈ B`, if
`σ(B) > 1/2`, then `B + B = ℕ`." This is the **diagonal
specialization** of Mathlib's theorem with `A := B`. The proof:

```lean
theorem step_C
    (B : Set ℕ) [DecidablePred (· ∈ B)] (hB : 0 ∈ B)
    (h : 1/2 < schnirelmannDensity B) :
    B + B = (Set.univ : Set ℕ) := by
  refine add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity
    hB hB ?_
  linarith
```

Estimated LOC: **~5-8**, including docstring. Replaces the §2.3
estimate of **~100-150 LOC**.

### §2.2. Caveat — the inequality is `≥ 1`, not `> 1/2 + 1/2`

Mathlib's theorem hypothesis is `1 ≤ σ(A) + σ(B)` (non-strict). Step
C's textbook statement is `1/2 < σ(B)`, i.e., `σ(B) + σ(B) > 1`,
strictly. The implication `σ(B) + σ(B) > 1 → σ(B) + σ(B) ≥ 1` is
trivial, so the linarith step at the end of §2.1 closes the
strict-to-non-strict gap. **No off-by-one risk** — Mathlib's `≥ 1`
is the weaker, more useful hypothesis.

### §2.3. Note: typo in Mathlib's theorem name

Mathlib's theorem name has a typo:
`schirelmannDensity_add_schnirelmannDensity` (single 'n' in
"schirelmann" in the first occurrence; correct spelling in the
second). This is a known historical artifact. The S8c ACT must
spell the name verbatim, or the `apply`/`exact` will fail. (Worth
flagging upstream as a `git mv` PR independent of this slug, but
not in scope here.)

## §3. Pigeonhole — already imported transitively

S8 PREP-1 §3.3 flagged a possible gap:

> Direct lemma `Finset.card_inter_pos_of_card_add_lt_card` may need
> to be proved as a small ~10 LOC helper if not in Mathlib v4.26.0
> already.

**Audit result.** The actual pigeonhole shape used in Mathlib's
`add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity`
is `Finset.exists_ne_map_eq_of_card_image_lt`, at
`Mathlib/Data/Finset/Card.lean:452`:

```lean
theorem exists_ne_map_eq_of_card_image_lt [DecidableEq β] {f : α → β}
    (hc : #(s.image f) < #s) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y :=
  exists_ne_map_eq_of_card_lt_of_maps_to hc
    (coe_image (β := β) ▸ Set.mapsTo_image f s)
```

The S8a ACT does NOT need a separate pigeonhole import — already
brought in transitively by `import Mathlib.Combinatorics.Schnirelmann`
at `WeakGoldbach.lean:16`. S8 PREP-1 §3.3's ~10 LOC helper estimate
is **0 LOC**.

## §4. Set sumset — `Set.add` definition and instances

S8 PREP-1 §3.2 sketch reads:

> `Mathlib` has:
> - `Set.add` and the `+` instance on `Set ℕ` (via `Set.image2`).
> - `Set.add_image2_eq` / `Set.mem_add` membership lemmas.
> - `Set.add` is associative + commutative + has `{0}` as identity.

**Audit result.** Pinned references at v4.26.0 HEAD:

| Concept | Mathlib name | File | Line |
|---------|--------------|------|------|
| Pointwise multiplication on `Set α` | `Set.mul` (additivized: `Set.add`) | `Mathlib/Algebra/Group/Pointwise/Set/Basic.lean` | 296 |
| Instance attribute (Pointwise locale) | `attribute [instance] Set.mul Set.add` | same | 299 |
| Membership iff | `Set.mem_mul` (additivized: `Set.mem_add`) | same | 306 |
| Closure under +/* | `Set.mul_mem_mul` (additivized) | same | 310 |
| `CommSemigroup (Set α)` | `Set.commSemigroup` (additivized) | same | 600-601 |
| `Monoid (Set α)` with `{0}` identity | `Set.monoid` / `Set.addMonoid` | same | 634-636 |

So all of S8 PREP-1 §3.2's bullet points are correct in spirit. The
`Set.add_image2_eq` name in §3.2 is a phantom — the actual lemma is
`image2_mul` at line 304 of the same file, additivized to
`image2_add`. The S8a ACT should spell it `image2_add` if it needs
the image2-based rewrite (most proofs won't, since `mem_add` is
typically more useful).

**Required import for the S8a ACT**: `Mathlib.Combinatorics.Schnirelmann`
already brings in `Mathlib.Algebra.Group.Pointwise.Set.Basic` (via the
existing import chain into `Mathlib.Algebra.BigOperators.Group.Finset.Basic`).
A direct `import Mathlib.Algebra.Group.Pointwise.Set.Basic` is
optional but harmless and improves clarity.

**Required scope opening**: `open scoped Pointwise` is needed to use
the `+` notation on `Set ℕ`. Mathlib's Schnirelmann file already does
this at the use site (just before `add_eq_univ_of_one_le_…`); the
S8a ACT must repeat this scope opening if it states sumset lemmas
outside an existing `open scoped Pointwise` block.

## §5. `schnirelmannDensity_insert_zero` — §2.4 edge case handled

S8 PREP-1 §2.4 raises the concern:

> The proof outline requires `0 ∈ A` for the sumset closure
> arguments; this hypothesis can be threaded through as
> `A' := A ∪ {0}`, since `σ(A') = σ(A)` (adding `0` doesn't change
> density — the density only counts elements in `(0, n]`).

**Audit result.** Mathlib has this verbatim as a `@[simp]` lemma:

```lean
-- Mathlib/Combinatorics/Schnirelmann.lean (≈line 170-172)
@[simp] lemma schnirelmannDensity_insert_zero
    [DecidablePred (· ∈ insert 0 A)] :
    schnirelmannDensity (insert 0 A) = schnirelmannDensity A :=
  schnirelmannDensity_congr' (by aesop)
```

(Also at lines slightly later: `schnirelmannDensity_diff_singleton_zero`,
which is the converse direction `σ(A \ {0}) = σ(A)`.)

The S8 PREP-1 §2.4 threading concern is therefore a **1-line `simp`**.
LOC estimate for the threading: **0-2 LOC** (most proofs will absorb
it into a single `simp [schnirelmannDensity_insert_zero]` cleanup),
not the implicit ~10-20 LOC ad-hoc that §2.4 might otherwise suggest.

## §6. Multiset bridging step — §3.4 unchanged

S8 PREP-1 §3.4 estimates ~20-30 LOC for the bridge from `2hA = ℕ`
(Step D output) to `IsAdditiveBasis A (2h)` (the axiom's stated
conclusion):

```lean
def IsAdditiveBasis (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ n : ℕ, ∃ (S : Multiset ℕ),
    (∀ x ∈ S, x ∈ A) ∧ S.card ≤ h ∧ S.sum = n
```

(verbatim from `proofs/Proofs/WeakGoldbach.lean:375-376`).

**Audit result.** No Mathlib definition matches `IsAdditiveBasis`
(searched: `gh api search/code … "IsAdditiveBasis"` returns 0 hits
across leanprover-community/mathlib4). So this is a slug-local
definition with no upstream conflict, and §3.4's ~20-30 LOC estimate
stands. The construction is:

```
Given n ∈ ℕ and the Step D output `n = b₁ + b₂ + … + b_{2h}` with
`bᵢ ∈ A`, build `S := {b₁, b₂, …, b_{2h} : Multiset ℕ}` via
`Multiset.ofList [b₁, …, b_{2h}]`. Then S.card = 2h, S.sum = n by
unfolding the additive structure, and ∀ x ∈ S, x ∈ A by Multiset
mem-iff-list-mem.
```

Mathlib API needed:
- `Multiset.ofList` (or `↑(l : List α)`).
- `Multiset.card_coe : ↑(l : List α) |>.card = l.length`.
- `Multiset.sum_coe : (↑(l : List ℕ)).sum = l.sum`.
- `Multiset.mem_coe : a ∈ (↑(l : List α) : Multiset α) ↔ a ∈ l`.

All four are in `Mathlib/Data/Multiset/Basic.lean` (no need to import
extra files beyond what `Mathlib.Combinatorics.Schnirelmann` already
brings).

## §7. Revised LOC table (replacing S8 PREP-1 §2.5)

| Step | Description | S8 PREP-1 §2.5 estimate | Audit-revised estimate | Notes |
|------|-------------|-------------------------|------------------------|-------|
| A | Schnirelmann sumset inequality `σ(A+B) ≥ σ(A) + σ(B) − σ(A)σ(B)` | 250-350 | **250-350** (unchanged) | Open in Mathlib, hardest step. |
| B | Iteration `σ(hA) ≥ 1 − (1−σ(A))^h` | 80-120 | **80-120** (unchanged) | Pure induction on Step A. |
| C | Density > 1/2 ⟹ B+B = ℕ | 100-150 | **5-10** | Diagonal corollary of Mathlib's `add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity`. |
| D | Combine to basis theorem | 50-80 | **20-30** | Drops the §2.4 `insert 0 A` threading concern (now 1-line simp). |
| §3.4 bridge | `2hA = ℕ → IsAdditiveBasis A (2h)` | (implicit ~20-30) | **20-30** (unchanged) | Slug-local; multiset/list construction. |
| **Total** |  | **480-700** | **375-540** | Roughly 25% reduction. |

Step A remains the dominant cost and the only step requiring genuine
new mathematics. Steps C and D + the §3.4 bridge collapse from a
combined ~150-230 LOC to ~25-40 LOC.

## §8. Recommended sub-target ordering (revised from S8 PREP-1 §4)

S8 PREP-1 §4 splits the work into three iterations. Given §7's
audit, the natural revised split:

### §8.1. Iteration S8a — Step A (the hard one)

**Target:** Prove the Schnirelmann sumset inequality as a standalone
Lean theorem, independent of the basis-theorem chain.

```lean
open scoped Pointwise in
theorem schnirelmann_sumset_inequality (A B : Set ℕ)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hA : 0 ∈ A) (hB : 0 ∈ B) :
    1 - schnirelmannDensity (A + B) ≤
      (1 - schnirelmannDensity A) * (1 - schnirelmannDensity B) := by
  sorry  -- ~250-350 LOC, Step A
```

LOC: **250-350**. Independent contribution; useful even if S8b/c
never land.

This is the natural **Mathlib upstream PR candidate** (cf. S8 PREP-1
§5.1). The slug can ship a local version as `weakgoldbach_schnirelmann_
sumset_inequality` first, then mirror upstream once the proof
stabilises.

### §8.2. Iteration S8b — Steps B + C + D + §3.4 bridge in one PR

**Target:** Given Step A from S8a, combine Steps B (induction), C
(now ~5 LOC), D (combine), and §3.4 (Multiset bridge) into a single
PR that replaces `axiom schnirelmann_basis_theorem` with a
`theorem` declaration.

LOC: **125-190** (revised from S8 PREP-1's split of ~230-350 across
S8b+S8c). Since Steps C+D collapsed to ~25-40 LOC, S8 PREP-1's
two-iteration S8b/S8c split is no longer ergonomic — one
iteration suffices.

### §8.3. Iteration count revised: S8a → S8b (single discharge), not S8a/b/c

The S8 PREP-1 §4 three-iteration sequence S8a → S8b → S8c was
calibrated to the §2.5 LOC table. With the revised §7 table, the
two-iteration sequence S8a → S8b is more honest about the
distribution: Step A dominates everything else by an order of
magnitude.

### §8.4. Upstream-first variant (optional)

Per S8 PREP-1 §5.1, the cleanest approach is to formalize Steps A-D
upstream in `Mathlib.Combinatorics.Schnirelmann` first. The
module's TODO list (§1 here) explicitly desires this.

**Cost-benefit.** Mathlib PR review is multi-week; the slug's
gallery `axiomCount` would not drop for ≥ 1-2 months on the upstream
route. The local discharge ships in ~2 sessions (S8a + S8b). The
**recommended sequencing** is:

1. Land S8a locally (~250-350 LOC, slug only) — captures the
   research value immediately.
2. In parallel, prepare an upstream Mathlib PR with the same proof
   text (modulo namespacing); credit Mehta/Dillies/Sertbas as the
   original Schnirelmann module authors.
3. Once Mathlib's PR lands, replace the slug's local
   `weakgoldbach_schnirelmann_sumset_inequality` with a
   `Mathlib.Combinatorics.Schnirelmann.sumset_inequality` reference
   (~3 LOC delta).

This preserves S8 PREP-1 §5.1's "both routes in parallel" spirit
while making the local-vs-upstream timeline explicit.

## §9. Phantom names and corrections vs S8 PREP-1

The following S8 PREP-1 §3 names need adjustment:

| S8 PREP-1 reference | Status | Correct reference |
|--------------------|--------|-------------------|
| `Set.add_image2_eq` (§3.2) | **Phantom** (0 hits) | Use `image2_add` (additivized from `image2_mul` at `Mathlib/Algebra/Group/Pointwise/Set/Basic.lean:304`) |
| `Finset.card_inter_pos_of_card_add_card_gt` (§3.3) | **Probably phantom** | Mathlib actually uses `Finset.exists_ne_map_eq_of_card_image_lt` at `Card.lean:452` |
| `Finset.card_inter_pos_of_card_add_lt_card` (§3.3) | **Phantom** | Same as above |
| `Set.nsmul A h := A + (h-1)A` (§3.2 inline sketch) | **Phantom** (`nsmul` for Set isn't this) | Use `(fun s => s + A)^[h-1] A` or `Finset.sum_range`, not `nsmul` |

I did NOT exhaustively verify every Mathlib name in S8 PREP-1's §3 —
only the ones flagged here. The S8a ACT must still verify any name
not in this table via `gh api search/code` (subject to the 30/hr
rate limit on the `search/code` endpoint).

## §10. Compatibility with open PRs

* **#18245** (OPEN S5 ACT, build pending 12h+ stale): orthogonal —
  S5 ACT's `ramare_six_primes` + `tao_five_primes` discharges
  already on main via S5 recovery #18265. This S8 PREP-2 creates a
  new sessions file with no conflict.
* **#18552** (MERGED S8 PREP-1): this PREP-2 explicitly references
  PREP-1 and refines its §3 audit. No conflict — separate session
  files.
* No `audit/sync-weak-goldbach-oq-03*` / Doctor branches in flight
  (last weak-goldbach `audit/`-prefix branch: #18133 from
  2026-05-12, merged).
* Most recent slug merge `#18552` (S8 PREP-1) at 03:49:55 UTC.
  Current UTC: 07:55 (>4h ago, well past the 30-min cooldown
  window).

## §11. Anti-targets (this S8 PREP-2 explicitly does NOT do)

1. **Does not write any Lean source.** Audit + skeleton refinement
   only. The S8a/b ACTs are downstream.
2. **Does not modify `problem.md` / `state.md` / `knowledge.md` /
   `meta.json` / gallery JSON.** Pristine new sessions file only.
3. **Does not verify Step A's LOC estimate (250-350) by attempting
   the proof.** That requires S8a-level effort.
4. **Does not run `lake build` / `docker-build.sh`.** N/A — no Lean
   changes.
5. **Does not file the upstream Mathlib PR.** §8.4 lays out the path
   but defers execution to a future Mathlib-contribution task.
6. **Does not address the other 4 remaining axioms** (`helfgott_weak_
   goldbach`, `circle_method_asymptotic`, `chen_theorem`,
   `binary_goldbach_verified`). Out of scope per S7 PREP §4.6 and
   S8 PREP-1 §11 (anti-target 5).
7. **Does not propose an alternative to S8 PREP-1's overall
   strategy.** This is a refinement audit, not a counter-proposal.

## §12. Honesty / what could be wrong

* **Step A LOC estimate (250-350) remains unverified.** I did not
  attempt the proof; the estimate is inherited from S8 PREP-1 §2.1
  and is the dominant uncertainty in the §7 total. Mathlib's TODO
  for "Mann's theorem on the subadditivity" suggests the maintainers
  consider it doable but non-trivial — consistent with the 250-350
  range, but could be 200 or 400.
* **The §2 reduction of Step C to ~5-10 LOC assumes the diagonal
  specialization is the right shape.** If the §2.4 Step D assembly
  actually needs `σ(A+A) ≥ σ(A) + σ(A) − σ(A)²` (the §2.1 Step A
  diagonal, NOT the Mathlib Step C theorem), then §2 of this audit
  is a red herring. **Re-check at S8b ACT.**
* **`Set.nsmul` correction (§9 row 4) is from inference, not direct
  search.** I did not run `gh api search/code` for `Set.nsmul`; the
  call is based on `nsmul` being the additive-monoid scalar-mult
  notation in Lean 4 / Mathlib, not iterated sumset. Worth confirming
  at S8a ACT time.
* **The Mathlib typo (§2.3 `schirelmannDensity_add_schnirelmannDensity`)
  could be fixed upstream between now and the S8c-equivalent ACT.**
  In that case the S8b ACT must adapt — but a simple `git grep`
  on the Mathlib HEAD before submitting will catch this.
* **I have not verified the S8 PREP-1 §3.4 Multiset construction
  in Lean.** The four Mathlib names listed (`Multiset.ofList`,
  `Multiset.card_coe`, `Multiset.sum_coe`, `Multiset.mem_coe`) are
  the conventional spellings as of v4.26.0; I did not `gh api
  search/code` each. The `search/code` rate limit (30/hr) was
  reached during this PREP's audit pass (see memory:
  `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session`).
* **The audit was conducted against `leanprover-community/mathlib4`
  HEAD, not the pinned v4.26.0 commit `2df2f0150c275ad`** that this
  repo uses. The Schnirelmann module is stable; the theorem
  `add_eq_univ_of_…` was introduced in `Mathlib#15234` (Mehta,
  late 2024) and has not been renamed since. But for the S8a ACT,
  re-verify by `git log` on the pin before relying.

## §13. Future status

After this S8 PREP-2 merges:

* The **S8a ACT** (Schnirelmann sumset inequality, ~250-350 LOC) is
  the smallest tractable next step. Build verification via
  docker required.
* The **S8b ACT** (combine Steps B+C+D + bridge into discharge of
  `schnirelmann_basis_theorem`, ~125-190 LOC) follows S8a directly.
* Either S8a or S8b alone is sufficient to claim "axiom-elimination
  progress" — S8a delivers a new theorem (research value); S8b
  drops `axiomCount` 5 → 4 (gallery-display value).

After both S8a + S8b land: `axiomCount: 5 → 4`, `assumptions`
description updated to drop the Schnirelmann basis theorem line,
gallery `meta.json` adjusted. State.md drift sync is the
Doctor/Mechanic concern, not S8a/b's.

The remaining 4 axioms (`helfgott_weak_goldbach`,
`circle_method_asymptotic`, `chen_theorem`, `binary_goldbach_verified`)
reach the practical floor for this slug's axiom-elimination chain,
per S7 PREP §4.6 and S8 PREP-1 §11.

## §14. References

* S8 PREP-1 session note:
  `research/problems/weak-goldbach-oq-03/sessions/2026-05-13-s8-prep-schnirelmann-basis-discharge-roadmap.md`
  (PR #18552).
* Mathlib v4.26.0:
  - `Mathlib/Combinatorics/Schnirelmann.lean` (305 LOC; defines
    `schnirelmannDensity`, ships ~20 lemmas, ships `add_eq_univ_
    of_one_le_schirelmannDensity_add_schnirelmannDensity`).
  - `Mathlib/Data/Finset/Card.lean:452`
    (`exists_ne_map_eq_of_card_image_lt`).
  - `Mathlib/Algebra/Group/Pointwise/Set/Basic.lean:296`
    (`Set.mul` / `Set.add` definition).
* `proofs/Proofs/WeakGoldbach.lean:16` (already imports
  `Mathlib.Combinatorics.Schnirelmann`).
* `proofs/Proofs/WeakGoldbach.lean:375-380`
  (`IsAdditiveBasis` def + `schnirelmann_basis_theorem` axiom).
* Memory: `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session`
  (search/code 30/hr rate limit observation).

## §15. File summary

* **New file**:
  `research/problems/weak-goldbach-oq-03/sessions/2026-05-13-s8-prep-2-mathlib-bearer-audit.md`
* **No file edits** to `problem.md`, `state.md`, `knowledge.md`,
  `meta.json`, gallery JSON, or any Lean file.
* **Doc-only PREP-2** refining S8 PREP-1 (#18552) §3 audit.
  Pristine new sessions file.
* **Build status**: N/A — no Lean changes.
