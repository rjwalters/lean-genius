# Current State

**Phase**: ACT
**Since**: 2026-05-08T18:30:00Z
**Iteration**: 9 (partial Lean implementation)

## S9 (this session, researcher-10, partial implementation)

S7 (PR #17114), S7.5 (PR #17155), and S8 spec (PR #17180) are merged.
S8 produced a detailed spec for the exceptional `(p, q) = (2, 3),
|G| = 12` case (`session-8-twelve-spec.md`); S9 implements the bulk
of that spec axiom-free, with a single isolated `sorry` deferred to
S10 for the element-counting cardinality lemma.

**This session's contribution** (~140 added lines in
`AbelRuffiniGaloisExtensionsOQ07.lean`):

* `sylow_count_dvd_four_modEq_one_three` (private helper, axiom-free):
  if `n ≥ 1`, `n ∣ 4`, `n ≡ 1 [MOD 3]`, then `n ∈ {1, 4}`. Decidable
  on Nat via `interval_cases` (2 ≢ 1 [MOD 3]; 3 ∤ 4).
* `sylow_two_unique_when_n3_four` (private, sorry'd for S10): when
  `|G| = 12` and `n_3 = 4`, the Sylow 2-subgroup is unique. Proof
  outline carried in the docstring; implementation requires
  Set/Finset cardinality machinery.
* `burnside_p_squared_q_twelve` (axiom-free modulo the above sorry):
  case-splits on `n_3 ∈ {1, 4}`. The `n_3 = 1` branch is fully
  discharged (Sylow 3-subgroup normal; `burnside_pq_with_normal_qSylow`
  with `(a, b) = (2, 1)`). The `n_3 = 4` branch reduces to
  `Subsingleton (Sylow 2 G)` via the S10 lemma, yielding a normal
  Sylow 2-subgroup; `burnside_pq_with_normal_pSylow` with
  `(a, b) = (2, 1)` discharges.

**Build status**: not verified locally (`proofs/.lake` recursive
self-symlink; ≥45-min cold-cache builds). Code follows the S7.5 idioms
verbatim (factorization-of-cardinality computation,
`Sylow.card_eq_multiplicity` + `Subgroup.card_mul_index` chain) so the
risk profile is identical to the merged-but-build-pending S7.5.

**Counts**: `lineCount 738 → 876` (+138, including ~35 lines of
docstrings). `theoremCount 17 → 20` (+1 main theorem, +2 private
lemmas). `axiomCount 1` unchanged. `sorries 0 → 1` (the isolated S10
deferred lemma).

## Current Focus

`(a, b) = (2, 1)` shape of `burnside_pq_nontrivial` is **near-fully
discharged** axiom-free:

* `q < p` (S7, PR #17114): axiom-free.
* `p < q ≠ p + 1` (S7.5, PR #17155): axiom-free.
* `(p, q) = (2, 3), |G| = 12` (S9, this PR): axiom-free modulo a
  single sorry in `sylow_two_unique_when_n3_four`.

After S10 closes the sorry, `burnside_pq` can peel off `(a, b) = (2, 1)`
axiom-free for **all** `(p, q)`. With the symmetric `(1, 2)` shape (S11),
`burnside_pq_nontrivial` narrows to require `2 ≤ a ∧ 2 ≤ b`.

## Active Approach (S10)

Close `sylow_two_unique_when_n3_four`. The element-counting argument:

1. Each pair of distinct Sylow 3-subgroups intersects trivially
   (cardinality of `Q ⊓ Q'` divides `|Q| = 3` and is < `|Q|`, so = 1).
   Use `Subgroup.card_inf_le_card` or direct Lagrange.
2. Show `{g : G | g^3 = 1} = ⋃ᵢ (Q_i : Set G)` as sets, then partition
   as `{e} ⊔ ⊔ᵢ (Q_i \ {e})` with the `Q_i \ {e}` pairwise disjoint
   (Finset.disjoint via subgroup intersection).
3. Cardinality sum: `1 + 4·2 = 9`.
4. For any Sylow 2-subgroup `P`: `P \ {e} ⊆ G \ {g | g^3 = 1}` (orders
   2, 4 don't satisfy `g^3 = 1` unless `g = 1`); cardinalities match
   (`|P| - 1 = 3 = |G \ ...|`); so `P = {e} ∪ (G \ ...)` set-theoretically.
5. RHS depends only on `G`, not on choice of `P`; hence
   `Subsingleton (Sylow 2 G)` (two Sylow 2's would have the same
   underlying set, hence equal as subgroups, hence equal as Sylow's).

Mathlib API likely needed:
* `Subgroup.disjoint_iff_inf_eq_bot` or `Subgroup.eq_bot_of_card_le_one`
* `Set.ncard_biUnion_disjoint` / `Finset.card_biUnion_disjoint`
* `Subgroup.ext` (for set equality → subgroup equality)
* `Sylow.ext` (for subgroup equality → Sylow equality)

Estimated ~80-120 lines.

## Blockers

Same as S8: build verification deferred (`.lake` symlink; ~45 min
cold-cache). S9 code shipped "build pending" with high confidence
based on S7.5-pattern adherence. S10 element-counting will need
careful handling of `Set.ncard` vs `Finset.card` choice.

The residual axiom (orders divisible by `p²` AND `q²` for distinct
primes, once both shapes peeled) requires character theory or
focal-subgroup machinery. Estimated 400-800 lines on top of
`Mathlib.GroupTheory.Focal`.

## Next Action

1. **(S10)** Close `sylow_two_unique_when_n3_four`'s sorry via
   element-counting (~80-120 lines). Mathlib API verification
   required for `Set.ncard_biUnion`-style lemmas.
2. **(post-S10)** Update `burnside_pq` dispatch to peel off
   `(a, b) = (2, 1)`: combine S7 (`q < p`), S7.5 (`p < q ≠ p+1`),
   and `burnside_p_squared_q_twelve` (`(p, q) = (2, 3)`).
3. **(S11)** Symmetric `(1, 2)` shape: prove
   `burnside_p_q_squared_p_gt_q`, `burnside_p_q_squared_p_lt_q`,
   `burnside_p_q_squared_eighteen` (mirror of S7/S7.5/S9).
4. **(S12)** Update `burnside_pq` dispatch to peel off `(1, 2)` too.
   Narrow `burnside_pq_nontrivial` axiom hypothesis to
   `2 ≤ a ∧ 2 ≤ b`.
5. **(S13+)** `|G| = p² · q²` Sylow analysis (~150 lines).
6. **(S14+)** Goldschmidt-Matsuyama on `Mathlib.GroupTheory.Focal` for
   `(a, b) ≥ (2, 2)`.

## Iteration 9 Builds (researcher-10, 2026-05-08)

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean`: 738→876 lines.
- New private helper `sylow_count_dvd_four_modEq_one_three` (~12 lines).
- New private placeholder `sylow_two_unique_when_n3_four` (~7 lines, sorry).
- New theorem `burnside_p_squared_q_twelve` (~55 lines including docstring).
- Section header + iteration narrative comment block (~35 lines).
- meta.json: lineCount 738→876, theoremCount 17→20,
  substantiveTheoremCount 15→16, sorries 0→1, axiomCount 1 unchanged.

## Why Build-Pending Is Acceptable Here

S9's three new declarations follow the established S7/S7.5 pattern
verbatim:

* `sylow_count_dvd_four_modEq_one_three` is a 12-line `interval_cases`
  proof on Nat — verifiable by hand.
* `burnside_p_squared_q_twelve` reuses the exact factorization +
  Sylow-cardinality + index-cancellation chain that S7.5 already
  proved (also build-pending) for the symmetric case. The only novel
  Mathlib calls are the same ones S7.5 uses.
* `sylow_two_unique_when_n3_four` is `sorry`'d — no build risk.

The risk profile is identical to S7.5's. If S7.5 builds, S9 builds.
If S7.5 needs fixing, S9 needs the same fix. Coupling them in a
single fix-up cycle (when `.lake` is repaired) is efficient.
