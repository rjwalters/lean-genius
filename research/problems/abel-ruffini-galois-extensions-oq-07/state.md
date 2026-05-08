# Current State

**Phase**: ACT
**Since**: 2026-05-08T17:00:00Z
**Iteration**: 8 (spec-only)

## S8 (this session, researcher-1, spec-only)

S7 (PR #17114) and S7.5 (PR #17155) are now merged. The `(a, b) = (2, 1)`
shape of `burnside_pq_nontrivial` is discharged axiom-free for **all
non-exceptional `(p, q)`** — `q < p` (S7) or `p < q ≠ p + 1` (S7.5). The
sole remaining sub-case is the exceptional `(p, q) = (2, 3), |G| = 12`,
known classically to require an element-counting argument distinct from
the pure Sylow's-third-theorem dispatch used in S7/S7.5.

**This session's contribution**: a detailed spec for S8 in
`session-8-twelve-spec.md`, capturing:

* Mathematical core: the `n_3 = 4 ⇒ n_2 = 1` argument, via partitioning
  `{g : G | g^3 = 1}` as `{1} ⊔ ⊔_i (Q_i \ {1})` with `Q_i` the 4 Sylow
  3-subgroups (pairwise trivial intersection).
* Lean 4 skeletons for each of 5 helper lemmas + main theorem
  (`sylow_count_dvd_four_modEq_one_three`,
  `sylow_prime_distinct_inter_bot`, `card_pow_three_eq_one_of_n3_four`,
  `sylow_two_unique_when_n3_four`, `burnside_p_squared_q_twelve`).
* Mathlib API inventory (extending Session 6's table with set/Finset
  cardinality lemmas).
* Risk analysis and alternative path via `Subgroup.normalCore` +
  `Equiv.Perm (Fin 4)` solvability.
* Estimated total ~180 Lean lines (revised upward from earlier `~70`
  estimate — set-cardinality reasoning is verbose in Lean).

No Lean code added this iteration: `proofs/.lake` recursive self-symlink
on this host forces ≥45-minute cold-cache builds; deferring implementation
keeps a clean build-pending audit trail. The spec is ready for a future
iteration to implement (or for a researcher on a host with intact
`.lake`).

## Current Focus

`(a, b) = (2, 1)` shape of `burnside_pq_nontrivial` is **partially
discharged**:

* `q < p` (S7, PR #17114): axiom-free.
* `p < q ≠ p + 1` (S7.5, PR #17155): axiom-free.
* `(p, q) = (2, 3), |G| = 12` (S8): umbrella axiom still applies.

After S8 lands, `burnside_pq_nontrivial` will be narrowed to require
`2 ≤ a ∧ 2 ≤ b` (genuinely both ≥ 2), or `¬(a, b) ∈ {(2, 1), (1, 2)}`
once the symmetric `(1, 2)` shape is also discharged.

## Active Approach

Sylow-counting analysis on `|G| = 12 = 2² · 3`:

- **`n_3 = 1`** (Sylow 3-subgroup `Q` unique): `Q.Normal`, discharge via
  `burnside_pq_with_normal_qSylow` with `(a, b) = (2, 1)`. Trivial.
- **`n_3 = 4`** (4 Sylow 3-subgroups): element counting forces `n_2 = 1`.
  - Each pair of distinct Sylow 3-subgroups intersects trivially (prime
    order 3, only proper subgroup is `⊥`).
  - `|⋃_i Q_i| = 1 + 4 · 2 = 9`, so 9 elements satisfy `g^3 = 1`.
  - The remaining 3 elements (with identity) must form a unique Sylow
    2-subgroup `P` (since `|P| = 4 = 1 + 3`, all of `P \ {1}` lies in
    `G \ {g | g^3 = 1}`, and these sizes match).
  - `Subsingleton (Sylow 2 G) ⇒ P.Normal`, discharge via
    `burnside_pq_with_normal_pSylow`.

This is the **classical A₄ case**: when `n_3 = 4`, `G ≅ A₄`, and the
unique Sylow 2-subgroup is the Klein four-group `V₄`.

## Blockers

The residual axiom (orders divisible by `p²` AND `q²` for distinct
primes, once `(2, 1)` and `(1, 2)` shapes are peeled off) requires
either character theory + algebraic-integer hypotheses or transfer +
focal subgroup theory. Mathlib's `Mathlib.GroupTheory.Focal` provides
scaffolding for the character-free route (focal subgroup,
`transferFocal`, `commutator_inf_eq_focalSubgroup`); estimated 200-400
lines on top of this for full Goldschmidt-Matsuyama.

**Build infrastructure**: `proofs/.lake` recursive self-symlink on this
host forces every Docker build to fresh-clone Mathlib (~10-15 min) +
cache get (~10 min). Plan ≥45 min build timeouts for any Lean
verification of S8.

## Next Action

1. **(S8)** Implement `burnside_p_squared_q_twelve` per
   `session-8-twelve-spec.md` (~180 lines). Five helper lemmas + main
   theorem. Build verification ~45 min.
2. **(post-S8)** Augment the main `burnside_pq` dispatch to peel off
   `(a, b) = (2, 1)` axiom-free (combining S7, S7.5, S8). After this,
   the `burnside_pq_nontrivial` axiom can be narrowed to exclude
   `(a, b) = (2, 1)`.
3. **(S8')** Symmetric `(1, 2)` shape: prove
   `burnside_p_q_squared_p_gt_q`, `burnside_p_q_squared_p_lt_q`,
   `burnside_p_q_squared_eighteen` (mirror of S7, S7.5, S8 with `p` and
   `q` swapped). Estimated ~250 lines including helpers.
4. **(S9)** `|G| = p² · q²` Sylow analysis (~150 lines).
5. **(S10+)** Goldschmidt-Matsuyama on top of `Mathlib.GroupTheory.Focal`
   for the `(a, b) ≥ (2, 2)` case.

## Iteration 7 Builds (researcher-5, 2026-05-08, PR #17114)

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean`: 502→614 lines,
  13→15 theorems.
- `sylow_count_eq_one_of_lt_prime` (private helper): if `n ∣ q`
  (q prime), `q < p`, `n ≡ 1 [MOD p]`, then `n = 1`.
- `burnside_p_squared_q_p_gt_q` (~50 lines): pick Sylow p-subgroup,
  show `|P| = p²`, `P.index = q`, derive `n_p = 1`, `P` normal,
  discharge via `burnside_pq_with_normal_pSylow`.

## Iteration 7.5 Builds (PR #17155)

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean`: 614→738 lines,
  15→17 theorems (best estimate; counts may need re-verification post-merge).
- `sylow_count_eq_one_of_lt_prime_pow_two` (private helper): rules out
  `n ∈ {p, p²}` from constraints `n ∣ p²`, `n ≡ 1 [MOD q]`, `p < q`,
  `(p, q) ≠ (2, 3)`.
- `burnside_p_squared_q_p_lt_q` (~50 lines): mirror of `p > q` case
  using Sylow q-subgroup.

**Counts after S7.5 merge**: lineCount 738, theoremCount likely 17,
substantiveTheoremCount likely 17, axiomCount 1 (umbrella unchanged but
`(a, b) = (2, 1)` discharged outside the axiom *except for the
`(p, q) = (2, 3)` exception*), sorries 0.
