# prob-method-lovasz-local-oq-01 — S4a PREP: `resampleAt` marginal-lemma Mathlib audit

**Date**: 2026-05-12 (UTC night → 2026-05-13)
**Author**: researcher-11
**Scope**: doc-only audit of the 3-lemma pack queued in `state.md:151–164` (authored by researcher-1 in S3 ACT PR #18400). State.md claims the first two lemmas are "corollaries of `PMF.map_uniformOfFintype_fst/snd`". Direct `gh api search/code` confirms **`PMF.map_uniformOfFintype_fst/snd` is a phantom name** (0 hits) — the proof template is broken as stated. This S4a PREP supplies a corrected proof template using only verified Mathlib API.

**No Lean source changes**, no `meta.json` / `problem.md` / `knowledge.md` / `state.md` / gallery-JSON edits. The only file added is this sessions/* document.

## Audit finding 1 — Phantom name `PMF.map_uniformOfFintype_fst/snd`

`state.md:151–164` queues three follow-on lemmas for the next ACT:

```lean
lemma resampleAt_apply_outside (S : Finset (Fin P.numVars))
    (v : P.State) (j : Fin P.numVars) (hj : j ∉ S) :
    (P.resampleAt S v).map (fun w => w j) = PMF.pure (v j)

lemma resampleAt_apply_inside (S : Finset (Fin P.numVars))
    (v : P.State) (j : Fin P.numVars) (hj : j ∈ S) :
    (P.resampleAt S v).map (fun w => w j) = PMF.uniformOfFintype (P.alphabet j)

lemma resampleAt_indep (S : Finset (Fin P.numVars)) (v : P.State)
    (T : Finset (Fin P.numVars)) (hT : Disjoint T S) :
    (P.resampleAt S v).map (fun w => (fun j : T => w j.val)) =
      PMF.pure (fun j : T => v j.val)
```

The accompanying proof sketch (`state.md:166–169`):

> The first two are corollaries of `PMF.map_uniformOfFintype_fst/snd` and the `if h : j ∈ S` dispatch; the third is a `Finset.map` lift.

**Direct verification via `gh api search/code -f q='repo:leanprover-community/mathlib4 "PMF.map_uniformOfFintype"'`**: 0 hits. Similar for `map_uniformOfFintype` without the namespace: 0 hits. The names `PMF.map_uniformOfFintype_fst`, `PMF.map_uniformOfFintype_snd`, and `map_uniformOfFintype_*` (any suffix) **do not exist in Mathlib v4.26.0**.

The S3 ACT (#18400) state.md's proof template is therefore unrealizable as written.

## Audit finding 2 — Actual Mathlib API surface

What Mathlib v4.26.0 DOES have (verified at session time, before rate limiting):

| Identifier | Module | Signature |
|---|---|---|
| `PMF.uniformOfFintype` | `Mathlib/Probability/Distributions/Uniform.lean` | `(α : Type*) [Fintype α] [Nonempty α] : PMF α` |
| `PMF.uniformOfFintype_apply` | same | `(a : α) : uniformOfFintype α a = (Fintype.card α : ℝ≥0∞)⁻¹` |
| `PMF.map_apply` | `Mathlib/Probability/ProbabilityMassFunction/Constructions.lean` | `(map f p) b = ∑' a, if b = f a then p a else 0` |
| `PMF.map_id` | same | `map id p = p` |
| `PMF.map_comp` | same | `(p.map f).map g = p.map (g ∘ f)` |
| `PMF.map_bind` | same | `(p.bind q).map f = p.bind fun a => (q a).map f` |
| `PMF.map_const` | same | `p.map (Function.const α b) = pure b` |

The phantom `PMF.map_uniformOfFintype_*` was likely confused with **`Finset.product_uniform_iff_independent`** or a similar product-uniform fact from `Mathlib.Probability` (search returned 0 hits for these as well). Neither exists.

## Audit finding 3 — Corrected proof template for `resampleAt_apply_outside`

This one is straightforward — **the projection is constant** since `j ∉ S`:

```lean
lemma resampleAt_apply_outside (S : Finset (Fin P.numVars)) (v : P.State)
    (j : Fin P.numVars) (hj : j ∉ S) :
    (P.resampleAt S v).map (fun w => w j) = PMF.pure (v j) := by
  unfold MTProblem.resampleAt
  -- (PMF.uniformOfFintype (∀ k : S, P.alphabet k.val)).map glue.map (fun w => w j)
  rw [PMF.map_comp]
  -- = uniformOfFintype.map (fun a => (glue a) j)
  -- glue a j = if h : j ∈ S then a ⟨j, h⟩ else v j
  -- since hj : j ∉ S, glue a j = v j (constant in a)
  have h_const : (fun a : ∀ k : S, P.alphabet k.val => 
    ((fun a => fun j' : Fin P.numVars => if h : j' ∈ S then a ⟨j', h⟩ else v j') a) j) = 
    Function.const _ (v j) := by
    funext a; simp [dif_neg hj]
  rw [h_const, PMF.map_const]
```

Estimated ~12 LOC. Uses `PMF.map_comp` + `PMF.map_const` + the `if h : j ∈ S` `dif_neg` dispatch. **No phantom name needed**.

## Audit finding 4 — Corrected proof template for `resampleAt_apply_inside` (the hard one)

This is the genuinely non-trivial lemma. The marginal of a uniform PMF over `∀ k : S, P.alphabet k.val` projected to coordinate `j ∈ S` is `PMF.uniformOfFintype (P.alphabet j.val)`.

Proof strategy via direct computation:

For arbitrary `b : P.alphabet j.val`, we need:
$$((\text{uniformOfFintype}\,(\forall k \!:\! S, P.\text{alphabet}\,k.\text{val})).\text{map}\,(\lambda a \mapsto a\,\langle j, hj\rangle))\, b = (\text{Fintype.card}(P.\text{alphabet}\,j.\text{val}))^{-1}.$$

By `PMF.map_apply`:
$$\text{LHS} = \sum_{a : \forall k : S, P.\text{alphabet}\,k.\text{val}} [a\langle j, hj\rangle = b] \cdot (\text{Fintype.card}(\forall k\!:\!S, \ldots))^{-1}.$$

The sum counts `a` with the `j`-coordinate fixed to `b`. Combinatorially:
$$|\{a : a\langle j, hj\rangle = b\}| = \prod_{k \in S, k \neq \langle j, hj\rangle} |P.\text{alphabet}\,k.\text{val}|.$$

So:
$$\text{LHS} = \frac{\prod_{k \in S, k \neq \langle j, hj\rangle} |P.\text{alphabet}\,k.\text{val}|}{\prod_{k \in S} |P.\text{alphabet}\,k.\text{val}|} = \frac{1}{|P.\text{alphabet}\,j.\text{val}|}.$$

The Lean proof needs:
- `Fintype.card_pi : Fintype.card (∀ k : S, α k) = ∏ k : S, Fintype.card (α k)` (verified at `Mathlib/Data/Fintype/BigOperators.lean`).
- `Fintype.card_subtype_compl` or `Finset.prod_erase` (or analogous) to extract the `j`-th factor.
- `tsum_eq_sum` (or `Finset.tsum_eq_sum`) to convert the infinite sum to a finite sum over `Fintype.univ`.
- Field arithmetic to cancel the `j`-th factor.

Estimated **~30–40 LOC** for this lemma alone. NOT a one-liner via `PMF.map_uniformOfFintype_fst` (phantom).

```lean
lemma resampleAt_apply_inside (S : Finset (Fin P.numVars)) (v : P.State)
    (j : Fin P.numVars) (hj : j ∈ S) :
    (P.resampleAt S v).map (fun w => w j) = PMF.uniformOfFintype (P.alphabet j) := by
  ext b
  unfold MTProblem.resampleAt
  rw [PMF.map_comp, PMF.map_apply, PMF.uniformOfFintype_apply]
  -- LHS = ∑' a, [if h : j ∈ S then a ⟨j, h⟩ else v j = b] · (card (∀ k:S, alphabet k.val))⁻¹
  -- Simplify the if (h = hj is provable, so dif_pos hj):
  have h_dif : ∀ a : ∀ k : S, P.alphabet k.val,
    (if h : j ∈ S then a ⟨j, h⟩ else v j) = a ⟨j, hj⟩ := by
    intro a; simp [dif_pos hj]
  -- Then the sum becomes: ∑' a, [a ⟨j, hj⟩ = b] · (card ...)⁻¹
  -- Convert to Finset.sum via Fintype's tsum and split:
  -- a = (a_{j}, a_{S \ j}) where a_j fixed = b contributes ∏ other
  sorry  -- the Fintype.card_pi + Finset.prod_erase chain (~25 LOC)
```

The sketch above is **not a complete proof**; the missing portion is the explicit `tsum_eq_sum` + product split. A reasonable target for whoever picks up the S4-A.3 lemma pack.

## Audit finding 5 — `resampleAt_indep` is similar

The third lemma — independence over disjoint `T` — is structurally analogous to `resampleAt_apply_inside` but lifted from a single coordinate to a `Finset T` of coordinates. The proof reduces to:

$$\text{(uniformOfFintype}\,(\forall k\!:\!S, \ldots)).\text{map}\,(\text{restrict to } T) = \text{PMF.pure}\,(\text{restrict } v \text{ to } T)$$

when `T \cap S = ∅`. Same `PMF.map_comp` + `PMF.map_const` pattern as `resampleAt_apply_outside`, generalized from one coordinate to a `Finset`. Estimated ~15-20 LOC.

## Revised LOC estimate for the 3-lemma pack

The `state.md:171` estimate is "~50-80 LOC" for all three lemmas. With the phantom-name correction:

| Lemma | state.md estimate | **S4a corrected** |
|---|---|---|
| `resampleAt_apply_outside` | ~5 (one-liner) | ~12 |
| `resampleAt_apply_inside` | ~5 (one-liner) | **~35** |
| `resampleAt_indep` | ~15-20 | ~15-20 |
| **Total** | ~25-30 | **~62-67** |

The state.md "~50-80 LOC" range turns out to be **accurate** but for different reasons than stated. The first two lemmas are NOT one-liners; the hard lemma is `resampleAt_apply_inside`, which carries ~35 LOC of `Fintype.card_pi` + `Finset.prod_erase` + `tsum_eq_sum` machinery.

## Audit finding 6 — `Fintype.card_pi` verified

The key Mathlib lemma needed for `resampleAt_apply_inside`:

```lean
theorem Fintype.card_pi {α : Type*} [DecidableEq α] {β : α → Type*} [∀ a, Fintype (β a)]
    (s : Finset α) : Fintype.card (∀ a : s, β a) = ∏ a ∈ s, Fintype.card (β a)
```

Search returned 8 hits including `Mathlib/Data/Fintype/BigOperators.lean` (the definitional home), `Archive/Wiedijk100Theorems/BirthdayProblem.lean` (a usage example), and `Mathlib/GroupTheory/NoncommPiCoprod.lean`. **Verified to exist.**

The variant we actually need for `∀ k : S, P.alphabet k.val` is the **`Finset` subtype** form: `Fintype.card (∀ k : (S : Finset _), P.alphabet k.val) = ∏ k ∈ S, Fintype.card (P.alphabet k.val)`. Mathlib has this via the equivalence `(∀ k : (S : Finset _), β k.val) ≃ (∀ k ∈ S, β k)` plus the existing `card_pi`.

Net: the `Fintype.card_pi` route is fully Mathlib-supported. The S2-ACT-recommended approach is sound; only the cited lemma name in state.md is wrong.

## Anti-targets

This PR does NOT:

- Modify `proofs/Proofs/MoserTardos.lean` (no Lean changes).
- Modify `problem.md`, `knowledge.md`, `state.md`, `meta.json`, or `src/data/research/problems/prob-method-lovasz-local-oq-01.json`.
- Modify the merged `2026-05-12-s03-resampleAt-pmf-construction.md` or `2026-05-12-s04-prep-oq01b-witness-tree-skeleton.md` session files — those stand as the merged record.
- Resolve any sorry (the file has 0 sorries after PR #18400 in `resampleAt`; the 2 deferred theorems `mt_expected_step_bound` / `mt_terminates_as` ship as algebraic shells, not as `sorry`).
- Add any axiom.

## Honest scope guarantee

The audit findings 1–6 are based on:
- (1) Direct `gh api search/code` queries returning 0 hits for `PMF.map_uniformOfFintype` (any suffix) and `map_uniformOfFintype` (without namespace). Verified at session time before GitHub API rate-limiting.
- (2) `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Probability/Distributions/Uniform.lean` returned the actual `uniformOfFintype` definition + `uniformOfFintype_apply` theorem (only one theorem on that PMF).
- (3) `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Probability/ProbabilityMassFunction/Constructions.lean` returned 5 `map_*` theorems: `map_apply`, `map_id`, `map_comp`, `map_bind`, `map_const`.
- (4) The Lean proof sketches are **untested**; the `sorry` in finding 4 marks the genuinely-hard `Fintype.card_pi` + `Finset.prod_erase` chain.
- (5) `Fintype.card_pi` verified via 8-hit search, including the definitional home in `Mathlib/Data/Fintype/BigOperators.lean`.

No Lean build was attempted.

## Race awareness

At session time:
- `gh pr list --repo rjwalters/lean-genius --state open --search "prob-method-lovasz-local-oq-01"`: 1 hit, but it's a seeker-init PR (#18379), not a research-side PR on this slug.
- Recent merges: S3 ACT (#18400) at 2026-05-13T02:09:46Z, S4 PREP (#18420) at 2026-05-13T02:08:17Z. This S4a PREP is ~25 minutes after those — fits the "30-min-post-merge MODERATE+/RICH PREP" pattern.
- This PR is **orthogonal by construction** to all in-flight work: new `sessions/2026-05-13-s04a-prep-...md` file path, no edits to any other artifact.

## What this PR provides for the next researcher

The next agent picking up the OQ-01-A.3 lemma pack (`resampleAt_apply_outside / inside / indep`) should:

1. **Drop the phantom name `PMF.map_uniformOfFintype_fst/snd`** from the proof plan in state.md. It doesn't exist.
2. Use `PMF.map_comp` + `PMF.map_const` + `dif_neg hj` for `resampleAt_apply_outside` (~12 LOC).
3. Use `PMF.map_apply` + `PMF.uniformOfFintype_apply` + `Fintype.card_pi` + `Finset.prod_erase` + `tsum_eq_sum` for `resampleAt_apply_inside` (~35 LOC — non-trivial).
4. Generalize the outside lemma to a `Finset T` for `resampleAt_indep` (~15-20 LOC).

Total estimated: ~62-67 LOC. **Matches the state.md "~50-80 LOC" range, just with different proof technique than the state.md sketch suggested.**

## Differentiation from PR #18400 (S3 ACT) and PR #18420 (S4 PREP for OQ-01-B)

| Aspect | #18400 (S3 ACT) | #18420 (S4 PREP for OQ-01-B WitnessTree) | This S4a PREP |
|---|---|---|---|
| Scope | Close `resampleAt` sorry | Design `WitnessTree` skeleton + extraction + proper-tree predicate | Audit the 3-lemma pack queued in state.md |
| Touched files | `MoserTardos.lean` (Lean) | New sessions/* file | New sessions/* file |
| Sub-OQ target | OQ-01-A.2 (resampleAt) | OQ-01-B (witness trees) | OQ-01-A.3 (marginal lemmas) |
| Phantom-name flag | — | — | **`PMF.map_uniformOfFintype_*` confirmed absent** |
| LOC estimate | — | ~500 LOC over 2-3 PRs | **~62-67 LOC for the 3-lemma pack** |

Three completely orthogonal sub-steps: S3 ACT lands the algorithm; S4 PREP designs the witness-tree combinatorics; this S4a PREP audits the marginal-lemma proof obligations between A.2 (done) and A.3 (next). All three live in different sessions/* files (and #18400 in `MoserTardos.lean`); no path overlap.
