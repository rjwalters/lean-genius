# S5b PREP — Pre-flight bearer pin verification + skeleton elaboration audit

**Date.** 2026-05-15
**Researcher.** researcher-12
**Mode.** ANALYSIS-ONLY (no `.lean` edits, no `state.md` edits, no JSON
edits, no `meta.json` edits). Doc-only PREP appended as a new session
file.

**Predecessor.** S5 PREP (researcher-3, PR #19179, doc-only,
2026-05-15T00:27:36Z) identified `Sym.equivNatSumOfFintype` at
`Mathlib/Data/Finsupp/Multiset.lean` as the minimum-LOC bearer for the
remaining `hypersimplex_count_k_one` sorry and supplied a ~25-LOC `§3`
proof skeleton with 6 caveats. The skeleton is **drafted but not
build-verified** — PR #19179 is a doc-only PREP awaiting deployer
release (zero-merge interval ~24h at the time of this PREP).

**Trigger.** Per memory pattern
`feedback_researcher_preflight_drafted_proof_after_peer_mechanic_surfaces_unpredicted_fix.md`
(adapted): when a prior session ships a drafted-but-unverified Lean
body in `§3` of a PREP doc and merges are stalled, a doc-only
pre-flight that re-pins each Mathlib bearer at the lake-pinned SHA and
audits the skeleton for elaboration risks is value-additive. This
PREP applies that pattern to PR #19179's `§3` skeleton.

**Findings.** Two concrete corrections to PR #19179's `§3` skeleton
(both fixable by ≤2-LOC delta inside the skeleton itself, not new
strategy):

1. **`Fintype.card_subtype` is not a Mathlib lemma at the lake-pinned
   SHA**. The skeleton's first `rw` invokes
   `Fintype.card_subtype _ (by intro x; simp)` — that name does not
   resolve. The intended lemma is **`Fintype.card_of_subtype`** at
   `Mathlib/Data/Fintype/Card.lean:47`. PR #19179 §3 caveat #1 already
   flagged uncertainty here ("might be `subtype_card`"); this PREP
   pins down the answer.
2. **The outer `.symm` on the `Equiv` composition is the wrong
   direction** for `Fintype.card_congr` in the post-rewrite goal. The
   skeleton has `(e_lift.trans (Sym.equivNatSumOfFintype …).symm).symm`
   which produces `Sym ≃ Subtype1`, while the goal after the `rw`
   needs `Subtype1 ≃ Sym`. Drop the outer `.symm`. This issue is NOT
   in PR #19179's caveat list.

This PREP does NOT discharge the sorry. It supplies a corrected
skeleton (Option A — minimal-edit, recommended) plus two robustness
fallbacks (Option B — explicit `Fintype.card_of_subtype` with full
arguments; Option C — bypass `Fintype.card_of_subtype` entirely via
`Finset.card_filter`-style direct decompose). Conflict-free with both
open same-slug PRs (#19066 S4 ACT palindrome and #19179 S5 PREP
bearer refresh).

---

## §1. Bearer pin re-verification (lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

All 8 bearer entries from PR #19179's §1 audit re-verified by direct
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`
fetch + base64 decode of the file at the lake-pinned SHA recorded in
`proofs/lake-manifest.json`.

| Bearer | Path | Line (PREP claim) | Line (verified) | Verdict |
|---|---|---|---|---|
| `Sym.equivNatSumOfFintype` | `Mathlib/Data/Finsupp/Multiset.lean` | 260 | 259–261 (def header at 259) | ✅ confirmed (1-line tolerance) |
| `Sym.equivNatSum` | `Mathlib/Data/Finsupp/Multiset.lean` | 244 | 243–245 (def header at 243) | ✅ confirmed |
| `Sym.card_sym_eq_choose` | `Mathlib/Data/Sym/Card.lean` | 113 | 113 | ✅ exact |
| `Nat.choose_symm_of_eq_add` | `Mathlib/Data/Nat/Choose/Basic.lean` | 199 | 199 | ✅ exact |
| `Finset.single_le_sum` (additive form) | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean` | 192 | 192 (`@[to_additive single_le_sum]` decorator at 192, `single_le_prod'` body at 193–198) | ✅ confirmed (additive name derived via `to_additive`) |
| **`Fintype.card_subtype`** | `Mathlib/Data/Fintype/Card.lean` | (47, hedged) | **does NOT exist** at this name | ❌ name-drift; correct name is `Fintype.card_of_subtype` (line 47) |
| `Fintype.card_of_subtype` | `Mathlib/Data/Fintype/Card.lean` | 47 | 47 | ✅ exact (this is what the skeleton needs) |
| `Fintype.card_congr` | `Mathlib/Data/Fintype/Card.lean` | 67 | 67 | ✅ exact |
| `Fintype.card_fin` | `Mathlib/Data/Fintype/Card.lean` (re-export) | n/a | re-exported in `Mathlib/Data/Fintype/Pi.lean` and `Mathlib/Data/Fintype/Sigma.lean` | ✅ confirmed available transitively |

**Aside on `Sym.equivNatSumOfFintype`'s explicit-argument shape.** The
file `Mathlib/Data/Finsupp/Multiset.lean` uses

```lean
namespace Sym
variable (α)
variable [DecidableEq α] (n : ℕ)
```

so the def's full signature when called from outside the namespace is

```lean
Sym.equivNatSumOfFintype : (α : Type*) → [DecidableEq α] → (n : ℕ) → [Fintype α] →
    Sym α n ≃ {P : α → ℕ // ∑ i, P i = n}
```

The `(α := Fin d) (n := n)` instantiation in PR #19179's skeleton is
fine — both `[DecidableEq (Fin d)]` (from `Fin.decEq`) and
`[Fintype (Fin d)]` (from `Fin.fintype`) auto-synthesize at v4.26.0.
No issue here.

**Aside on `Sym.card_sym_eq_choose`'s `[Fintype (Sym α k)]` argument.**
The signature is

```lean
theorem card_sym_eq_choose {α : Type*} [Fintype α] (k : ℕ) [Fintype (Sym α k)] :
    card (Sym α k) = (card α + k - 1).choose k
```

The `[Fintype (Sym α k)]` typeclass is auto-synthesized when `α` is
`DecidableEq` + `Fintype` (which `Fin d` is). Same pattern is used by
`EhrhartSimplexProven.simplex_lattice_count`
(`proofs/Proofs/EhrhartSimplexProven.lean:62`) which builds clean on
main — parent-file compile witnesses this bearer per memory pattern
`feedback_researcher_parent_compile_as_bearer_witness`.

---

## §2. Skeleton elaboration audit — two concrete bugs

PR #19179's `§3` skeleton (the `~25 LOC` ACT body for the k=1 sorry)
is reproduced for reference at the bottom of this section. Two
elaboration-time bugs:

### Bug A — `Fintype.card_subtype` does not resolve

The skeleton's first `rw` step:

```lean
rw [show (Finset.univ.filter _).card =
        Fintype.card {x : Fin d → Fin (n + 1) //
          (∑ i : Fin d, (x i : ℕ)) = n} from
          (Fintype.card_subtype _ (by intro x; simp)).symm]
```

invokes `Fintype.card_subtype` — that identifier does not exist at
the lake-pinned SHA. The actual lemmas in
`Mathlib/Data/Fintype/Card.lean` are:

```lean
-- Line 43:
theorem subtype_card {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
    @card { x // p x } (Fintype.subtype s H) = #s

-- Line 47:
theorem card_of_subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x)
    [Fintype { x // p x }] : card { x // p x } = #s
```

(`Fintype.subtype_card` requires the `Fintype.subtype s H` instance
to be threaded explicitly; `Fintype.card_of_subtype` takes the
ambient `[Fintype { x // p x }]` instance.)

**Correct identifier for the skeleton's structure**: **`Fintype.card_of_subtype`**.
The ambient `Fintype` instance for `{x : Fin d → Fin (n + 1) // ∑ x i = n}`
auto-derives from `Fintype (Fin d → Fin (n + 1))` + `DecidablePred`
on the sum equation, so `card_of_subtype` is the natural choice (no
need to plumb a custom Fintype instance).

Independent confirmation that `Fintype.card_subtype` is not a Mathlib
identifier:
`gh search code '"theorem Fintype.card_subtype " repo:leanprover-community/mathlib4 path:Mathlib/Data/Fintype'`
returns 0 hits at this SHA. Only suffixed variants like
`card_subtype_or` (`Mathlib/Data/Fintype/Sum.lean`) and
`card_subtype_eq` exist.

**Fix delta (Bug A)**: 1 character — replace `Fintype.card_subtype`
with `Fintype.card_of_subtype` in the `rw` step.

### Bug B — outer `.symm` flips the equiv to the wrong direction

After the (corrected) `rw` lands, the goal of the inner `have h_card`
becomes:

```
Fintype.card {x : Fin d → Fin (n + 1) // (∑ i : Fin d, (x i : ℕ)) = n}
  = Fintype.card (Sym (Fin d) n)
```

i.e. `Fintype.card Subtype1 = Fintype.card (Sym (Fin d) n)`, where
`Subtype1 := {x // ...}` (LHS) and `Sym := Sym (Fin d) n` (RHS).

The skeleton's closer is:

```lean
exact Fintype.card_congr (e_lift.trans (Sym.equivNatSumOfFintype (Fin d) n).symm).symm
```

Trace the equiv direction:

- `e_lift : Subtype1 ≃ Subtype2` (where `Subtype2 := {P : Fin d → ℕ // ∑ P = n}`)
- `Sym.equivNatSumOfFintype (Fin d) n : Sym ≃ Subtype2`
- `(Sym.equivNatSumOfFintype …).symm : Subtype2 ≃ Sym`
- `e_lift.trans (….symm) : Subtype1 ≃ Sym`
- **outer `.symm`**: `(e_lift.trans (….symm)).symm : Sym ≃ Subtype1`

Then `Fintype.card_congr (Sym ≃ Subtype1) : Fintype.card Sym = Fintype.card Subtype1`,
which is **the symm of the goal**. `exact` does not auto-apply
`Eq.symm`, so this fails to close.

**Without the outer `.symm`**: `e_lift.trans (….symm) : Subtype1 ≃ Sym`,
and `Fintype.card_congr (Subtype1 ≃ Sym) : Fintype.card Subtype1 = Fintype.card Sym`,
which **is** the goal.

**Fix delta (Bug B)**: 5 characters — drop `.symm` from the outer
expression, leaving `(e_lift.trans (Sym.equivNatSumOfFintype (Fin d) n).symm)`.

### Combined fix (Bugs A + B), inline with PR #19179 §3 skeleton

Bug A and Bug B are independent and combine cleanly. The corrected
inner `have h_card` block is:

```lean
have h_card :
    (Finset.univ.filter (fun x : Fin d → Fin (n + 1) =>
        (∑ i : Fin d, (x i : ℕ)) = n)).card
      = Fintype.card (Sym (Fin d) n) := by
  rw [show (Finset.univ.filter _).card =
          Fintype.card {x : Fin d → Fin (n + 1) //
            (∑ i : Fin d, (x i : ℕ)) = n} from
            (Fintype.card_of_subtype _ (by intro x; simp)).symm]    -- Bug A fix
  exact Fintype.card_congr (e_lift.trans (Sym.equivNatSumOfFintype (Fin d) n).symm)
                                                                   -- Bug B fix (drop outer .symm)
```

Net delta from PR #19179 §3 skeleton: **`+1 / −1` chars on Bug A,
`−5` chars on Bug B**. No structural change. No new bearers required.

### Original PR #19179 §3 skeleton (for reference)

```lean
theorem hypersimplex_count_k_one (d n : ℕ) (hd : 1 ≤ d) :
    hypersimplexLatticeCount d 1 n = (n + d - 1).choose (d - 1) := by
  unfold hypersimplexLatticeCount
  simp only [Nat.mul_one]
  let e_lift :
      {x : Fin d → Fin (n + 1) // (∑ i : Fin d, (x i : ℕ)) = n}
        ≃ {P : Fin d → ℕ // ∑ i, P i = n} :=
    { toFun := fun ⟨x, hx⟩ => ⟨fun i => (x i : ℕ), hx⟩
      invFun := fun ⟨P, hP⟩ =>
        ⟨fun i => ⟨P i, by
          have : P i ≤ ∑ j, P j :=
            Finset.single_le_sum (f := P) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          omega⟩, by
          simp only; exact hP⟩
      left_inv := by intro ⟨x, hx⟩; ext i; rfl
      right_inv := by intro ⟨P, hP⟩; rfl }
  have h_card :
      (Finset.univ.filter (fun x : Fin d → Fin (n + 1) =>
          (∑ i : Fin d, (x i : ℕ)) = n)).card
        = Fintype.card (Sym (Fin d) n) := by
    rw [show (Finset.univ.filter _).card =
            Fintype.card {x : Fin d → Fin (n + 1) //
              (∑ i : Fin d, (x i : ℕ)) = n} from
              (Fintype.card_subtype _ (by intro x; simp)).symm]      -- Bug A
    exact Fintype.card_congr (e_lift.trans (Sym.equivNatSumOfFintype (Fin d) n).symm).symm
                                                                    -- Bug B
  rw [h_card, Sym.card_sym_eq_choose, Fintype.card_fin]
  have h_idx : (d + n - 1) = (n + d - 1) := by omega
  rw [h_idx]
  exact Nat.choose_symm_of_eq_add (by omega)
```

---

## §3. Three corrected variants for S5 ACT consumption

### Option A — minimal-edit (recommended)

Apply Bugs A + B fix only. Body identical to PR #19179 §3 except:

```lean
  -- Bug A fix:
  rw [show (Finset.univ.filter _).card = ... from
        (Fintype.card_of_subtype _ (by intro x; simp)).symm]
  -- Bug B fix:
  exact Fintype.card_congr (e_lift.trans (Sym.equivNatSumOfFintype (Fin d) n).symm)
```

**LOC estimate**: ~25 (same as PR #19179 §3).
**Robustness**: Medium. Inherits PR #19179's other 6 caveats (especially
`right_inv` `rfl`-vs-`Subtype.ext`, and `Finset.single_le_sum`'s
named-arg-elaboration shape).

### Option B — explicit `Fintype.card_of_subtype` with full arguments

Same as Option A, but eliminate the `_` placeholder in
`Fintype.card_of_subtype _` to remove an elaboration unknown:

```lean
have h_filter_eq :
    (Finset.univ.filter (fun x : Fin d → Fin (n + 1) =>
        (∑ i : Fin d, (x i : ℕ)) = n)).card
      = Fintype.card {x : Fin d → Fin (n + 1) //
          (∑ i : Fin d, (x i : ℕ)) = n} :=
  (Fintype.card_of_subtype
      (Finset.univ.filter (fun x : Fin d → Fin (n + 1) =>
          (∑ i : Fin d, (x i : ℕ)) = n))
      (fun x => by simp [Finset.mem_filter, Finset.mem_univ])).symm
rw [h_filter_eq]
```

**LOC estimate**: ~30 (Option A + 5 LOC for the explicit `have`).
**Robustness**: Higher. Removes the `_` placeholder in the `Finset` arg
to `card_of_subtype`, and replaces the bare `simp` with explicit lemma
names (`Finset.mem_filter`, `Finset.mem_univ`). At v4.26.0, `simp`
with no args sometimes fails on `Finset.univ.filter ↔` membership;
explicit names avoid that risk.

### Option C — bypass `Fintype.card_of_subtype` via `Finset.card_filter` decomposition

Sidestep the `Fintype.card`/`Finset.card` round-trip entirely. Use
`Finset.card_image_of_injOn` (or `card_bij`) directly between the
filter Finset and a Finset constructed from `Sym (Fin d) n`'s
`Fintype.elems`:

```lean
-- Sketch (~35 LOC, more verbose):
have h_filter_card_eq_sym_card :
    (Finset.univ.filter ...).card = (Finset.univ : Finset (Sym (Fin d) n)).card := by
  rw [Finset.card_univ]
  -- Then card_congr through e_lift.trans equivNatSumOfFintype.symm
  -- via Finset.card_eq_of_equiv_fin or analogous
  sorry
```

**LOC estimate**: ~35.
**Robustness**: Higher (no Fintype-instance-on-subtype synthesis), but
**more verbose** and may surface its own issues with
`Finset.card_eq_of_equiv_fin` arg shape. Recommend ONLY if Options A/B
both fail under Docker.

### Recommendation

Ship **Option A** as the S5 ACT body. It's the minimum delta from
PR #19179's §3 (15-character total fix), and its only additional
risk over the bare PR #19179 §3 is in the inherited 6 caveats — none
of which are introduced by this PREP's two corrections.

If Option A fails on first Docker iter, fall back to **Option B** (10
LOC larger, removes elaboration unknowns).

---

## §4. Hazard log addendum (extends PR #19179 §3 caveats)

PR #19179 §3 already enumerated 6 caveats. This PREP adds findings
that resolve or extend each:

| PR #19179 caveat | This PREP's resolution |
|---|---|
| #1 `Fintype.card_subtype` vs `card_of_subtype` ("might be `subtype_card`; both seem to exist"). Fallback: `Finset.card_filter` directly. | **Resolved**: `Fintype.card_subtype` does not exist; correct name is `Fintype.card_of_subtype` (line 47). `Fintype.subtype_card` (line 43) exists but requires explicit `(Fintype.subtype s H)` instance. Recommend `Fintype.card_of_subtype` per Option A. |
| #2 `equivNatSumOfFintype` is `noncomputable`; verify no `decide` upstream complains. | **Concur**: the four `decide`-based sanity checks in Section III of `EhrhartCubeProvenOQ03.lean` (`hypersimplex_count_2_1_2`, `hypersimplex_count_3_1_1`, `hypersimplex_count_3_2_1`, `hypersimplex_count_3_1_2`) all live in the unchanged Section III post-#19066-merge and don't reference `equivNatSumOfFintype`. No `decide` interference expected. |
| #3 `Finset.single_le_sum` named-arg shape (`f := P`?). | **Concur**: at v4.26.0 the `to_additive`-derived form keeps `f` as an explicit arg in the `single_le_prod'` source signature. Named-arg form `(f := P)` is the safer call; the skeleton's `Finset.single_le_sum (f := P) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)` shape is correct. |
| #4 `right_inv` for `e_lift`: may need `Subtype.ext` / `funext` rather than `rfl`. | **Heightened risk** for Option A. The `right_inv` body `intro ⟨P, hP⟩; rfl` requires `(Subtype.mk (fun i => Subtype.mk (P i) ?bnd).val (?sum hP)) = Subtype.mk P hP` definitionally. The function-projection `(fun i => Fin.val (Fin.mk (P i) _))` reduces to `(fun i => P i)`, which η-reduces to `P` only via Lean 4's `funext`-extensionality. **Recommended fallback**: `intro ⟨P, hP⟩; exact rfl` or `intro ⟨P, hP⟩; rfl` may need `Subtype.ext_iff.mpr ⟨funext (fun i => rfl), rfl⟩`. Pre-stage `intro ⟨P, hP⟩; ext i; rfl` (mirroring the `left_inv` pattern) as a 1-LOC safe substitute. |
| #5 Index shuffle `(d + n - 1) = (n + d - 1)` via `omega`. | **No issue**: `omega` handles linear ℕ identities with abandon. |
| #6 `Nat.choose_symm_of_eq_add` `(n + d - 1) = n + (d - 1)` plumbing for `1 ≤ d`. | **No issue**: trivial `omega` from `hd : 1 ≤ d`. |
| **NEW** Bug B (this PREP): outer `.symm` flips equiv direction. | **Resolved**: drop outer `.symm`. See §2 Bug B for the equiv-direction trace. |

### Net hazard verdict for Option A (post-corrections)

After applying both Option A corrections, the only remaining
medium-risk caveat is #4 (`right_inv` `rfl` vs `ext i; rfl`). Pre-stage
the 1-LOC safe substitute and the S5 ACT should land in a single
Docker iteration. All other caveats either cleared (#1, #2, #5, #6) or
already accounted for in the skeleton (#3).

**Estimated S5 ACT cost post-corrections**: ~25 LOC, 1 Docker
iteration (best case), ≤2 iterations if `right_inv` needs the `ext i; rfl`
substitute on retry.

---

## §5. Cross-PR coordination — three open same-slug PRs

Three open PRs on this slug as of 2026-05-15T03:50Z:

| PR | Type | State | Files modified | Conflict with this PR? |
|---|---|---|---|---|
| **#19066** (researcher author, S4 ACT palindrome) | code+doc | CLEAN, MERGEABLE | `proofs/Proofs/EhrhartCubeProvenOQ03.lean` (+62 -6); `state.md` (+80 -4); `meta.json` (+8 -8); `*.json` tracker (+11 -11) | ❌ no overlap (this PR adds 1 new sessions/ file only) |
| **#19179** (researcher-3, S5 PREP bearer refresh) | doc | CLEAN, MERGEABLE | NEW `sessions/2026-05-14-s5-prep-equivnatsumoffintype-bearer-refresh.md` only | ❌ no overlap (different filename) |
| **#19234** (this PREP, S5b PREP pre-flight) | doc | (about to open) | NEW `sessions/2026-05-15-s5b-preflight-bearer-corrections.md` only | (this PR) |

All three PRs touch **disjoint** sets of files. Merge order does not
matter; any sequencing works.

### Forecast for S5 ACT (next code-shipping iteration)

After **all three** of #19066, #19179, this PREP merge, the S5 ACT
PR should:

1. Pick up Option A (or B) from §3 above.
2. Edit `proofs/Proofs/EhrhartCubeProvenOQ03.lean` lines 75–77: replace
   `sorry` body with the ~25-LOC Option A. Post-#19066-merge file is
   169 LOC; post-S5-ACT will be ~190 LOC.
3. Edit `src/data/proofs/ehrhart-cube-proven-oq-03/meta.json`:
   `sorries: 1` → `0`, `lineCount: 169` → `~190`.
4. Edit `src/data/research/problems/ehrhart-cube-proven-oq-03.json`:
   phase `S4_ACT` → `S5_ACT`, iter `4` → `5`,
   `currentState.{focus,nextAction}`,
   `leanFiles[0].sorryCount: 1` → `0`.
5. Append S5 ACT section to `state.md`.
6. **Status flip eligibility** (per CLAUDE.md): with `sorries: 0` and
   `axiomCount: 0` (file has only `theorem`s and `def`s; no `axiom`
   declarations and no structure-encoded assumptions), the slug
   becomes eligible for `meta.status: formalized` → `verified` and
   `meta.badge: formalized` → `original`. The S5 ACT PR can include
   this flip in the same edit (per PR #19179 §5).

### Sequencing recommendation

S5 ACT must wait for **#19066 to merge** (line numbers in S5 ACT
plan reference post-#19066 file structure: `sorry` at line 75–77,
file 169 LOC). S5 ACT does NOT require #19179 or this PREP to merge
first — those are doc-only PREPs that inform the ACT but don't
provide code dependencies.

### Deployer-stall context

Most-recent `main`-merge as of this PREP draft:
2026-05-14T03:03:38Z (PR #18980 schroeder-bernstein-oq-01). That's
~24h44m of zero merges, matching the
`feedback_researcher_deployer_stall_coordination_prep_pattern` profile
(>12h zero-merge + ≥10 stuck mergeable PRs). All three same-slug PRs
plus dozens of others across the gallery are awaiting deployer
release. This PREP is value-additive in the deployer-stall window
(strictly conflict-free + pins down 2 elaboration bugs that would
otherwise surface only at S5 ACT Docker time, costing 1 extra
iteration each).

---

## §6. Conflict-free scope statement (this PR)

This PR is doc-only and conflict-free with both open same-slug PRs.

* **Adds**: 1 new file —
  `research/problems/ehrhart-cube-proven-oq-03/sessions/2026-05-15-s5b-preflight-bearer-corrections.md`
  (this file).
* **Does NOT touch**: `state.md`, `problem.md`, `knowledge.md`, the
  JSON tracker `src/data/research/problems/ehrhart-cube-proven-oq-03.json`,
  the gallery `src/data/proofs/ehrhart-cube-proven-oq-03/meta.json`,
  any `proofs/*.lean` file.
* **Does NOT discharge** the k=1 sorry. That is queued for S5 ACT
  in a future iteration (post-#19066-merge).
* **Does NOT make a scope-decision** on Option A (continue
  hypersimplex) vs Option B (spin off Barvinok as `oq-05`). The
  corrected skeleton variants in §3 are *option-symmetric*: if Option
  A is chosen by future triage, ship Option A from §3 above; if Option
  B is chosen, the corrections document the hypersimplex track's k=1
  ACT cost as ~25 LOC + 1 Docker iter for whatever new slug owns
  hypersimplex.

---

## §7. Decision Log

* **2026-05-15 S5b PREP (researcher-12)**: Wrote a doc-only
  pre-flight PREP rather than attempting S5 ACT directly. Reason:
  S5 ACT depends on PR #19066 (still OPEN, deployer stall ~24h44m)
  for the post-palindrome line numbers. Pre-flight pins down two
  elaboration bugs in PR #19179 §3 skeleton (`Fintype.card_subtype`
  → `Fintype.card_of_subtype`; outer `.symm` direction) that would
  cost 2 extra Docker iterations at S5 ACT time. Per
  `feedback_researcher_preflight_drafted_proof_after_peer_mechanic_surfaces_unpredicted_fix`
  (adapted: trigger is deployer-stall + drafted-but-unverified §3
  skeleton, not peer-mechanic-PR-surfaces-fix).

* **2026-05-15 S5b PREP (researcher-12)**: Recommend Option A
  (minimal-edit) over Options B (explicit args) and C (bypass
  `card_of_subtype` via direct `card_eq` decomposition). Reason:
  Option A is +15 chars total off PR #19179 §3 (1-char Bug A fix,
  −5-char Bug B fix); Options B and C trade LOC for marginal extra
  robustness only after Option A demonstrably fails. Defer fallbacks
  to S5 ACT contingency.

* **2026-05-15 S5b PREP (researcher-12)**: Recommend NOT bundling
  this PREP's findings into PR #19179 (which is currently in
  deployer-stall queue). Reason: any rewrite of #19179 would orphan
  its own deployer queue position and add review surface; a fresh
  PREP that explicitly cross-references and corrects is cleaner per
  `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern`
  and `feedback_researcher_deployer_stall_coordination_prep_pattern`.

* **2026-05-15 S5b PREP (researcher-12)**: Did NOT run Docker
  build to verify Option A. Reason: per the slug's recurring
  worktree `proofs/.lake` self-referential-symlink trap (documented
  at the head of this slug's state.md), local Docker builds
  re-fresh-clone Mathlib (~30–45 min cold). Bearer pin verification
  via `gh api` + base64 decode at the lake-pinned SHA is sufficient
  for a doc-only pre-flight; Docker verification is the S5 ACT PR's
  responsibility.
