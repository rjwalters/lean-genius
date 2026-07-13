# S5 PREP — `hypersimplex_count_k_one` via `Sym.equivNatSumOfFintype`

**Date.** 2026-05-14
**Researcher.** researcher-3
**Mode.** ANALYSIS-ONLY (no `.lean` edits, no `state.md` edits, no JSON
edits). Doc-only PREP appended as a new session file. Conflict-free
with the open S4 ACT PR (#19066) which edits the parent `.lean` file +
`state.md` + 2 JSON trackers.

**Predecessor.** S3 PREP (researcher-4, 2026-05-13, merged into the
state.md narrative under §"Refined proof outline — `hypersimplex_count_k_one`"
at the head of this slug's state.md). That PREP estimated the k=1
sorry at ~70–100 LOC requiring a hand-rolled `{x : Fin d → Fin (n+1) //
∑ x_i = n} ≃ Sym (Fin d) n` bijection.

**This PREP.** Identifies a Mathlib v4.26.0 lemma that the S3 PREP
audit missed: **`Sym.equivNatSumOfFintype`** at
`Mathlib/Data/Finsupp/Multiset.lean:260` provides the entire bijection
to `{P : α → ℕ // ∑ i, P i = n}` for free, reducing the ACT to a
trivial `Fin (n+1) ↔ ℕ` coercion bridge. New estimate: **~25–40 LOC**
(roughly 2× shorter than S3 PREP's outline, with one fewer hand-rolled
bijection).

This PREP does NOT discharge the sorry. It refreshes the bearer audit
with the missed lemma, sketches the revised proof skeleton with
file:line pins at the lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
and forecasts the S5 ACT body for a future iteration.

---

## §1. Bearer audit refresh — what S3 PREP missed

S3 PREP's bearer table (state.md lines 200–208) listed primary
candidates `Sym.card_sym_eq_choose` (line 113 of `Mathlib/Data/Sym/Card.lean`)
and `Sym.card_sym_fin_eq_multichoose` (line 94), and noted under §"Refined
proof outline — `hypersimplex_count_k_one`":

> **Bijection** `{x : Fin d → Fin (n + 1) | ∑ x_i = n} ≃ Sym (Fin d) n` —
> the "x_i = multiplicity of i" map. **This is NOT a one-liner in Mathlib**;
> it must be constructed (likely via `Finset.card_nbij'` between the filter
> and the `Sym` finset, modulo the `Multiset.count`-style API). Estimated ~50 LOC.

That assessment is **wrong at the lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`**.
The bijection IS in Mathlib, just not in `Mathlib/Data/Sym/`. It
lives in `Mathlib/Data/Finsupp/Multiset.lean`:

| Lemma | Path | Line | Signature |
|---|---|---|---|
| **`Sym.equivNatSumOfFintype`** (primary, missed) | `Mathlib/Data/Finsupp/Multiset.lean` | **260** | `noncomputable def equivNatSumOfFintype [Fintype α] : Sym α n ≃ {P : α → ℕ // ∑ i, P i = n}` |
| `Sym.equivNatSum` (more general, requires DecidableEq) | `Mathlib/Data/Finsupp/Multiset.lean` | 244 | `Sym α n ≃ {P : α →₀ ℕ // P.sum (fun _ ↦ id) = n}` |
| `Sym.card_sym_eq_choose` (final cardinality) | `Mathlib/Data/Sym/Card.lean` | 113 | `[Fintype α] (k : ℕ) [Fintype (Sym α k)] : Fintype.card (Sym α k) = (Fintype.card α + k − 1).choose k` |
| `Nat.choose_symm_of_eq_add` (coeff swap) | `Mathlib/Data/Nat/Choose/Basic.lean` | 199 | `n = a + b → Nat.choose n a = Nat.choose n b` |
| `Finset.single_le_sum` (≤ bound) | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean` | 192 | `(∀ i ∈ s, 0 ≤ f i) → a ∈ s → f a ≤ ∑ x ∈ s, f x` (additive form via `to_additive`) |
| `Fintype.card_subtype` / `Fintype.card_of_subtype` | `Mathlib/Data/Fintype/Card.lean` | 47 | `card { x // p x } = #s` when `s = Finset.filter p Finset.univ` |
| `Fintype.card_congr` | `Mathlib/Data/Fintype/Card.lean` | 67 | `α ≃ β → Fintype.card α = Fintype.card β` |
| `Fintype.card_fin` | `Mathlib/Data/Fintype/Card.lean` (re-export) | n/a | `Fintype.card (Fin n) = n` |

All entries verified by directly fetching
`https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/<path>`
(the `gh api` lake-pinned route). No path drift; no signature drift;
no name drift versus mainline.

**Why S3 PREP missed it.** `equivNatSumOfFintype` lives in the
`Finsupp` directory, not the `Sym` directory; its name does not
appear in `gh search code 'Sym.equivNat*'` results because the file
opens `namespace Sym` from inside `Finsupp/Multiset.lean`. S3 PREP's
bearer audit was Sym-namespaced (`gh search code Sym.card_sym_*`), so
it found the cardinality lemma but not the underlying bijection.

**Verdict.** The hypersimplex track is bearer-clean for the k=1 case
*more strongly* than S3 PREP estimated — the "non-trivial Sym
bijection construction" that S3 PREP flagged as the dominant ACT cost
is in fact a one-line application of an existing library equiv.

---

## §2. Reframed S5 ACT strategy

The hypersimplex's k=1 sorry is currently:

```lean
-- proofs/Proofs/EhrhartCubeProvenOQ03.lean:75–77
theorem hypersimplex_count_k_one (d n : ℕ) (hd : 1 ≤ d) :
    hypersimplexLatticeCount d 1 n = (n + d - 1).choose (d - 1) := by
  sorry
```

where

```lean
def hypersimplexLatticeCount (d k n : ℕ) : ℕ :=
  (Finset.univ.filter
      (fun x : Fin d → Fin (n + 1) => (∑ i : Fin d, (x i : ℕ)) = n * k)).card
```

The S3 PREP sketch (now superseded) involved hand-rolling a bijection
from this filter to `Sym (Fin d) n`. The revised S5 ACT plan has **three steps**:

### Step A — bridge `Finset.filter` cardinality to a subtype card

Reduce the LHS to a `Fintype.card`:

```
hypersimplexLatticeCount d 1 n
  = #{x : Fin d → Fin (n+1) // ∑ (x i : ℕ) = n*1}    -- by Fintype.card_subtype / card_of_subtype
  = #{x : Fin d → Fin (n+1) // ∑ (x i : ℕ) = n}      -- by `n*1 = n` (Nat.mul_one)
```

Mathlib bearer: `Fintype.card_of_subtype` at
`Mathlib/Data/Fintype/Card.lean:47`. Routine.

### Step B — bridge the Fin codomain to ℕ codomain (~5 LOC)

Construct the equiv

```
e_lift : {x : Fin d → Fin (n+1) // ∑ (x i : ℕ) = n}
        ≃ {P : Fin d → ℕ        // ∑ i, P i = n}
```

- **toFun** `⟨x, hx⟩ ↦ ⟨fun i => (x i : ℕ), hx⟩` — coerce each
  `Fin (n+1)` to its underlying `ℕ`. Sum-preservation is by definition.
- **invFun** `⟨P, hP⟩ ↦ ⟨fun i => ⟨P i, ?bnd⟩, ?sum⟩` where
  `?bnd : P i < n + 1` is `Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))` rewritten via `hP`. Sum-preservation by definition.
- **left_inv / right_inv** are `Fin.ext`-pointwise rfl.

Mathlib bearer for the bound: `Finset.single_le_sum` at
`Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:192` — yields
`P i ≤ ∑ x ∈ s, P x` from `∀ x ∈ s, 0 ≤ P x` (vacuous on `ℕ`) and
`i ∈ s`. Combined with `hP : ∑ = n` and `Nat.lt_succ_of_le` we get
`P i < n + 1`. ~3 LOC.

### Step C — compose with `Sym.equivNatSumOfFintype.symm` and finish

```
e_full : Sym (Fin d) n
       ≃ {P : Fin d → ℕ // ∑ i, P i = n}              -- equivNatSumOfFintype
       ≃ {x : Fin d → Fin (n+1) // ∑ (x i : ℕ) = n}    -- e_lift.symm
```

Then:

```
hypersimplexLatticeCount d 1 n
  = Fintype.card {x // ...}                -- Step A
  = Fintype.card (Sym (Fin d) n)           -- Fintype.card_congr e_full.symm
  = (Fintype.card (Fin d) + n - 1).choose n  -- Sym.card_sym_eq_choose
  = (d + n - 1).choose n                    -- Fintype.card_fin
  = (n + d - 1).choose n                    -- Nat.add_comm or rfl-via-omega
  = (n + d - 1).choose (d - 1)              -- Nat.choose_symm_of_eq_add (n + d - 1 = n + (d - 1) for hd : 1 ≤ d)
```

The last step is `Nat.choose_symm_of_eq_add (h : (n + d - 1) = n + (d - 1))`,
which holds by `omega` from `hd : 1 ≤ d`. Note `EhrhartSimplexProven.simplex_lattice_count`
(line 62–67 of `proofs/Proofs/EhrhartSimplexProven.lean`) uses exactly
this final-step pattern.

### Estimated LOC

| Step | LOC | Notes |
|---|---|---|
| A — `card_of_subtype` setup | 3 | `Fintype.card_of_subtype Finset.univ`-style |
| B — `e_lift` construction | 12 | toFun (1) + invFun (3) + left_inv (3) + right_inv (3) + struct boilerplate (2) |
| C — composition + finish | 10 | three `rw`s + `Nat.choose_symm_of_eq_add` + `omega` for index-shuffle |
| Total | **~25** | optimistic; ≤ **~40** with margin for `simp` / `Fin.ext` plumbing |

---

## §3. Concrete proof skeleton (NOT shipped — for S5 ACT reference)

```lean
theorem hypersimplex_count_k_one (d n : ℕ) (hd : 1 ≤ d) :
    hypersimplexLatticeCount d 1 n = (n + d - 1).choose (d - 1) := by
  -- Step A: rewrite n * 1 to n in the filter.
  unfold hypersimplexLatticeCount
  simp only [Nat.mul_one]
  -- LHS now: #(Finset.univ.filter (fun x => ∑ (x i : ℕ) = n))
  -- Step B: build the Fin/ℕ subtype equiv.
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
  -- Compose with Sym.equivNatSumOfFintype.symm to land in Sym (Fin d) n.
  have h_card :
      (Finset.univ.filter (fun x : Fin d → Fin (n + 1) =>
          (∑ i : Fin d, (x i : ℕ)) = n)).card
        = Fintype.card (Sym (Fin d) n) := by
    rw [show (Finset.univ.filter _).card =
            Fintype.card {x : Fin d → Fin (n + 1) //
              (∑ i : Fin d, (x i : ℕ)) = n} from
              (Fintype.card_subtype _ (by intro x; simp)).symm]
    exact Fintype.card_congr (e_lift.trans (Sym.equivNatSumOfFintype (Fin d) n).symm).symm
  rw [h_card, Sym.card_sym_eq_choose, Fintype.card_fin]
  -- Goal: (d + n - 1).choose n = (n + d - 1).choose (d - 1)
  have h_idx : (d + n - 1) = (n + d - 1) := by omega
  rw [h_idx]
  exact Nat.choose_symm_of_eq_add (by omega)
```

**Caveats / hazards (S5 ACT to verify on Docker):**

1. **`Fintype.card_subtype` vs `Fintype.card_of_subtype`.** Both are
   in `Mathlib/Data/Fintype/Card.lean`; the former (line 43) needs the
   `Fintype.subtype` instance threaded through, the latter (line 47)
   takes a `[Fintype { x // p x }]` and gives the equality. The skeleton
   above uses `Fintype.card_subtype` directly — verify that name resolves
   (might be `subtype_card`; both seem to exist). Fallback: `Finset.card_filter`
   directly relating filter-card to a subtype-card via `Fintype`.
2. **`equivNatSumOfFintype` is `noncomputable`.** That is fine for
   cardinality reasoning (`Fintype.card_congr` doesn't need
   computability). Confirm no `decide` upstream call complains
   (the four `decide`-based sanity checks in §III of the file are
   independent and don't use this theorem).
3. **Step B `Finset.single_le_sum` invocation shape.** The lemma
   wants `(hf : ∀ i ∈ s, 0 ≤ f i)` and `(h : a ∈ s)`. On `ℕ`, the
   `0 ≤` hypothesis is vacuous (`Nat.zero_le _`). At v4.26.0 verify
   that the named-arg form `(f := P)` is needed (the `to_additive`-derived
   lemma sometimes elaborates with `f` as a non-implicit argument).
4. **`right_inv` for `e_lift`.** The witness is `⟨P, hP⟩ ↦ ⟨P, hP⟩`
   morally, but the trip through `Fin.mk` and `Fin.val` may need
   `Fin.ext` / `funext` rather than `rfl`. If `rfl` fails, try
   `intro ⟨P, hP⟩; ext i; rfl` or `intro ⟨P, hP⟩; rfl` with a
   `Subtype.ext` wrapper.
5. **Index shuffle `(d + n - 1) = (n + d - 1)`.** `omega` should
   close this trivially. If `omega` stalls (it shouldn't on this pair),
   fallback is `Nat.add_comm` after splitting via `Nat.sub_add_cancel`.
6. **`hd : 1 ≤ d` plumbing for `Nat.choose_symm_of_eq_add`.** The
   hypothesis to `choose_symm_of_eq_add` is `(n + d - 1) = n + (d - 1)`,
   which needs `1 ≤ d` to discharge `(d - 1) + 1 = d`. `omega` from `hd`.

---

## §4. Why S3 PREP's stars-and-bars alternative is no longer needed

S3 PREP also sketched an alternative ~80 LOC route: build an injection
`{x : ∑ = n} → {S : Finset (Fin (n + d - 1)) | #S = d - 1}` via the
prefix-sum map, then conclude via `Finset.card_powersetCard`. With
`Sym.equivNatSumOfFintype` available, this alternative is strictly
worse (more LOC, more invariants to maintain, no expected payoff in
generality since both routes specialize to the same cardinality).

**Recommendation.** S5 ACT should NOT pursue the stars-and-bars
alternative. The `equivNatSumOfFintype` path is the minimum-LOC
formalization on Mathlib v4.26.0.

---

## §5. Cross-PR coordination — open S4 ACT (PR #19066)

The open PR **#19066** (`research/ehrhart-cube-proven-oq-03-s4-act-palindrome-1778770829`,
created 2026-05-14T15:01:46Z, +155 −29 across 4 files) discharges the
*other* sorry in the parent file, namely
`hypersimplex_palindrome_k_d_minus_1` at lines 89–91. After it
merges:

| File | Pre-merge | Post-merge |
|---|---|---|
| `proofs/Proofs/EhrhartCubeProvenOQ03.lean` | 119 LOC, 2 sorries | 169 LOC, 1 sorry |
| `src/data/proofs/ehrhart-cube-proven-oq-03/meta.json` | sorries: 2 | sorries: 1 |
| `src/data/research/problems/ehrhart-cube-proven-oq-03.json` | phase: S3_PREP, iter 3 | phase: S4_ACT, iter 4 |
| `research/problems/ehrhart-cube-proven-oq-03/state.md` | (290 lines) | (~370 lines) +1 Session 4 section |

The k=1 sorry stays at line **75–77** unchanged through PR #19066's
merge. The skeleton in §3 above will apply verbatim post-merge.

**Forecast for the S5 ACT PR (next iteration):**

- Touches `proofs/Proofs/EhrhartCubeProvenOQ03.lean`: replace the
  `sorry` body at line 75–77 with the ~25-LOC skeleton (file LOC
  goes 169 → ~190).
- Touches `src/data/proofs/ehrhart-cube-proven-oq-03/meta.json`:
  `sorries` 1 → 0, `lineCount` 169 → ~190.
- Touches `src/data/research/problems/ehrhart-cube-proven-oq-03.json`:
  phase `S4_ACT` → `S5_ACT`, iter `4` → `5`, `currentState.focus`,
  `leanFiles[0].sorryCount` 1 → 0.
- Touches `research/problems/ehrhart-cube-proven-oq-03/state.md`:
  +1 new Session 5 section.
- Build forecast: a single Docker iteration; ~7745 jobs (within
  ±5 of the S4 ACT job count of 7743).
- **Status flip eligibility**: with both sorries discharged and the
  file at 0 axioms, this slug becomes eligible for the
  `proofs/Proofs/EhrhartCubeProvenOQ03.lean` `meta.status` flip
  `formalized` → `verified` and `meta.badge` flip `formalized` →
  `original`. Per CLAUDE.md the `axiomCount` is verified to be 0 (the
  file has only `theorem`s and `def`s; no `axiom` declarations and no
  structure-encoded assumptions). The S5 ACT PR can include this flip
  in the same edit.

**Sequencing recommendation.** Wait for PR #19066 to merge before
opening the S5 ACT PR. Reason: both edit the same `.lean` file, both
edit the same `state.md`, both edit the same two JSON trackers. While
the *line ranges* don't conflict (PR #19066 edits line 79–91; S5 ACT
edits line 75–77 + appends new sections to docs), GitHub's auto-merge
will likely flag conflicts on the `state.md` and JSON files if both
land out-of-order. Pinning S5 ACT post-#19066 is the safe sequencing.

---

## §6. Conflict-free scope statement (this PR)

This PR is doc-only and conflict-free with the open PR #19066:

* **Adds**: 1 new file —
  `research/problems/ehrhart-cube-proven-oq-03/sessions/2026-05-14-s5-prep-equivnatsumoffintype-bearer-refresh.md`
  (this file).
* **Does NOT touch**: `state.md`, `problem.md`, `knowledge.md`, the
  JSON tracker `src/data/research/problems/ehrhart-cube-proven-oq-03.json`,
  the gallery `src/data/proofs/ehrhart-cube-proven-oq-03/meta.json`,
  any `proofs/*.lean` file.
* **Does NOT discharge** the k=1 sorry. That is queued for S5 ACT
  in a future iteration.
* **Does NOT make a scope-decision** on Option A (continue
  hypersimplex) vs Option B (spin off Barvinok as `oq-05`). The
  refined skeleton in §3 above is *option-symmetric*: if Option A is
  chosen by future triage, the skeleton becomes the S5 ACT body
  verbatim; if Option B is chosen, the skeleton documents the
  hypersimplex track's k=1 ACT cost as ~25 LOC + 1 Docker iter for
  whatever new slug owns hypersimplex.

---

## §7. Decision Log

* **2026-05-14 S5 PREP (researcher-3)**: Identified
  `Sym.equivNatSumOfFintype` at `Mathlib/Data/Finsupp/Multiset.lean:260`
  as the minimum-LOC bearer for `hypersimplex_count_k_one`.
  Rationale: directly encodes the bijection
  `Sym α n ≃ {P : α → ℕ // ∑ P = n}` that S3 PREP planned to
  hand-roll. Reduces estimated ACT body from ~80 LOC to ~25 LOC.

* **2026-05-14 S5 PREP (researcher-3)**: Wrote a doc-only PREP
  rather than attempting the S5 ACT. Reason: an open S4 ACT PR
  (#19066) edits the same parent `.lean` + `state.md` + 2 JSON
  trackers, so any S5 ACT would land in conflict; the PREP de-risks
  S5 ACT (post-#19066-merge) by pinning the API with file:line
  citations + a concrete skeleton + hazard list. Per the cross-PR
  coordination memory pattern.

* **2026-05-14 S5 PREP (researcher-3)**: Recommend NOT pursuing
  the stars-and-bars alternative (S3 PREP's ~80 LOC backup). Reason:
  with `equivNatSumOfFintype` available, stars-and-bars is strictly
  worse on every axis (more LOC, more invariants, no generality
  payoff). Future S5 ACT should ship the `equivNatSumOfFintype`
  skeleton.
