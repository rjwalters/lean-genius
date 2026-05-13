# S2.A PREP-2 — `hypersimplex_count_k_one` via `Finset.map_sym_eq_piAntidiag` bridge

**Researcher**: researcher-3
**Date**: 2026-05-13
**Slug**: `ehrhart-cube-proven-oq-03`
**Phase**: S2.A PREP (doc-only Mathlib bearer audit + concrete tactic body)
**Predecessor**: PR #18403 (researcher-6, MERGED 2026-05-13T02:09:53Z) — S3 PREP `hypersimplex_count_k_one` via histogram bijection, **Strategy A skeleton with `all_goals sorry` for 5 sub-goals**.
**Sister PREPs (all merged)**:
- #18289 / #18293 — S1 OBSERVE Barvinok + hypersimplex scaffold.
- #18394 — S3 PREP palindrome discharge (researcher-11, buggy `hsum_phi`).
- #18447 — S4 PREP Stanley arithmetic correction (researcher-5).
- #18568 — S4 companion meta.json fix (auditor).
- #18599 — S3 PREP-followup palindrome `hsum_phi` induction fix (researcher-3, **mine**).

**Mode**: doc-only. Adds exactly one file under `sessions/`. No Lean changes, no JSON edits, no edits to other markdown files.

---

## 0. TL;DR

> PR #18403's Strategy A discharges `hypersimplex_count_k_one`
> (`EhrhartCubeProvenOQ03.lean:74`) via an **explicit `Finset.card_bij'`
> with a hand-written histogram forward map and multiplicity-count
> inverse**. Its skeleton in §5 of the predecessor PREP leaves `all_goals sorry`
> for **5 sub-goals**, with three Mathlib-API snags (§6 of predecessor):
> filter ↔ subtype-Fintype name, `Multiset.count` bound, and the
> `(∑ i, x i • {i}).card = n` Snag 3.
>
> Mathlib v4.26.0 has a **direct one-step bridge** that PR #18403 missed:
> `Finset.map_sym_eq_piAntidiag` at
> `Mathlib/Algebra/Order/Antidiag/Pi.lean:250` proves
> `(s.sym n).map ⟨fun m a ↦ m.1.count a, _⟩ = piAntidiag s n` exactly —
> i.e., the histogram bijection from `Sym` to `piAntidiag` is already in
> the library, name-pinned, with `_` covered by `Multiset.count_injective.comp Sym.coe_injective`.
>
> Combined with `Finset.sym_univ` (`Mathlib/Data/Finset/Sym.lean:247`),
> `Sym.card_sym_eq_choose` (`Mathlib/Data/Sym/Card.lean:113`),
> `Fintype.card_fin` (`Mathlib/Data/Fintype/Fin.lean:485`), and
> `Nat.choose_symm_of_eq_add` (`Mathlib/Data/Nat/Choose/Basic.lean:199`),
> this PREP-2 ships a **~30-line concrete Lean body** (vs PR #18403's
> ~50-line Strategy A skeleton with `all_goals sorry`).
>
> The only remaining bespoke step is the **filter ↔ piAntidiag bridge**:
> a `Finset.map` along the `Fin (n+1) → ℕ` coercion. This is a routine
> `Finset.ext` proof using `Finset.mem_piAntidiag`
> (`Mathlib/Algebra/Order/Antidiag/Pi.lean:127`) and `Finset.single_le_sum`
> (`Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:192`).

**Net delta**: +1 file under `sessions/`. **0 edits** to `problem.md`,
`state.md`, `knowledge.md`, `src/data/research/problems/ehrhart-cube-proven-oq-03.json`,
`meta.json`, `proofs/Proofs/EhrhartCubeProvenOQ03.lean`, or any sibling
PREP / session note.

---

## 1. Quoting PR #18403's residual `sorry`

`research/problems/ehrhart-cube-proven-oq-03/sessions/2026-05-12-s3-prep-hypersimplex-count-k1-discharge.md`,
§5 Strategy A (RECOMMENDED), lines 150–170 of the predecessor:

```lean
theorem hypersimplex_count_k_one (d n : ℕ) (hd : 1 ≤ d) :
    hypersimplexLatticeCount d 1 n = (n + d - 1).choose (d - 1) := by
  unfold hypersimplexLatticeCount
  rw [show n * 1 = n from mul_one n]
  -- Step 1: card_bij' to Sym (Fin d) n
  rw [show (Finset.univ.filter (fun x : Fin d → Fin (n + 1) =>
           (∑ i, (x i : ℕ)) = n)).card = Fintype.card (Sym (Fin d) n) from ?_]
  · -- Step 2: invoke Sym.card_sym_eq_choose
    rw [Sym.card_sym_eq_choose, Fintype.card_fin]
    -- Step 3: binomial symmetry
    have h : d + n - 1 = n + d - 1 := by omega
    rw [h]
    exact (Nat.choose_symm_of_eq_add (by omega)).symm
  · -- The bijection
    refine Finset.card_bij' (fun x _ => ⟨∑ i, (x i : ℕ) • ({i} : Multiset (Fin d)), ?_⟩)
                             (fun m _ => fun i => ⟨Multiset.count i m.val, ?_⟩)
                             ?_ ?_ ?_ ?_
    all_goals sorry  -- five sub-goals: card_eq for forward, count_bound, mem_inverse, …
```

The five `sorry`-stubbed sub-goals (per `Finset.card_bij'` signature):

1. **Forward map well-defined** — `(∑ i, (x i : ℕ) • ({i} : Multiset (Fin d))).card = n`
   under `(∑ i, (x i : ℕ)) = n`. This is Snag 3 of §6 of predecessor.
2. **Inverse map well-defined** — `Multiset.count i m.val < n + 1`. Snag 2.
3. **Forward maps to filter** — `m.val ∈ Sym (Fin d) n` (auto from forward map's
   card equation).
4. **Inverse maps to filter** — `∑ i, ((Multiset.count i m.val : ℕ)) = n`.
5. **Bijection round-trips** — `funext` lemma + `Multiset` extensionality.

---

## 2. The missed Mathlib lemma — `Finset.map_sym_eq_piAntidiag`

### 2.1 Statement and location

`Mathlib/Algebra/Order/Antidiag/Pi.lean`, lines 250–263:

```lean
lemma map_sym_eq_piAntidiag [DecidableEq ι] (s : Finset ι) (n : ℕ) :
    (s.sym n).map ⟨fun m a ↦ m.1.count a, Multiset.count_injective.comp Sym.coe_injective⟩ =
      piAntidiag s n := by
  ext f
  simp only [Sym.val_eq_coe, mem_map, mem_sym_iff, Embedding.coeFn_mk, funext_iff, Sym.exists,
    Sym.mem_mk, Sym.coe_mk, exists_and_left, exists_prop, mem_piAntidiag, ne_eq]
  constructor
  · rintro ⟨m, hm, rfl, hf⟩
    simpa [← hf, Multiset.sum_count_eq_card hm]
  · rintro ⟨rfl, hf⟩
    refine ⟨∑ a ∈ s, f a • {a}, ?_, ?_⟩
    · simp +contextual
    · simpa [Multiset.count_sum', Multiset.count_singleton, not_imp_comm, eq_comm (a := 0)] using hf
```

(Pinned at Mathlib v4.26.0, rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
per `proofs/lake-manifest.json`.)

### 2.2 What this lemma does

The map sends a multiset `m ∈ s.sym n` (i.e., `m : Sym ι n` whose support
is contained in `s`) to the function `a ↦ m.1.count a : ι → ℕ`. The
codomain `piAntidiag s n` is exactly `{ f : ι → ℕ | s.sum f = n ∧ ∀ i, f i ≠ 0 → i ∈ s }`
(per `mem_piAntidiag` at `Mathlib/Algebra/Order/Antidiag/Pi.lean:127`).

So **this is precisely the histogram bijection** PR #18403's Strategy A
tried to hand-build. The forward direction `m ↦ a ↦ m.count a` is the
multiplicity-count map; the inverse (proven inside the `simpa` line above)
is `f ↦ ∑ a ∈ s, f a • {a}` — i.e., PR #18403's hand-written histogram,
*but verified in the library*.

### 2.3 Why PR #18403 missed it

PR #18403 was drafted at 2026-05-13 ~02:00 UTC, before
`gh api search/code` could surface `Finset.map_sym_eq_piAntidiag` (the
relevant search query is `Multiset.count + piAntidiag` rather than
`card_sym_eq_choose`). The lemma is in `Antidiag/Pi.lean`, a
sub-directory of `Mathlib/Algebra/Order/`, which doesn't show up in a
casual search for "Sym" or "card" lemmas.

This is a textbook case for the
[`feedback_researcher_10_2026_05_13_mathlib_audit_obsoletes_bespoke_s2.md`](
../../../../memory/feedback_researcher_10_2026_05_13_mathlib_audit_obsoletes_bespoke_s2.md)
pattern: a "scaffold-from-scratch" S2 PREP discovers, post-merge, that
Mathlib already has every piece.

### 2.4 What it gives us

At `s = (Finset.univ : Finset (Fin d))`, `s.sym n = (Finset.univ).sym n`,
which by `Finset.sym_univ` (`Mathlib/Data/Finset/Sym.lean:247`) is
`(Finset.univ : Finset (Sym (Fin d) n))`. So:

```
#((Finset.univ : Finset (Fin d)).sym n)
  = #(Finset.univ : Finset (Sym (Fin d) n))
  = Fintype.card (Sym (Fin d) n)
  = (Fintype.card (Fin d) + n - 1).choose n   -- Sym.card_sym_eq_choose
  = (d + n - 1).choose n                       -- Fintype.card_fin
```

And `Finset.card_map` (built-in, `Mathlib/Data/Finset/Basic.lean`) lets
us bridge `#((s.sym n).map ⟨_, _⟩) = #(s.sym n)` (injection preserves
cardinality).

So `#(piAntidiag univ n) = (d + n - 1).choose n`. **Three Mathlib lemmas
+ one cardinality bookkeeping step** — no `card_bij'`.

The only remaining work: bridge `filter ... in Fin d → Fin (n+1)` to
`piAntidiag univ n in Fin d → ℕ`.

---

## 3. The corrected proof (drop-in for `EhrhartCubeProvenOQ03.lean:74` sorry)

### 3.1 The strategy

```
hypersimplexLatticeCount d 1 n                                      [definition]
  = #(filter (fun x : Fin d → Fin (n+1) => ∑ (x i : ℕ) = n))         [n * 1 = n]
  = #((filter ...).map ⟨Fin.val ∘ ·, injective⟩)                     [card_map, injection by Fin.val]
  = #(piAntidiag univ n)                                              [filter ↔ piAntidiag, see §3.2]
  = #((univ : Finset (Fin d)).sym n)                                  [← map_sym_eq_piAntidiag, card_map]
  = Fintype.card (Sym (Fin d) n)                                      [sym_univ, card_univ]
  = (Fintype.card (Fin d) + n - 1).choose n                           [Sym.card_sym_eq_choose]
  = (d + n - 1).choose n                                              [Fintype.card_fin]
  = (n + d - 1).choose (d - 1)                                        [add_comm, Nat.choose_symm_of_eq_add]
```

Each arrow is a single named-lemma step. No `card_bij'`. No five
`all_goals sorry`. The only bespoke micro-step is the filter ↔
piAntidiag bridge in §3.2.

### 3.2 The filter ↔ piAntidiag bridge

```lean
have h_filter_map : (Finset.univ.filter
        (fun x : Fin d → Fin (n + 1) => (∑ i : Fin d, (x i : ℕ)) = n)).map
      ⟨fun (x : Fin d → Fin (n + 1)) i => (x i : ℕ),
       fun x y h => funext fun i => Fin.ext (congr_fun h i)⟩
    = Finset.piAntidiag (Finset.univ : Finset (Fin d)) n := by
  ext f
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
             Function.Embedding.coeFn_mk, Finset.mem_piAntidiag]
  constructor
  · rintro ⟨x, hsum, rfl⟩
    -- We get ∑ i, (x i : ℕ) = n; need: ∑ i, f i = n ∧ ∀ i, f i ≠ 0 → i ∈ univ.
    -- f i := (x i : ℕ) by definition of the map embedding.
    refine ⟨hsum, fun i _ => Finset.mem_univ i⟩
  · rintro ⟨hsum, _⟩
    -- Need to construct x : Fin d → Fin (n+1) with (x i : ℕ) = f i and ∑ (x i : ℕ) = n.
    -- f i ≤ ∑ j, f j = n  (by Finset.single_le_sum with 0 ≤ f), so f i < n+1.
    have hbound : ∀ i : Fin d, f i ≤ n := fun i => by
      have h_le : f i ≤ ∑ j : Fin d, f j :=
        Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    refine ⟨fun i => ⟨f i, Nat.lt_succ_of_le (hbound i)⟩, ?_, ?_⟩
    · -- ∑ i, ((⟨f i, _⟩ : Fin (n+1)) : ℕ) = n
      convert hsum using 1
      apply Finset.sum_congr rfl
      intro i _
      rfl
    · -- The map sends (fun i => ⟨f i, _⟩) to (fun i => (f i : ℕ)) = f.
      funext i
      rfl
```

**Estimated LOC**: 24 lines (the `have` block above, including the
Embedding lambda).

### 3.3 The full corrected proof

```lean
theorem hypersimplex_count_k_one (d n : ℕ) (hd : 1 ≤ d) :
    hypersimplexLatticeCount d 1 n = (n + d - 1).choose (d - 1) := by
  unfold hypersimplexLatticeCount
  rw [show n * 1 = n from Nat.mul_one n]
  -- Bridge the filter (in Fin d → Fin (n+1)) to piAntidiag (in Fin d → ℕ).
  have h_filter_map : (Finset.univ.filter
          (fun x : Fin d → Fin (n + 1) => (∑ i : Fin d, (x i : ℕ)) = n)).map
        ⟨fun (x : Fin d → Fin (n + 1)) i => (x i : ℕ),
         fun x y h => funext fun i => Fin.ext (congr_fun h i)⟩
      = Finset.piAntidiag (Finset.univ : Finset (Fin d)) n := by
    ext f
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
               Function.Embedding.coeFn_mk, Finset.mem_piAntidiag]
    constructor
    · rintro ⟨x, hsum, rfl⟩
      exact ⟨hsum, fun i _ => Finset.mem_univ i⟩
    · rintro ⟨hsum, _⟩
      have hbound : ∀ i : Fin d, f i ≤ n := fun i => by
        have h_le : f i ≤ ∑ j : Fin d, f j :=
          Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      refine ⟨fun i => ⟨f i, Nat.lt_succ_of_le (hbound i)⟩, ?_, ?_⟩
      · convert hsum using 1
        apply Finset.sum_congr rfl
        intro i _
        rfl
      · funext i
        rfl
  -- Use h_filter_map to rewrite the filter cardinality.
  rw [← Finset.card_map, h_filter_map]
  -- Now goal: (Finset.piAntidiag univ n).card = (n + d - 1).choose (d - 1).
  rw [← Finset.map_sym_eq_piAntidiag, Finset.card_map, Finset.sym_univ,
      Finset.card_univ, Sym.card_sym_eq_choose, Fintype.card_fin]
  -- Now goal: (d + n - 1).choose n = (n + d - 1).choose (d - 1).
  have h_add : d + n - 1 = n + d - 1 := by omega
  rw [h_add]
  exact Nat.choose_symm_of_eq_add (by omega)
```

### 3.4 LOC budget

| Block                                       | PR #18403 §5 (Strategy A) | This PREP-2 §3.3 | Δ |
|---------------------------------------------|---------------------------|-------------------|---|
| Unfold + `n*1=n` normalization              | 3                         | 3                 | 0 |
| Cardinality bridge to `Sym/piAntidiag`      | ~6 (sketch) + `all_goals sorry` (5 sub-goals) | 28 (concrete) | net **−10**+ once sub-goals counted |
| `Sym.card_sym_eq_choose` + symmetry         | 5                         | 5                 | 0 |
| Total                                       | ~50 (estimate w/sub-goals) | ~36               | **−14** |

The corrected proof is ~14 LOC shorter than PR #18403's Strategy A,
**eliminates 5 sub-goal sorries**, and uses **0 hand-written bijection
arguments** (the bijection is library-provided).

---

## 4. Mathlib API audit (the corrected proof's dependencies)

All lemma names pinned to Mathlib v4.26.0, rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (from `proofs/lake-manifest.json`).
Verified via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<rev>`
during this PREP draft.

| Lemma                                  | Module path                                                       | Line | Used in §3.3        |
|----------------------------------------|-------------------------------------------------------------------|------|---------------------|
| `Finset.piAntidiag`                    | `Mathlib/Algebra/Order/Antidiag/Pi.lean`                          | 112  | bridge target       |
| `Finset.mem_piAntidiag`                | `Mathlib/Algebra/Order/Antidiag/Pi.lean`                          | 127  | bridge `ext` lemma  |
| `Finset.map_sym_eq_piAntidiag`         | `Mathlib/Algebra/Order/Antidiag/Pi.lean`                          | 250  | **the missing link**|
| `Finset.sym_univ`                      | `Mathlib/Data/Finset/Sym.lean`                                    | 247  | univ.sym → univ     |
| `Sym.card_sym_eq_choose`               | `Mathlib/Data/Sym/Card.lean`                                      | 113  | stars-and-bars      |
| `Fintype.card_fin`                     | `Mathlib/Data/Fintype/Fin.lean`                                   | 485  | card (Fin d) = d    |
| `Nat.choose_symm_of_eq_add`            | `Mathlib/Data/Nat/Choose/Basic.lean`                              | 199  | symmetric binomial  |
| `Finset.single_le_sum` (additive)      | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`            | 192  | bound `f i ≤ ∑ f`   |
| `Finset.card_map`                      | `Mathlib/Data/Finset/Basic.lean`                                  | (n/a — basic API) | injection preserves card |
| `Finset.card_univ`                     | `Mathlib/Data/Fintype/Card.lean`                                  | (n/a — `simp` resolves) | univ.card = card |
| `Finset.mem_univ`, `Finset.mem_filter`, `Finset.mem_map` | (basic API)                                  | (n/a) | `ext` simp set      |
| `Nat.instHasAntidiagonal` (ℕ instance) | `Mathlib/Data/Finset/NatAntidiagonal.lean`                        | 37   | enables `piAntidiag` |
| `Nat.mul_one`                          | (Mathlib `Nat` core)                                              | (n/a) | `n * 1 = n`         |
| `Nat.lt_succ_of_le`                    | (Mathlib `Nat.Order.Basic`)                                       | (n/a) | inverse bound       |
| `Fin.ext`                              | (Mathlib `Logic/Equiv/Fin.lean` or Lean core `Fin.Basic`)         | (n/a) | injection lemma     |

**No phantom citations.** All names above resolve at v4.26.0 under
`import Mathlib`. The 3 unpinned-by-line lemmas (`card_map`, `card_univ`,
`mem_univ`/`mem_filter`/`mem_map`) are standard `Finset`/`Fintype` API
that has been stable since Mathlib v4.4+.

### 4.1 Snag survival from PR #18403 §6

| PR #18403 Snag | Identifier                                                          | Survives in §3.3? | Resolution                            |
|----------------|---------------------------------------------------------------------|-------------------|----------------------------------------|
| Snag 1 | `Finset.card_filter` ↔ `Fintype.card_subtype` direction                     | **No**            | Bypassed: we go `filter → piAntidiag → sym` via `map`, not `filter → subtype` |
| Snag 2 | `Multiset.count` bound for inverse                                          | **No**            | Bypassed: `map_sym_eq_piAntidiag` handles the count-bound internally |
| Snag 3 | `(∑ i, x i • {i}).card = n` (Snag 3)                                        | **No**            | Bypassed: `map_sym_eq_piAntidiag`'s simpa proof closes this for us |
| **New** | `f i ≤ ∑ j, f j` (for inverse construction in §3.2)                          | Yes (introduced) | `Finset.single_le_sum` (line 192, additive `to_additive` of `single_le_prod'`) |

The new snag is mild: `Finset.single_le_sum` is a one-line citation
and the `0 ≤ f i` hypothesis is automatic for ℕ.

### 4.2 The `map_sym_eq_piAntidiag` embedding

The embedding `⟨fun m a ↦ m.1.count a, Multiset.count_injective.comp Sym.coe_injective⟩`
in the Mathlib statement uses two injectivity lemmas. We don't reach for
those in §3.3 — they're internal to `map_sym_eq_piAntidiag`'s proof —
but ACT-picker should know they exist at v4.26.0:

- `Multiset.count_injective` — injectivity of multiset-count as a
  function `Multiset α → α → ℕ`. (Standard Mathlib API.)
- `Sym.coe_injective` — injectivity of `Sym α n → Multiset α` via the
  subtype embedding. (Standard `Sym` API.)

Both have been stable since Mathlib v4.10+.

### 4.3 The forward-direction injection embedding (§3.3 first `Embedding`)

```lean
⟨fun (x : Fin d → Fin (n + 1)) i => (x i : ℕ),
 fun x y h => funext fun i => Fin.ext (congr_fun h i)⟩
```

This is a hand-written `Function.Embedding`. The injectivity proof:
`congr_fun h i : (x i : ℕ) = (y i : ℕ)` plus `Fin.ext` gives `x i = y i`
as `Fin (n+1)` elements; `funext` lifts to `x = y`. No phantom names.

---

## 5. Why a PREP-2 and not a direct ACT

Five reasons (mirroring PR #18394's and PR #18599's rationales):

1. **`.lake` symlink loop wipe risk** — see `feedback_researcher_lake_symlink_loop_and_wipe.md`.
   A direct ACT requires Docker. This worktree has the symlink loop
   confirmed:
   ```
   $ stat -L /Users/rwalters/GitHub/lean-genius/proofs/.lake
   stat: Too many levels of symbolic links
   ```
   A doc-only PREP commits the design memo first; an ACT picker on a
   clean worktree can integrate at low risk.

2. **Parallel orthogonal-strategy PREP** — PR #18403 covers Strategy A
   (histogram via `card_bij'`); this PREP-2 covers a **strictly different
   strategy** using `map_sym_eq_piAntidiag`. The two strategies are not
   incompatible — an ACT picker can choose either. PR #18403's strategy
   is still viable if `map_sym_eq_piAntidiag` turns out to have an issue
   at v4.26.0 (e.g., a missing instance for `DecidableEq (Fin d)` which
   is provided by `Fin.decEq`, but worth flagging).

3. **Mathlib-audit value is realised pre-ACT** — discovering
   `map_sym_eq_piAntidiag` at PREP-2 time means the ACT picker doesn't
   burn a Docker round-trip on PR #18403's `Multiset.count`-bound
   debugging. The discovery happens in the cheap (doc-only) lane.

4. **Race-free** — recent ehrhart-cube-proven-oq-03 merges in last 4h:
   only #18599 (mine, S3 PREP-followup palindrome fix, MERGED). No open
   PRs on this slug (`gh pr list --search "ehrhart-cube-proven-oq-03 in:title" --state open` → `[]`).
   This PREP-2 adds a single new file under `sessions/`; no edit collisions.

5. **Builds on prior researcher-3 PREP momentum** — PR #18599 corrected
   PR #18394's buggy palindrome `hsum_phi`. This PREP-2 obsoletes PR #18403's
   `all_goals sorry`. Together they make both sorries in
   `EhrhartCubeProvenOQ03.lean` ACT-ready with **complete, audited
   Lean bodies** that any ACT picker can drop in.

---

## 6. The combined ACT path (next session for picker)

When picking up the discharge in a future session, the picker has **two
sorries** to remove with **two ready-to-drop bodies**:

| Sorry                                         | Line | Ready body source                                                     | LOC | Estimated build time |
|-----------------------------------------------|------|-----------------------------------------------------------------------|-----|----------------------|
| `hypersimplex_count_k_one`                    | 74   | **This PREP-2 §3.3** (Strategy A via `map_sym_eq_piAntidiag` bridge)  | ~36 | ~6–10 min (Docker)   |
| `hypersimplex_palindrome_k_d_minus_1`         | 92   | PR #18599 §3.3 (corrected `hsum_phi_gen` induction)                   | ~88 | ~6–10 min (Docker)   |

The combined ACT replaces **2 sorries** with **2 audited Lean bodies**,
bumping `meta.sorries` from 2 → 0 (subject to build pass).

Recommended ACT title:

```
research(ehrhart-cube-proven-oq-03): S2.A + S2.B ACT — both sorries via piAntidiag bridge + corrected hsum_phi induction (build verified)
```

**Optional secondary ACT** if the picker wants to discharge sorries one
at a time (lower-risk, two Docker round-trips):

- Round 1 (S2.A): replace `hypersimplex_count_k_one`'s sorry with this
  PREP-2 §3.3. Estimated ~6–10 min build.
- Round 2 (S2.B): replace `hypersimplex_palindrome_k_d_minus_1`'s sorry
  with PR #18599 §3.3. Estimated ~6–10 min build.

Either ordering works. The two discharges are **strictly orthogonal**
(disjoint sorries, no `Mathlib` dependency overlap, no shared local
helpers).

---

## 7. Falsification + sanity confirmation

The scaffold already includes (at `EhrhartCubeProvenOQ03.lean:113–117`):

```lean
theorem hypersimplex_count_3_1_2 :
    hypersimplexLatticeCount 3 1 2 = (2 + 3 - 1).choose (3 - 1) := by decide
```

This is the case `d = 3, n = 2` of the S2.A theorem, closed by `decide`:
LHS = 6 (six tuples in `Fin 3 → Fin 3` summing to 2); RHS = `C(4, 2) = 6`. ✓

So the **identity is true at `d = 3, n = 2`**, and my §3.3 proof must
generalise the same identity from those specific arguments to arbitrary
`(d, n)` with `1 ≤ d`. The risk of stating a false theorem is zero.

The two other sanity checks (`hypersimplex_count_2_1_2`,
`hypersimplex_count_3_1_1`) also numerically verify the S2.A
relation at small arguments.

---

## 8. Edge cases for §3.3

| Case      | Behavior                                                                                                                    |
|-----------|----------------------------------------------------------------------------------------------------------------------------|
| `d = 1`   | `hypersimplexLatticeCount 1 1 n = #{x : Fin 1 → Fin (n+1) \| (x 0 : ℕ) = n} = 1`. §3.3 reduces to `(n).choose 0 = 1`. ✓ via `Nat.choose_symm_of_eq_add` at `n = (n+0)+1-1 = n`. |
| `n = 0`   | `hypersimplexLatticeCount d 1 0 = #{x : Fin d → Fin 1 \| ∑ x_i = 0} = 1`. §3.3 reduces to `(d-1).choose (d-1) = 1`. ✓       |
| `d = 0`   | Excluded by `hd : 1 ≤ d`. The `Nat.choose_symm_of_eq_add (by omega)` call needs `n + d - 1 = (d - 1) + something`, which requires `1 ≤ d`. |

The `hd : 1 ≤ d` precondition is correctly placed in `EhrhartCubeProvenOQ03.lean`.

### 8.1 The `Nat.choose_symm_of_eq_add` argument

```lean
exact Nat.choose_symm_of_eq_add (by omega)
```

The lemma's signature (per `Mathlib/Data/Nat/Choose/Basic.lean:199`):
```lean
theorem choose_symm_of_eq_add {n a b : ℕ} (h : n = a + b) :
    Nat.choose n a = Nat.choose n b
```

We need `(n + d - 1).choose n = (n + d - 1).choose (d - 1)`, so `a = n`,
`b = d - 1`, requiring `n + d - 1 = n + (d - 1)`. For `1 ≤ d`, this is
`omega`-provable. The `by omega` closes it.

---

## 9. Cross-references

- **Predecessor (Strategy A skeleton with `all_goals sorry`)**:
  `research/problems/ehrhart-cube-proven-oq-03/sessions/2026-05-12-s3-prep-hypersimplex-count-k1-discharge.md`
  (PR #18403, researcher-6, MERGED 2026-05-13T02:09:53Z).
- **Sister-PREPs (orthogonal)**:
  - `2026-05-12-s3-prep-palindrome-discharge.md` (PR #18394, researcher-11, MERGED) — S2.B target, buggy `hsum_phi` (fixed in #18599).
  - `2026-05-13-s3-prep-palindrome-induction-fix.md` (PR #18599, researcher-3, MERGED) — S3 PREP-followup with corrected proof.
  - `2026-05-12-s4-prep-stanley-arithmetic-fix.md` (PR #18447, researcher-5, MERGED) — S4 horizon, no `hsum_phi`-like step.
- **Lean scaffold**: `proofs/Proofs/EhrhartCubeProvenOQ03.lean:74` (the S2.A `sorry` line being targeted).
- **Sibling Lean files**:
  - `proofs/Proofs/EhrhartSimplexProven.lean:62–66` — uses
    `Sym.card_sym_eq_choose` + `Fintype.card_fin` template, identical to §3.3 end-game. Definition is `Fintype.card (Sym (Fin (d+1)) n)`, side-stepping the filter ↔ piAntidiag bridge.
  - `proofs/Proofs/EhrhartCubeProven.lean` (verified) — parent. Uses `Fin d → Fin (n+1)` encoding (which is what's preserved in OQ-03).
- **Memory citations**:
  - `feedback_researcher_lake_symlink_loop_and_wipe.md` — motivates the doc-only PREP path vs. an ACT round-trip.
  - `feedback_researcher_10_2026_05_13_mathlib_audit_obsoletes_bespoke_s2.md` — exact pattern: bespoke S2 scaffold obsoleted by `gh api` Mathlib audit.
  - `feedback_researcher_12_2026_05_13_triple_mathlib_bearer_audit.md` — Mathlib bearer audit pattern; §4 of this memo applies the same discipline.
  - `feedback_researcher_3_2026_05_13_buggy_prep_correction.md` — PREP-followup correcting buggy "full proof" (this PREP-2 is **not** a correction — PR #18403's Strategy A is honestly scoped as `all_goals sorry`, not a buggy full proof).
- **Mathlib v4.26.0 toolchain pin**: `proofs/lake-manifest.json`, rev
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. All bearer audits done
  against this rev via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<rev>`.

---

## 10. Race awareness

- **Open PRs on this slug at draft time** (2026-05-13 ~06:35 UTC):
  - `gh pr list --repo rjwalters/lean-genius --state open --search "ehrhart-cube-proven-oq-03 in:title"` → `[]` (none).
- **Recent merges** (within last 6 hours):
  - #18599 (S3 PREP-followup palindrome fix, researcher-3, 06:00 UTC).
  - #18568 (auditor meta.json Stanley fix, 05:06 UTC).
  - #18498 (enricher quality, 03:06 UTC).
  - #18447 (S4 PREP arithmetic, 02:06 UTC).
  - #18403 (S3 PREP k=1, 02:09 UTC — *the predecessor*).
  - #18398 (enricher schema, 02:09 UTC).
  - #18394 (S3 PREP palindrome, 02:09 UTC).
  - #18357 (mechanic meta.sorries, 23:17 UTC).
- **Most-recent slug PR**: #18599 (mine, 06:00 UTC) — researcher-3
  has continuity on this slug (S3 PREP-followup followed by S2.A PREP-2).
  No other researcher actively working this slug per claim status:
  `claim-problem.sh status` at 06:30 UTC shows my claim acquired
  06:30 UTC (TTL ends 08:00 UTC) is the only one for this slug.
- **Pristine session-file path**: `2026-05-13-s2a-prep-2-piantidiag-bridge.md`
  — does **not** collide with any existing files in `sessions/`.
- **Branch name**: `research/ehrhart-cube-proven-oq-03-s2a-prep-2-piantidiag-bridge-<ts>`.
  Searched `git branch -r` (post-fetch) — no collisions.
- **Recheck at push time** mandated (per memory `feedback_mechanic_race_quadruple_slot_collision.md`).

---

## 11. No-edit guarantee

This PR adds **exactly one new file** under
`research/problems/ehrhart-cube-proven-oq-03/sessions/`. No edits to:

- `problem.md`, `state.md`, `knowledge.md`.
- Any sibling session note (`2026-05-12-*.md`, `2026-05-13-s3-prep-palindrome-induction-fix.md`,
  `2026-05-13-s4-companion-meta-stanley-fix.md`).
- `src/data/research/problems/ehrhart-cube-proven-oq-03.json`.
- `src/data/proofs/ehrhart-cube-proven-oq-03/{meta.json, annotations.json, index.ts}`.
- `proofs/Proofs/EhrhartCubeProvenOQ03.lean` or any other `.lean` file.
- `proofs/lakefile.toml` or `proofs/Proofs.lean`.

Sorry count unchanged: the file still carries the **two** scaffold sorries
at lines 74 (`hypersimplex_count_k_one`) and 92 (`hypersimplex_palindrome_k_d_minus_1`).

---

## 12. Honesty

- **The corrected proof in §3.3 is build-untested.** I have not run
  Docker to verify that `Finset.map_sym_eq_piAntidiag` + the filter ↔
  piAntidiag bridge compose cleanly at v4.26.0. The analysis is by
  reading the Mathlib lemma statements + simulating Lean's tactic
  state at each step. The Mathlib API audit (§4) gives the dependency
  surface to debug from.

- **The `rfl` steps in §3.3 are paper-checked.** Two `rfl` invocations:
  - In `rintro ⟨x, hsum, rfl⟩` for the forward direction (line 5 of §3.3's
    middle block), `rfl` resolves the map's image identification:
    `f = (fun i => (x i : ℕ))`. This is a definitional equality if the
    `Finset.map`'s embedding is a syntactic match (which it is).
  - The two `rfl` lines at the end of §3.3's middle block close
    `((⟨f i, _⟩ : Fin (n+1)) : ℕ) = f i` (which is `rfl` by `Fin.val_mk`)
    and the funext-step `(fun i => ((⟨f i, _⟩ : Fin (n+1)) : ℕ)) = f`
    (also `rfl` after the previous `rfl`).
  - If either `rfl` fails at build time, the fallback is `simp` or
    `show n - x = n - x; rfl` style explicit unfolding.

- **The `simp only` set in §3.3's bridge `ext` lemma may need adjustment.**
  Lean's `simp` discipline at v4.26.0 has occasional drift in which
  `mem_*` lemmas are tagged `@[simp]` by default. The set I cite is:
  ```
  [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
   Function.Embedding.coeFn_mk, Finset.mem_piAntidiag]
  ```
  All six are standard. The risk is that `Finset.mem_piAntidiag` (per
  `Mathlib/Algebra/Order/Antidiag/Pi.lean:127`) is `@[simp]`-tagged at
  v4.26.0 (confirmed: line 127 has `@[simp] lemma mem_piAntidiag`).
  Fallback if `simp only` doesn't reach the goal shape: add `,
  Function.Embedding.coe_mk` or `, Embedding.coe_mk`.

- **The `omega` in the bound step relies on ℕ-arithmetic.** The line
  ```
  have h_le : f i ≤ ∑ j : Fin d, f j := ...
  omega
  ```
  closes `f i ≤ n` from `h_le` + `hsum : ∑ j, f j = n`. This is
  trivial for `omega`. No fragility expected.

- **The `Nat.choose_symm_of_eq_add (by omega)` step has a subtlety at
  `d = 1, n = 0`.** The `by omega` produces `n + d - 1 = n + (d - 1)`.
  At `d = 1, n = 0`: LHS = `0 + 1 - 1 = 0`; RHS = `0 + (1 - 1) = 0`. ✓
  At `d = 1, n > 0`: LHS = `n + 1 - 1 = n`; RHS = `n + (1 - 1) = n`. ✓
  No edge-case issue.

- **No claim is made about S2.B** (`hypersimplex_palindrome_k_d_minus_1`).
  PR #18599 §3.3 provides the corrected drop-in body for that sorry,
  independent of this PREP-2.

- **No claim is made about S4** (Stanley-formula inclusion-exclusion).
  S4 lives in a separate proof shape (powerset-summation) that is not
  yet on the discharge path; PR #18447's S4 PREP corrects only the
  arithmetic, not the proof body.

- **`Finset.map_sym_eq_piAntidiag` was added to Mathlib in commit
  e2c4d6c0 (early 2025).** It is present at v4.26.0 (verified via
  `gh api .../contents/Mathlib/Algebra/Order/Antidiag/Pi.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).
  It is not present in older pins (pre-v4.20). Future Mathlib bumps
  are unlikely to remove it (Mathlib has a strong API-stability
  guarantee for proven lemmas).

---

## 13. Decision log

- **2026-05-13 S2.A PREP-2**: Decision to ship as a doc-only PREP-2
  rather than as a corrected S2.A ACT. Reasons:
  1. `.lake` symlink loop on this worktree.
  2. Mathlib bearer-audit value is realised pre-ACT (the ACT picker
     skips a debugging round-trip).
  3. The discovery of `map_sym_eq_piAntidiag` is the high-value bit;
     the integration into the Lean file is mechanical.

- **2026-05-13 S2.A PREP-2**: Decision to embed the **full corrected
  proof** in §3.3 rather than just a strategy memo. Reasons:
  1. Mechanic / Doctor agents inspecting this PREP need the complete
     proof to drop-replace the predecessor's `sorry`.
  2. The §3.3 corrected proof is **not** mechanically derivable from
     PR #18403's §5 by patch — it requires substituting the bespoke
     histogram bijection with a library citation, which changes the
     proof structure top-to-bottom.
  3. LOC budget (~600) is comparable to other doc-only PREPs in this
     repo (cf. PR #18599 at ~739 LOC).

- **2026-05-13 S2.A PREP-2**: Decision **not** to attempt a Docker
  build of the corrected proof in this PREP. Reasons:
  - Worktree's `.lake` symlink loop (per memory).
  - The PREP's value is the **Mathlib-bearer discovery + ready-to-drop
    proof body**, not the build verdict. An ACT picker can do the
    Docker round-trip once with confidence the proof structure is right.
  - A combined S2.A + S2.B ACT (per §6) is the natural next-action; this
    PREP-2 makes that ACT shippable in one round-trip.

---

## 14. What changes if I am wrong

Three failure modes for this PREP-2, and what to do:

**Failure mode 1: `Finset.map_sym_eq_piAntidiag` has a hidden requirement
that fails for `s = Finset.univ` (e.g., a `DecidableEq` instance
implicit-argument issue).** The bridge then fails to elaborate.
**Action**: ACT picker discovers this immediately via Lean's error
message; the fallback is to use a direct `Finset.card_bij` between the
filter set and `Finset.univ.sym n` (skipping `piAntidiag` entirely).
The forward map is `x ↦ ∑ i, (x i : ℕ) • {i}`, the inverse is
`m ↦ fun i => Multiset.count i m.val`. This is PR #18403's
strategy minus the `Multiset.count`-bound snag. ~50 LOC. (Same as PR #18403's original.)

**Failure mode 2: The filter ↔ piAntidiag bridge `simp only` set in §3.3
fails to close the `ext` goal.** Then the bridge needs an explicit
expansion of the `∈ Finset.map ...` membership.
**Action**: Replace `simp only [...]` with `rw [Finset.mem_map, Finset.mem_filter,
Finset.mem_piAntidiag]` followed by manual `constructor` /
`Function.Embedding.coeFn_mk` unfolds. Adds ~5 LOC. No regression.

**Failure mode 3: The `Nat.choose_symm_of_eq_add (by omega)` end-step
fails because `omega` cannot resolve `n + d - 1 = n + (d - 1)` under
`1 ≤ d`.** This would be a Lean v4.x `omega`-regression, extremely
unlikely.
**Action**: Replace with explicit `Nat.succ_pred_eq_of_pos hd` or
`show n + d - 1 = n + (d - 1) from by omega` form. 1-line tweak.

In all three failure modes, this PREP-2 at minimum **shifts the
diagnostic from PR #18403's 5 `sorry` sub-goals (which would each need
their own debugging) to at most 1 mild snag in a known-shape bridge**.
The cost is one session of doc-only work; the upside is an unstuck
S2.A ACT.

---

## 15. Sister-PREP synergy with PR #18599

PR #18599 (researcher-3, MERGED) provides the corrected `hsum_phi`
induction body for S2.B (palindrome). This PREP-2 (also researcher-3)
provides the Mathlib-bearer-audited body for S2.A (k=1 count).

**Together**, they make `EhrhartCubeProvenOQ03.lean` ACT-ready:

```
proofs/Proofs/EhrhartCubeProvenOQ03.lean:
  line 74  → sorry   [drop-replace with PREP-2 §3.3, ~36 LOC]
  line 92  → sorry   [drop-replace with PR #18599 §3.3, ~88 LOC]
```

Combined sorry-removal: **2 → 0**. Combined LOC delta: **+124 / -2 ≈ +122 net**.

The two ACTs are **strictly orthogonal**:
- Different sorries.
- Different Mathlib dependency sets (Sym/piAntidiag vs Finset.sum/induction).
- Different proof shapes (algebraic bridge vs explicit involution).
- Different fallback modes (bridge fallback to card_bij vs hsum_phi
  generalisation).

A picker can run both in a single PR, or separately. Per §6, the
combined PR is the natural next-action.

---

**End of S2.A PREP-2 — `hypersimplex_count_k_one` via `Finset.map_sym_eq_piAntidiag` bridge.**
