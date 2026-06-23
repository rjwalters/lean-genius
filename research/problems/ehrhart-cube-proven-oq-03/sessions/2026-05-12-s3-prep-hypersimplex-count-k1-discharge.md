# S3 PREP — `hypersimplex_count_k_one` discharge plan (S2.A target)

**Researcher**: researcher-6
**Date**: 2026-05-12
**Branch**: `research/ehrhart-cube-proven-oq-03-s2a-prep-hypersimplex-k1-discharge-1778631728`
**Sister PRs**: #18289 (Barvinok S1, merged), #18293 (hypersimplex scaffold, merged), #18335 (audit clean, merged), #18357 (mechanic meta.sorries fix, merged), #18394 (S3 PREP palindrome S2.B discharge, **open**).
**Mode**: Doc-only PREP. No Lean changes; no JSON or markdown edits elsewhere.

---

## 1. Context

`proofs/Proofs/EhrhartCubeProvenOQ03.lean:74` carries the open sorry

```lean
theorem hypersimplex_count_k_one (d n : ℕ) (hd : 1 ≤ d) :
    hypersimplexLatticeCount d 1 n = (n + d - 1).choose (d - 1) := by
  sorry
```

PR #18394 (in flight) ships an analogous discharge plan for the **palindrome**
sorry at line 92 (S2.B target) — the involution `x ↦ n - x i`. The
palindrome and the binomial-identity targets are **strictly orthogonal**:
PR #18394 does not touch this sorry, and this PREP does not touch the
palindrome sorry.

The S2.A docstring at line 65–72 already sketches the strategy:

> Lattice points are weak compositions of `n` into `d` parts. Setting
> `y_i = x_i` for `i < d - 1` and absorbing the slack into the last
> coordinate yields a bijection with `Sym (Fin d) n`; conclude with
> `Sym.card_sym_eq_choose` (cf. `EhrhartSimplexProven.simplex_lattice_count`).

This PREP **expands that sketch into a build-verifiable tactic chain**,
flags three Mathlib-API snags, and locks the cost estimate at ~50–70 Lean
lines.

---

## 2. Race-safety

```
$ gh pr list --repo rjwalters/lean-genius --state open \
    --search "ehrhart-cube-proven-oq-03 in:title"
[#18394] S3 PREP — palindrome discharge plan with full Lean proof embedded (doc-only)
[#18398] Enrich ehrhart-cube-proven-oq-03: crossReferences schema fix + depth
```

PR #18394 adds exactly one file under
`research/problems/ehrhart-cube-proven-oq-03/sessions/2026-05-12-s3-prep-palindrome-discharge.md`.
This PREP adds a file with a **different name**
(`2026-05-12-s3-prep-hypersimplex-count-k1-discharge.md`) and does not edit
`problem.md`, `state.md`, `knowledge.md`, or
`src/data/research/problems/ehrhart-cube-proven-oq-03.json`. Mergeable in
either order with PR #18394.

PR #18398 is an enrichment PR touching the `src/data/proofs/ehrhart-cube-proven-oq-03/`
gallery directory — also disjoint. Mergeable in either order.

---

## 3. Goal restatement

`hypersimplexLatticeCount d k n` is defined at `EhrhartCubeProvenOQ03.lean:58–61`
as a `Finset.filter` cardinality:

```lean
def hypersimplexLatticeCount (d k n : ℕ) : ℕ :=
  (Finset.univ.filter
      (fun x : Fin d → Fin (n + 1) => (∑ i : Fin d, (x i : ℕ)) = n * k)).card
```

At `k = 1`, the constraint is `∑ x_i = n · 1 = n`. The S2.A goal is

```
hypersimplexLatticeCount d 1 n = (n + d - 1).choose (d - 1)
```

i.e., the number of functions `Fin d → Fin (n + 1)` with coordinate sum
exactly `n` equals `(n + d − 1).choose (d − 1)` — Stars-and-Bars over `d`
boxes with total `n`.

Note that the upper-bound `x_i ≤ n` is **redundant** under `∑ x_i = n`,
since each summand is `≤ n` automatically. The interesting structure is the
**weak-composition / multiset** bijection.

---

## 4. The Mathlib-side identity

`Sym.card_sym_eq_choose` (Mathlib) states

```
Fintype.card (Sym α n) = (Fintype.card α + n - 1).choose n
```

With `α := Fin d` and `Fintype.card_fin : Fintype.card (Fin d) = d`,

```
Fintype.card (Sym (Fin d) n) = (d + n - 1).choose n
```

`Nat.choose_symm_of_eq_add` (or `Nat.choose_symm` directly) gives

```
(d + n - 1).choose n = (d + n - 1).choose ((d + n - 1) - n)
                     = (d + n - 1).choose (d - 1)
                     = (n + d - 1).choose (d - 1)   -- by add_comm
```

So the Mathlib endpoint is `(n + d - 1).choose (d - 1)`, **exactly** the
S2.A RHS.

This is identical to the route taken by the sibling
`EhrhartSimplexProven.simplex_lattice_count` (line 62–66), modulo one
difference: the sibling **defines** `Fintype.card (Sym (Fin (d+1)) n)` as
the lattice count, whereas the hypersimplex scaffold defines the lattice
count as a `Finset.filter`. So we need an extra step **identifying the
filter cardinality with `Fintype.card (Sym (Fin d) n)`**.

---

## 5. The bridge — three discharge strategies

### Strategy A: `Finset.card_bij` with histogram (RECOMMENDED — ~50 lines)

Construct an explicit bijection from the filter-set to `Sym (Fin d) n`.
The forward map is the **histogram**:

```lean
toFun (x : Fin d → Fin (n + 1)) : Sym (Fin d) n :=
  ⟨∑ i : Fin d, (x i : ℕ) • ({i} : Multiset (Fin d)), by
    simp [Multiset.card_sum, Multiset.card_smul, Multiset.card_singleton, mul_one]
    -- reduces to: ∑ i, (x i : ℕ) = n, which is the filter hypothesis
    ...⟩
```

The inverse is the **multiplicity-count**:

```lean
invFun (m : Sym (Fin d) n) : Fin d → Fin (n + 1) :=
  fun i => ⟨Multiset.count i m.val, by
    -- Multiset.count_le_card + Sym.card = n: count i ≤ n
    have h₁ : Multiset.count i m.val ≤ m.val.card := Multiset.count_le_card _ _
    have h₂ : m.val.card = n := m.2
    omega⟩
```

Lean shape (using `Finset.card_bij'` which accepts the explicit inverse):

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

Estimated cost: **~50 Lean lines** including the five sub-goals.

### Strategy B: `Equiv`-then-`Fintype.card_congr` (~70 lines)

Build the same histogram bijection as an `Equiv`:

```lean
def hypersimplexEquivSym (d n : ℕ) :
    { x : Fin d → Fin (n + 1) // (∑ i, (x i : ℕ)) = n } ≃ Sym (Fin d) n where
  toFun x := ⟨∑ i, (x.val i : ℕ) • ({i} : Multiset (Fin d)), ?_⟩
  invFun m i := ⟨Multiset.count i m.val, ?_⟩
  left_inv := ?_
  right_inv := ?_
```

Then `Fintype.card_congr hypersimplexEquivSym` plus
`Finset.card_filter_eq_card_subtype` (or its inverse direction) closes the
filter-to-subtype gap.

Estimated cost: **~70 Lean lines**. Slightly cleaner factoring (the equiv
can be re-used by S2.B's palindrome alternative-proof attempt), but more
lines for the two `_inv` proofs.

### Strategy C: induction on `d` (~80 lines)

A recurrence: condition on the value of the last coordinate `x_{d-1} = k`,
reducing to `hypersimplexLatticeCount (d - 1) 1 (n - k)`. The recursion
matches Pascal's identity `C(n + d − 1, d − 1) = ∑_{k=0}^{n} C(n − k + d − 2, d − 2)`,
which is `Finset.sum_range_choose` after re-indexing.

Estimated cost: **~80 Lean lines**. More work and the base case `d = 1`
needs `hd : 1 ≤ d` to dispatch cleanly. **Not recommended** — Strategy A
or B is shorter.

---

## 6. Three Mathlib-API snags

### Snag 1: `Finset.filter` vs. `Fintype.card` of subtype

The filter version

```
(Finset.univ.filter (fun x => P x)).card
```

and the subtype-Fintype version

```
Fintype.card { x // P x }
```

agree by `Finset.card_filter_univ_eq_fintype_card_subtype` (or `Fintype.card_subtype`).
Direction of the lemma is

```
Fintype.card { x // P x } = (Finset.univ.filter (fun x => P x)).card
```

so the rewrite in Strategy A is in the right direction; just confirm the
exact name at v4.26.0. Alternative: search Mathlib for `card_filter` family
and pick the one matching `Finset.univ.filter`.

### Snag 2: `Multiset.count` bound for the inverse

The inverse map needs `Multiset.count i m.val ≤ n`. We have:

- `Multiset.count_le_card : count a s ≤ s.card`
- `Sym.card_val : (⟨s, h⟩ : Sym α n).val.card = n` — but in fact `Sym` is
  defined as `{ s : Multiset α // s.card = n }`, so the cardinality field is
  the second projection. `m.2 : m.val.card = n`.

Combine: `count i m.val ≤ m.val.card = n`, hence `count i m.val < n + 1`
for the `Fin (n + 1)` coercion. **No omega needed** if we use
`Nat.lt_succ_of_le (Multiset.count_le_card i m.val |>.trans m.2.le)`, but
`omega` works too.

### Snag 3: Histogram size is `n`

The forward map needs

```
(∑ i, (x i : ℕ) • ({i} : Multiset (Fin d))).card = n
```

Mathlib has:

- `Multiset.card_sum : (s.sum).card = s.sum (Multiset.card)` for `s : Multiset (Multiset α)` — wrong shape.
- For a `Finset`-sum: `Multiset.card_sum_finset : (∑ i ∈ s, f i).card = ∑ i ∈ s, (f i).card` — likely named without the `_finset` suffix and applied via `Finset.sum_congr`.
- `Multiset.card_smul_eq_smul_card` or `Multiset.card_nsmul` : `(k • s).card = k * s.card` (modulo `smul_eq_mul`).
- `Multiset.card_singleton : ({a} : Multiset α).card = 1`.

Chain: `(∑ i, x i • {i}).card = ∑ i, (x i • {i}).card = ∑ i, x i * 1 = ∑ i, x i = n`.

The final `= n` step uses the filter hypothesis `(∑ i, (x i : ℕ)) = n`.

**Risk**: the exact name of "card commutes with `Finset.sum` for `Multiset`"
in v4.26.0. Plausible candidates: `Multiset.card_sum`, `Finset.sum_card`,
`Multiset.sum_card_lt` (no). If absent under a single name, expand via
`Finset.sum_congr rfl + Multiset.card_smul + Multiset.card_singleton + mul_one`
and `Finset.sum_const`-style cleanup. **Documented as a snag to watch
during build verification.**

---

## 7. Falsification by numeric sanity check

The scaffold already includes

```lean
theorem hypersimplex_count_3_1_2 :
    hypersimplexLatticeCount 3 1 2 = (2 + 3 - 1).choose (3 - 1) := by decide
```

This is the case `d = 3, n = 2`, which is **the same identity as the S2.A
theorem evaluated at these arguments**. The `decide` checks both sides
explicitly:

- LHS = #{(x_1, x_2, x_3) : Fin 3 → Fin 3 | x_1 + x_2 + x_3 = 2} = 6.
  (Tuples: (2,0,0), (1,1,0), (1,0,1), (0,2,0), (0,1,1), (0,0,2).)
- RHS = `(2 + 3 - 1).choose (3 - 1) = (4).choose (2) = 6`. ✓

So we know the **identity is true** and the Lean RHS evaluates correctly
to 6. The S2.A theorem just generalizes this `decide` check from `(d=3,n=2)`
to arbitrary `(d, n)` with `1 ≤ d`. No risk of stating a false theorem.

Two additional sanity checks already in the file confirm `d=2,n=2`
(LHS=3=RHS) and `d=3,n=1` (LHS=3=RHS), though the third is stated as
`hypersimplexLatticeCount 3 1 1 = 3` and not as an instance of the
S2.A formula.

---

## 8. Edge cases

| Case      | Behavior of S2.A statement                                                                                       |
| --------- | ---------------------------------------------------------------------------------------------------------------- |
| `d = 1`   | `hypersimplexLatticeCount 1 1 n = #{x : Fin 1 → Fin (n+1) \| x_0 = n} = 1`. RHS = `(n + 1 - 1).choose 0 = n.choose 0 = 1`. ✓ |
| `n = 0`   | `hypersimplexLatticeCount d 1 0 = #{x : Fin d → Fin 1 \| ∑ x_i = 0} = 1` (only the zero function). RHS = `(0 + d - 1).choose (d - 1) = (d-1).choose (d-1) = 1`. ✓ |
| `d = 0`   | Excluded by `hd : 1 ≤ d`. The hypothesis is necessary because `Nat.choose_symm_of_eq_add` at `d = 0, n ≥ 1` would give `(n - 1).choose (-1)`, which is `(n-1).choose 0 = 1` in ℕ-arithmetic, but `hypersimplexLatticeCount 0 1 n` is `#{x : Fin 0 → Fin (n+1) \| 0 = n}` = `1` if `n = 0` else `0` — does **not** match `(n - 1).choose 0 = 1`. So `hd` is load-bearing. |

The `hd : 1 ≤ d` precondition is correctly placed.

---

## 9. ACT-readiness checklist (for the next session)

When picking up S2.A in an ACT:

1. Branch off **main** (not off PR #18394's branch), name
   `research/ehrhart-cube-proven-oq-03-s2a-act-hypersimplex-count-k1-<ts>`.
2. Open `proofs/Proofs/EhrhartCubeProvenOQ03.lean`, replace `sorry` on line 74
   with Strategy A's body (see §5).
3. Build inside Docker: `./proofs/scripts/docker-build.sh Proofs.EhrhartCubeProvenOQ03`.
   Expected fresh-build time: ~6–8 minutes if `.lake` cache is intact, ~10
   minutes if cache misses (Mathlib re-import).
4. If §6 Snag 3 hits: substitute a manual `Finset.sum_congr` + binder rewrite
   chain. The fallback proof grows by ~10 lines.
5. Bump `src/data/proofs/ehrhart-cube-proven-oq-03/meta.json` sorry count
   from 2 → 1.
6. Update `src/data/research/problems/ehrhart-cube-proven-oq-03.json`:
   add an `insights` entry, advance the `currentState` if S2.B is also
   discharged.
7. PR title: `research(ehrhart-cube-proven-oq-03): S2.A ACT — discharge hypersimplex_count_k_one via Sym (Fin d) n bijection (build verified)`.

If the ACT lands **before** PR #18394 merges, the PR can adopt that
session's filename convention or co-exist; the two ACTs touch disjoint
sorries and `meta.sorries` simply drops by `1` each.

---

## 10. Why a PREP and not a direct ACT

Five reasons mirroring PR #18394's rationale plus one additional:

1. **`.lake` symlink loop wipe risk** — see `feedback_researcher_lake_symlink_loop_and_wipe.md`.
   A direct ACT requires Docker, which has nuked uncommitted work before;
   a PREP commits the design memo first.
2. **Slug heat** — 4 merges in <2 hours today (#18289 / #18293 / #18335 /
   #18357) plus PR #18394 still open. Concurrent agents are active; a
   doc-only PREP is conflict-free.
3. **Three Mathlib-API snags** — flagged in §6. Build-verifying needs a
   round-trip to confirm the name of `Multiset.card_sum` at v4.26.0 and
   the direction of `Finset.card_filter`. Cheaper to document the
   fallback first.
4. **Two parallel-orthogonal PREPs** — PR #18394 covers S2.B; this PREP
   covers S2.A. The pair scopes both remaining sorries before either is
   discharged. The next researcher can pick whichever is faster to
   build-verify on their hardware.
5. **Three discharge strategies** — A vs. B vs. C. Locking the recommendation
   (Strategy A) prevents the next researcher from re-debating the
   `Finset.card_bij` vs. `Equiv.toFun` choice.
6. **No-`MotivicMeasure`-equivalent obstacle** — unlike PR #18401's
   `motivic-flag-maps-oq-03` PREP, S2.A here has **no new structure** to
   design. The discharge is pure tactic chain. Documenting it at PREP
   level gives the next session a copy-pasteable starting point and
   nothing more.

---

## 11. Cross-references

- **Sister palindrome PREP**: PR #18394 (open), files:
  `research/problems/ehrhart-cube-proven-oq-03/sessions/2026-05-12-s3-prep-palindrome-discharge.md`.
- **Scaffold**: `proofs/Proofs/EhrhartCubeProvenOQ03.lean:74` (the sorry).
- **Sibling pattern**: `proofs/Proofs/EhrhartSimplexProven.lean:62–66`
  (`simplex_lattice_count` — the Sym-model template, but with the count
  defined AS `Fintype.card (Sym (Fin (d+1)) n)`, sidestepping the bridge
  step §5).
- **Numeric anchor**: `hypersimplex_count_3_1_2` in the same file already
  closes the S2.A identity at `(d=3, n=2)` via `decide`.

---

## 12. What this PR does NOT do

- No edit to `problem.md`, `state.md`, `knowledge.md`.
- No edit to `src/data/research/problems/ehrhart-cube-proven-oq-03.json`.
- No edit to any `.lean` file. Sorry count unchanged.
- No edit to `src/data/proofs/ehrhart-cube-proven-oq-03/` (PR #18398's
  territory).
- No phase advance. Stays at S1 OBSERVE / S2 SCAFFOLD pending the ACT
  pick of S2.A or S2.B.
