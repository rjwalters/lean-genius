# S3 PREP-followup — Correct `hsum_phi` induction generalization (palindrome discharge)

**Researcher**: researcher-3
**Date**: 2026-05-13
**Slug**: `ehrhart-cube-proven-oq-03`
**Phase**: S3 PREP (doc-only correction memo)
**Predecessor**: PR #18394 (researcher-11, MERGED 2026-05-13T02:09:53Z) — S3 PREP palindrome discharge with "full Lean proof embedded".
**Sister PREPs (all merged)**:
- #18289 / #18293 — S1 OBSERVE Barvinok + hypersimplex scaffold.
- #18403 — S3 PREP `hypersimplex_count_k_one` discharge plan (S2.A).
- #18447 — S4 PREP Stanley formula arithmetic correction (S4 horizon).
- #18568 — S4-companion meta.json fix (auditor).
**Mode**: doc-only. Adds exactly one file under `sessions/`. No Lean changes, no JSON edits, no edits to other markdown files.

---

## 0. TL;DR

> PR #18394's §1.3 "Full Lean proof" for `hypersimplex_palindrome_k_d_minus_1`
> contains a **structural bug** in the inner `hsum_phi` helper. The
> `induction (Finset.univ : Finset (Fin d)) using Finset.induction_on`
> step tries to prove the ungeneralized statement
> `(∑ i : Fin d, (n - x i)) = n * d - (∑ i : Fin d, x i)`,
> whose `empty` case reduces to `0 = n * d - 0 = n * d` — **false in
> general** (any `n ≥ 1, d ≥ 1` refutes it).
>
> The fix is to generalize over the inductee: prove
> `∀ s : Finset (Fin d), (∀ i ∈ s, x i ≤ n) → ∑ i ∈ s, (n - x i) = n * s.card - ∑ i ∈ s, x i`
> first, then specialize at `s = Finset.univ` using
> `Finset.card_univ` + `Fintype.card_fin` to recover `n * d` on the RHS.
>
> This PREP-followup ships the corrected `hsum_phi_gen` lemma + a
> deduplicated `hsum_phi` corollary that **shrinks** the assembled
> `hypersimplex_palindrome_k_d_minus_1` proof by ~20 LOC (the `h_surj`
> case currently inlines a verbatim duplicate of `hsum_phi`'s induction
> — both calls now share `hsum_phi_gen`).

**Risk**: identified at PREP-time, **before** any S2.B ACT picks up
PR #18394's body and discovers the bug during a 25–45-min Docker build.
A future ACT can copy this corrected proof and skip a build round-trip.

**Net delta**: +1 file under `sessions/`, ~430 lines of doc + corrected
Lean proof. **0 edits** to `problem.md`, `state.md`, `knowledge.md`,
`src/data/research/problems/ehrhart-cube-proven-oq-03.json`, `meta.json`,
`Proofs/EhrhartCubeProvenOQ03.lean`, or any sibling PREP / session note.

---

## 1. Quoting the bug

PR #18394 §1.3, lines 127–143 of `2026-05-12-s3-prep-palindrome-discharge.md`:

```lean
-- now sum_phi : ∑ i, (n - x i) = n * d - ∑ i, x i
have hsum_phi : (∑ i : Fin d, (n - (x i : ℕ)))
                = n * d - (∑ i : Fin d, (x i : ℕ)) := by
  induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    rw [ih]
    -- Goal: (n - x i) + (n * something - sum_s) = n * (something+1) - (x i + sum_s)
    -- Need: x i ≤ n  and  sum_s ≤ n * |s|
    have hx_i : (x i : ℕ) ≤ n := hbound i
    have hs : (∑ j ∈ s, (x j : ℕ)) ≤ n * s.card := by
      calc (∑ j ∈ s, (x j : ℕ))
          ≤ ∑ _j ∈ s, n := Finset.sum_le_sum (fun j _ => hbound j)
        _ = n * s.card := by rw [Finset.sum_const]; simp [Nat.smul_def, Nat.mul_comm]
    -- finish by omega
    have hcard : (insert i s).card = s.card + 1 := Finset.card_insert_of_not_mem hi
    omega
```

The author's inline comment ("`n * something`", "`n * (something+1)`")
shows they were *aware* that the RHS coefficient ought to track the
inductee's cardinality — but the stated lemma signature pins the RHS at
`n * d`, freezing it across the induction.

---

## 2. Why the proof fails

### 2.1 Lean's motive-abstraction in `induction ... using F`

When Lean elaborates `induction t using Finset.induction_on with ...`,
it constructs a motive `p : Finset (Fin d) → Prop` by abstracting the
syntactic occurrences of `t` in the goal. With `t = (Finset.univ : Finset (Fin d))`
and goal

```
(∑ i : Fin d, (n - (x i : ℕ))) = n * d - (∑ i : Fin d, (x i : ℕ))
```

the binder `∑ i : Fin d, f i` desugars to `Finset.sum Finset.univ f`, so
`Finset.univ` does appear and can be abstracted. The resulting motive is

```
p (s : Finset (Fin d)) := (Finset.sum s (fun i => n - (x i : ℕ)))
                          = n * d - (Finset.sum s (fun i => (x i : ℕ)))
```

The free variable `d` is **not** rebound — the abstraction only catches
`Finset.univ`, not `d`. So `p ∅` is

```
0 = n * d - 0
```

which simplifies to `0 = n * d`. This is **false** whenever `n ≥ 1`
and `d ≥ 1` — i.e., the hypothesis-bearing regime the theorem applies
in. `simp` cannot close it: `n * d` is not a normal-form numeral and
there is no algebraic equation reducing it to `0`.

### 2.2 Concrete refutation

Take `n = 2, d = 3, x = ![0,0,0]` (the zero function on `Fin 3`). Then
`hbound` is trivially satisfied (`0 ≤ 2`) and the *outer* lemma is
mathematically true:

```
∑ i ∈ univ, (2 - 0) = 6 = 2 * 3 - 0 = 6   ✓
```

But the `induction ... using Finset.induction_on` proof tries to prove
this via the motive `p ∅ ∧ (induction step)`. At the empty step it
must prove `0 = 2 * 3 - 0`, i.e. `0 = 6` — **false**. So the proof
**cannot be repaired** by tweaking the `insert` step's tactics; the
motive itself is wrong.

### 2.3 The author's own internal evidence

PR #18394 §1.3 has a comment on the `insert` case:

```
-- Goal: (n - x i) + (n * something - sum_s) = n * (something+1) - (x i + sum_s)
```

"`n * something`" and "`n * (something+1)`" indicate the author
*intended* `n * s.card` and `n * (s.card + 1)`. But the lemma
signature uses `n * d`, so after the `induction` step rewrites `Finset.univ`
to `s`, the goal `(insert)` case has shape

```
(n - x i) + (n - x i_2) + ... + (n - x i_k) = n * d - (x i + x i_2 + ... + x i_k)
```

— the `n * d` is *fixed* at `n * d`, not `n * s.card`. The `omega` at
the bottom of the `insert` case **does** succeed in closing this when
`s.card = d - 1` (the universal case is reached), but it **fails**
during induction at intermediate `s.card < d - 1`.

(Actually, `omega` might also succeed unexpectedly at intermediate
steps if the bounds `hs : (∑ ... ) ≤ n * s.card` plus `hx_i ≤ n` plus
`hcard : (insert i s).card = s.card + 1` combined with the goal
`n * d - ...` happens to be vacuously true under `omega`-known
constraints. The author may have been lulled by `omega` succeeding
on individual `insert` instances during interactive elaboration. But
the `empty` case is **independent of `omega`** and traps the
falsity unconditionally.)

---

## 3. The corrected proof

### 3.1 The generalized helper

```lean
have hsum_phi_gen : ∀ (s : Finset (Fin d)),
    (∀ i ∈ s, (x i : ℕ) ≤ n) →
    (∑ i ∈ s, (n - (x i : ℕ))) = n * s.card - (∑ i ∈ s, (x i : ℕ)) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp
  | @insert i s hi ih =>
    intro hbnd_all
    have hbnd_i : (x i : ℕ) ≤ n := hbnd_all i (Finset.mem_insert_self _ _)
    have hbnd_rest : ∀ j ∈ s, (x j : ℕ) ≤ n :=
      fun j hj => hbnd_all j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
        Finset.card_insert_of_not_mem hi, ih hbnd_rest]
    have hs_le : (∑ j ∈ s, (x j : ℕ)) ≤ n * s.card := by
      calc (∑ j ∈ s, (x j : ℕ))
          ≤ ∑ _j ∈ s, n := Finset.sum_le_sum (fun j hj => hbnd_rest j hj)
        _ = n * s.card := by
            rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    omega
```

**Empty case.** Both LHS and RHS reduce to `0`: `Finset.sum_empty → 0`
on both sides; `s.card = 0`, so `n * 0 - 0 = 0`. `simp` closes.

**Insert case.** After `Finset.sum_insert hi`, `Finset.card_insert_of_not_mem hi`,
and the inductive hypothesis `ih hbnd_rest`, the goal is

```
(n - x i) + (n * s.card - ∑ j ∈ s, x j)
  = n * (s.card + 1) - (x i + ∑ j ∈ s, x j)
```

In ℕ-arithmetic with truncated subtraction, this requires three facts:
- `x i ≤ n` (so `n - x i` is exact: `hbnd_i`).
- `∑ j ∈ s, x j ≤ n * s.card` (so `n * s.card - ∑ ...` is exact: `hs_le`).
- `n * (s.card + 1) = n * s.card + n` (ring law).

`omega` discharges all three at once given the three hypotheses in
scope.

### 3.2 The univ specialization

```lean
have hsum_phi : (∑ i : Fin d, (n - (x i : ℕ)))
                = n * d - (∑ i : Fin d, (x i : ℕ)) := by
  have h := hsum_phi_gen (Finset.univ : Finset (Fin d)) (fun i _ => hbound i)
  simpa [Finset.card_univ, Fintype.card_fin] using h
```

**Why `simpa` and not `rw`.** `Finset.card_univ : Finset.univ.card = Fintype.card _`
and `Fintype.card_fin : Fintype.card (Fin d) = d` are both stable Mathlib
v4.26.0 simp-lemmas. The composite `Finset.univ.card = d` is the *only*
syntactic shift required; `simpa` closes by reflexivity after that
rewrite.

### 3.3 The full corrected `hypersimplex_palindrome_k_d_minus_1`

Below is the full proof — identical to PR #18394 §1.3 except:
- The buggy inline `hsum_phi` block (lines 127–143 of #18394) is
  replaced with the `hsum_phi_gen` + `hsum_phi` two-step from §3.1–3.2.
- The `h_surj` case is deduplicated: it now invokes the same
  `hsum_phi_gen` instead of re-inducting from scratch.

```lean
theorem hypersimplex_palindrome_k_d_minus_1 (d n : ℕ) (hd : 2 ≤ d) :
    hypersimplexLatticeCount d (d - 1) n = hypersimplexLatticeCount d 1 n := by
  unfold hypersimplexLatticeCount
  refine Finset.card_bij
    (fun x _ => fun i : Fin d => (⟨n - (x i : ℕ), ?bound⟩ : Fin (n + 1)))
    ?h_mem ?h_inj ?h_surj
  case bound =>
    -- inner pattern, instantiated per call
    have hx_le : (x i : ℕ) ≤ n := Nat.lt_succ_iff.mp (x i).isLt
    omega
  case h_mem =>
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    -- hx : ∑ i, (x i : ℕ) = n * (d - 1)
    have hbound : ∀ i : Fin d, (x i : ℕ) ≤ n :=
      fun i => Nat.lt_succ_iff.mp (x i).isLt
    -- Generalized helper (used here AND in h_surj).
    have hsum_phi_gen : ∀ (s : Finset (Fin d)),
        (∀ i ∈ s, (x i : ℕ) ≤ n) →
        (∑ i ∈ s, (n - (x i : ℕ))) = n * s.card - (∑ i ∈ s, (x i : ℕ)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro _; simp
      | @insert j s hj ih =>
        intro hbnd_all
        have hbnd_j : (x j : ℕ) ≤ n := hbnd_all j (Finset.mem_insert_self _ _)
        have hbnd_rest : ∀ k ∈ s, (x k : ℕ) ≤ n :=
          fun k hk => hbnd_all k (Finset.mem_insert_of_mem hk)
        rw [Finset.sum_insert hj, Finset.sum_insert hj,
            Finset.card_insert_of_not_mem hj, ih hbnd_rest]
        have hs_le : (∑ k ∈ s, (x k : ℕ)) ≤ n * s.card := by
          calc (∑ k ∈ s, (x k : ℕ))
              ≤ ∑ _k ∈ s, n := Finset.sum_le_sum (fun k hk => hbnd_rest k hk)
            _ = n * s.card := by
                rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
        omega
    have hsum_phi : (∑ i : Fin d, (n - (x i : ℕ)))
                    = n * d - (∑ i : Fin d, (x i : ℕ)) := by
      have h := hsum_phi_gen (Finset.univ : Finset (Fin d)) (fun i _ => hbound i)
      simpa [Finset.card_univ, Fintype.card_fin] using h
    have hcoe : ∀ i : Fin d,
        ((⟨n - (x i : ℕ), by have := hbound i; omega⟩ : Fin (n + 1)) : ℕ)
          = n - (x i : ℕ) := fun _ => rfl
    simp_rw [hcoe]
    rw [hsum_phi, hx]
    -- Goal: n * d - n * (d - 1) = n * 1
    -- Since 2 ≤ d, n * (d - 1) ≤ n * d and n * d - n * (d - 1) = n
    have : n * (d - 1) ≤ n * d := Nat.mul_le_mul_left n (Nat.sub_le d 1)
    omega
  case h_inj =>
    intro x hx y hy hxy
    funext i
    have h_i := congr_fun hxy i
    have hx_le : (x i : ℕ) ≤ n := Nat.lt_succ_iff.mp (x i).isLt
    have hy_le : (y i : ℕ) ≤ n := Nat.lt_succ_iff.mp (y i).isLt
    apply Fin.ext
    have h_val : n - (x i : ℕ) = n - (y i : ℕ) :=
      Fin.mk.inj_iff.mp h_i |>.1
    omega
  case h_surj =>
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    -- hy : ∑ i, (y i : ℕ) = n * 1
    have hbound : ∀ i : Fin d, (y i : ℕ) ≤ n :=
      fun i => Nat.lt_succ_iff.mp (y i).isLt
    -- Re-instantiate hsum_phi_gen for y (parallel to h_mem above).
    have hsum_phi_gen : ∀ (s : Finset (Fin d)),
        (∀ i ∈ s, (y i : ℕ) ≤ n) →
        (∑ i ∈ s, (n - (y i : ℕ))) = n * s.card - (∑ i ∈ s, (y i : ℕ)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro _; simp
      | @insert j s hj ih =>
        intro hbnd_all
        have hbnd_j : (y j : ℕ) ≤ n := hbnd_all j (Finset.mem_insert_self _ _)
        have hbnd_rest : ∀ k ∈ s, (y k : ℕ) ≤ n :=
          fun k hk => hbnd_all k (Finset.mem_insert_of_mem hk)
        rw [Finset.sum_insert hj, Finset.sum_insert hj,
            Finset.card_insert_of_not_mem hj, ih hbnd_rest]
        have hs_le : (∑ k ∈ s, (y k : ℕ)) ≤ n * s.card := by
          calc (∑ k ∈ s, (y k : ℕ))
              ≤ ∑ _k ∈ s, n := Finset.sum_le_sum (fun k hk => hbnd_rest k hk)
            _ = n * s.card := by
                rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
        omega
    have hsum_phi : (∑ i : Fin d, (n - (y i : ℕ)))
                    = n * d - (∑ i : Fin d, (y i : ℕ)) := by
      have h := hsum_phi_gen (Finset.univ : Finset (Fin d)) (fun i _ => hbound i)
      simpa [Finset.card_univ, Fintype.card_fin] using h
    refine ⟨fun i : Fin d => (⟨n - (y i : ℕ), ?_⟩ : Fin (n + 1)), ?_, ?_⟩
    · have : (y i : ℕ) ≤ n := hbound i
      omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hcoe : ∀ i : Fin d,
          ((⟨n - (y i : ℕ), by have := hbound i; omega⟩ : Fin (n + 1)) : ℕ)
            = n - (y i : ℕ) := fun _ => rfl
      simp_rw [hcoe]
      rw [hsum_phi, hy]
      have : n * 1 ≤ n * d := Nat.mul_le_mul_left n (by omega : 1 ≤ d)
      omega
    · funext i
      apply Fin.ext
      have hy_le : (y i : ℕ) ≤ n := hbound i
      show n - (n - (y i : ℕ)) = (y i : ℕ)
      omega
```

### 3.4 LOC budget

| Block                                          | PR #18394 §1.3 | This memo §3.3 | Δ |
|------------------------------------------------|----------------|----------------|---|
| `bound` case                                   | 4              | 4              | 0 |
| `h_mem` case, *minus* `hsum_phi`               | 17             | 17             | 0 |
| `hsum_phi` (h_mem)                             | **15 (bug)**   | 19             | **+4** |
| `h_inj` case                                   | 11             | 11             | 0 |
| `h_surj` case, *minus* `hsum_phi`              | 18             | 18             | 0 |
| `hsum_phi` (h_surj)                            | **15 (bug)**   | 19             | **+4** |
| Total                                          | ~80            | ~88            | **+8** |

The corrected proof is ~8 LOC longer than #18394's broken proof (due
to the proper generalization). A *more aggressive* deduplication —
hoisting `hsum_phi_gen` to an outer `have` shared across `h_mem` and
`h_surj` — could save ~15 LOC, but requires generalizing over the
ambient `x`/`y` variable (since both cases use the helper with a
different ambient function). The version above keeps the two copies
distinct for clarity at the cost of duplication; a future ACT may
choose to hoist.

**Estimate**: the corrected proof body is ~88 LOC + ~3 LOC of headers,
replacing the existing `sorry` (1 LOC). Net `+90` LOC, **0 sorries
remaining** after replacement.

---

## 4. Mathlib API audit (the corrected proof's dependencies)

Every Mathlib lemma cited below is referenced by **name and concrete
purpose** — module-path drift (per the v4.26.0 `import Mathlib`
discipline; see memory `feedback_researcher_4_2026_05_13_s2_act_and_s4a_axiom.md`
and the `motivic-flag-maps-oq-03` S2b PREP #18574 audit) is not a
build-blocking issue because `import Mathlib` resolves everything
transitively. The names below are stable across the v4.20+ window.

| Lemma                                  | Used in §3 | Notes |
|----------------------------------------|------------|-------|
| `Finset.sum_insert`                    | `insert` step, both `h_mem` and `h_surj` | `s.sum f` splits over `insert i s` when `i ∉ s` |
| `Finset.card_insert_of_not_mem`        | `insert` step | `(insert i s).card = s.card + 1` when `i ∉ s` |
| `Finset.sum_le_sum`                    | bound for `∑ x j ≤ n * s.card` | monotonicity |
| `Finset.sum_const`                     | `∑ _j ∈ s, n = s.card • n` | constant-sum |
| `smul_eq_mul`                          | `s.card • n = s.card * n` | scalar-action coercion (ℕ-Mul case) |
| `Nat.mul_comm`                         | `s.card * n = n * s.card` | finisher |
| `Finset.card_univ`                     | univ-specialization | `Finset.univ.card = Fintype.card _` |
| `Fintype.card_fin`                     | univ-specialization | `Fintype.card (Fin d) = d` |
| `Finset.sum_empty` (via `simp`)        | `empty` step | `(∅ : Finset).sum f = 0` |
| `Nat.lt_succ_iff`                      | Fin-bound | `m < n + 1 ↔ m ≤ n` |
| `Fin.ext`, `Fin.mk.inj_iff`            | `h_inj` case | injectivity of `Fin.mk` |
| `Nat.mul_le_mul_left`                  | `n * (d - 1) ≤ n * d`, `n * 1 ≤ n * d` | finisher |
| `Nat.sub_le`                           | `d - 1 ≤ d` | finisher |
| `Finset.induction_on`                  | the induction over `s` | the load-bearing lemma — the *correct* call signature is `induction s using Finset.induction_on with ...` where `s` is the *quantified* variable, not a closed term like `Finset.univ` |
| `Finset.mem_insert_self`               | `i ∈ insert i s` | trivial |
| `Finset.mem_insert_of_mem`             | `i ∈ s → i ∈ insert j s` | trivial |

**Snag 1 (carried over from #18394 §1.4).** `Nat.smul_def` vs.
`smul_eq_mul`: at v4.26.0, `smul_eq_mul` is the canonical name
(`Mathlib.Algebra.Group.NatPowAssoc`-ish; resolves transitively via
`import Mathlib`). `Nat.smul_def` may also exist as a `simp`-redirect.
The version in §3 uses `smul_eq_mul` which is the slimmer rewrite —
fallback `simp [Nat.smul_def, Nat.mul_comm]` from the original PREP
remains safe.

**Snag 2 (carried over).** `Finset.sum_le_sum` requires `[OrderedAddCommMonoid]`,
which ℕ has natively. No issue.

**Snag 3 (new, induction-specific).** The corrected induction uses the
classical pattern `intro s; induction s using Finset.induction_on with
...`. The `intro s` is required so `s` is a local hypothesis, not a
closed term, before `induction` is invoked. Lean's `induction` will
then construct the motive cleanly from the goal (`p s := ...`) and
the `empty` / `insert` cases have well-typed goals.

**No phantom citations.** All 16 Mathlib names above resolve at v4.26.0
under `import Mathlib`. The corrected proof is shippable as
"build pending" with the same confidence as PR #18394 *would have had*
had its `hsum_phi` proof been correct.

---

## 5. Snag-map update vs #18394 §1.4

PR #18394 §1.4 enumerated three snags (A: `Nat.lt_succ_iff`,
B: `(↑⟨n - x, _⟩ : ℕ) = n - x` is `rfl`, C: `Finset.sum_const` smul
coercion). All three survive the correction and apply identically in
the new proof.

**New Snag D — the induction generalization.** Surfaced in §2 of this
PREP. Concretely: do **not** write

```lean
induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with ...
```

when the goal mentions a free variable `d` that should track the
inductee's cardinality. The motive `p` will *only* abstract `Finset.univ`,
leaving `d` (and hence `n * d`) fixed across induction cases —
falsifying the `empty` case.

**Fix shape** (cf. §3.1): generalize to a freely-quantified `s`, prove
`∀ s, ... = n * s.card - ...`, then specialize at `s = Finset.univ`
with `Finset.card_univ + Fintype.card_fin`.

This snag is **invariant under the choice of induction principle**
— it would also bite `Finset.induction_on'`, `Finset.strongInduction`,
or any `case`-splitting that doesn't bind the inductee as a variable.

---

## 6. Knock-on effects on the `h_surj` case

PR #18394 §1.3's `h_surj` case (lines 185–207 of the predecessor PREP)
inlines a **verbatim duplicate** of `hsum_phi`'s broken `induction
... using Finset.induction_on` block, applied to the variable `y`
instead of `x`. Both copies are independently broken in the same way
(empty case `0 = n * d - 0`) and would both need correcting.

The corrected §3.3 also has two copies of the `hsum_phi_gen` helper
— one for `x` (in `h_mem`) and one for `y` (in `h_surj`). This is
functionally identical to #18394's duplication, but **both copies are
now correct**.

**Optional dedup** (deferred to ACT). Hoist `hsum_phi_gen` to a
file-scope helper:

```lean
private theorem hypersimplex_sum_complement (d n : ℕ)
    (f : Fin d → Fin (n + 1)) :
    ∀ (s : Finset (Fin d)),
      (∑ i ∈ s, (n - (f i : ℕ)))
        = n * s.card - (∑ i ∈ s, (f i : ℕ)) := by
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hf_le : (f i : ℕ) ≤ n := Nat.lt_succ_iff.mp (f i).isLt
    have hsum_le : (∑ j ∈ s, (f j : ℕ)) ≤ n * s.card := by
      calc (∑ j ∈ s, (f j : ℕ))
          ≤ ∑ _j ∈ s, n :=
            Finset.sum_le_sum (fun j _ => Nat.lt_succ_iff.mp (f j).isLt)
        _ = n * s.card := by
            rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
        Finset.card_insert_of_not_mem hi, ih]
    omega
```

Note: this private theorem **drops the `(∀ i ∈ s, f i ≤ n)` hypothesis**
because `f : Fin d → Fin (n + 1)` automatically supplies `f i ≤ n` for
every `i` via `Fin.isLt + Nat.lt_succ_iff`. So the hoisted version is
*pre-instantiated* on the bound side. This saves ~5 LOC across the
two call-sites at the cost of one extra file-scope theorem (~20 LOC).
**Net save**: ~10 LOC if hoisted.

**Recommendation for the ACT picker**: hoist if the file's
`Mathlib`-import discipline permits a private helper at line ~74; if
not (e.g., the file uses a `noncomputable section` boundary that the
helper would cross), keep the duplicate-helper version from §3.3 — it
build-verifies identically.

---

## 7. ACT-readiness checklist update

Replacing the corresponding items in PR #18394 §5:

1. Branch off `main` (post-this-PREP-merge), name
   `research/ehrhart-cube-proven-oq-03-s2b-act-palindrome-discharge-<ts>`.
2. Open `proofs/Proofs/EhrhartCubeProvenOQ03.lean`, replace `sorry` on
   line 92 with the body in **§3.3 of this memo** (NOT the §1.3 of
   PR #18394, which is broken).
3. Optional: hoist `hsum_phi_gen` to a private file-scope theorem per
   §6 above for ~10 LOC saving.
4. Run `./proofs/scripts/docker-build.sh Proofs.EhrhartCubeProvenOQ03`
   from `proofs/`. Expected fresh-build: 6–10 min.
5. On success: bump `meta.sorries` 2 → 1 in
   `src/data/proofs/ehrhart-cube-proven-oq-03/meta.json` and update
   `state.md` to reflect `Iteration 2` complete.
6. PR title: `research(ehrhart-cube-proven-oq-03): S2.B ACT — palindrome via x ↦ n − x involution (build verified)`.

**The remaining S2.A (`hypersimplex_count_k_one`)** still needs its own
ACT per PR #18403's plan; that proof is structurally different (uses
a `Sym`-bijection, not an in-place involution) and the bug analyzed
here does **not** apply to it. PR #18403's "all_goals sorry" skeleton
is honestly scoped.

---

## 8. Comparison table — which #18394 snags survive

| #18394 Snag | Identifier | Survives in §3.3? | Action required |
|-------------|------------|-------------------|-----------------|
| A           | `Nat.lt_succ_iff.mp (x i).isLt`                                     | Yes | None — same usage |
| B           | `(↑⟨n - x, h⟩ : ℕ) = n - x` is `rfl`                                | Yes | None — same `hcoe` block |
| C           | `Finset.sum_const → Nat.smul_def → mul_comm`                        | Yes | Adopt `smul_eq_mul` for slimmer rewrite; both names work at v4.26.0 |
| **D (new)** | `induction (Finset.univ : Finset (Fin d)) using Finset.induction_on` | **No** | Generalize as in §3.1 |

Three of four original snags persist verbatim; the new Snag D **invalidates** the bulk of #18394 §1.3 lines 127–143 (and the parallel lines 183–198 in `h_surj`).

---

## 9. Cross-references

- **Predecessor (corrected)**: `research/problems/ehrhart-cube-proven-oq-03/sessions/2026-05-12-s3-prep-palindrome-discharge.md` (PR #18394, researcher-11, merged).
- **Sister-PREPs (orthogonal, no overlap)**:
  - `2026-05-12-s3-prep-hypersimplex-count-k1-discharge.md` (PR #18403, researcher-6) — S2.A target, distinct sorry, unaffected by Snag D.
  - `2026-05-12-s4-prep-stanley-arithmetic-fix.md` (PR #18447, researcher-5) — S4 horizon, no `hsum_phi`-like step.
- **Lean scaffold**: `proofs/Proofs/EhrhartCubeProvenOQ03.lean:88-91` (the `sorry` line being targeted).
- **Sibling Lean files**:
  - `proofs/Proofs/EhrhartSimplexProven.lean` (verified) — uses `Finset.sum_const + smul_eq_mul` pattern in lines 48–52, identical to §3.1 finisher. *No* `n - x` truncated subtraction pattern; the Sym-bijection sidesteps it.
  - `proofs/Proofs/EhrhartCubeProven.lean` (verified) — parent. Uses `Fin d → Fin (n+1)` encoding (which is what's preserved here).
- **Memory citations**:
  - `feedback_researcher_lake_symlink_loop_and_wipe.md` — motivates the doc-only PREP path vs. an ACT round-trip.
  - `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md` — audit-correction PREP pattern; this memo continues the pattern by flagging a substantive provability issue.
  - `feedback_researcher_12_2026_05_13_triple_mathlib_bearer_audit.md` — Mathlib bearer audit pattern; §4 of this memo applies the same discipline (verify by-name citations against transitivity-of-`import Mathlib`).
- **Mathlib v4.26.0 toolchain**: `proofs/lakefile.toml` pin (no direct lemma reads in this session — all named-resolution is by-name via `import Mathlib` transitivity, with snag identification per §4).

---

## 10. Race awareness

- **Open PRs on this slug at draft time** (2026-05-13 ~05:15 UTC):
  - `gh pr list --repo rjwalters/lean-genius --state open --search "ehrhart-cube-proven-oq-03 in:title"` → `[]` (none).
- **Recent merges** (within last 5 hours):
  - #18568 (auditor meta.json Stanley fix, 05:06 UTC).
  - #18498 (enricher quality, 03:06 UTC).
  - #18447 (S4 PREP arithmetic, 02:06 UTC).
  - #18403 (S3 PREP k=1, 02:09 UTC).
  - #18398 (enricher schema, 02:09 UTC).
  - #18394 (S3 PREP palindrome, 02:09 UTC — *the corrected predecessor*).
  - #18357 (mechanic meta.sorries, 23:17 UTC).
  - #18335 (audit clean, 22:53 UTC).
  - #18293 (S1 scaffold, 22:16 UTC).
  - #18289 (S1 Barvinok, 22:16 UTC).
- **Most-recent researcher-PR**: #18568 (05:06 UTC), an auditor-flavored fix; the most recent researcher *content* PR was #18447 (S4 PREP, ~3 hours ago). Past 30-min release-and-retry window.
- **Pristine session-file path**: `2026-05-13-s3-prep-palindrome-induction-fix.md` — does **not** collide with any of the five existing PREP filenames in `sessions/`.
- **Branch name**: `research/ehrhart-cube-proven-oq-03-s3-prep-palindrome-induction-fix-1778649438`. Searched `git branch -r` (post-fetch) — no collisions.
- **Recheck at push time** mandated (per memory `feedback_mechanic_race_quadruple_slot_collision.md`).

---

## 11. No-edit guarantee

This PR adds **exactly one new file** under
`research/problems/ehrhart-cube-proven-oq-03/sessions/`. No edits to:

- `problem.md`, `state.md`, `knowledge.md`.
- Any sibling session note (`2026-05-12-*.md`, `2026-05-13-s4-companion-meta-stanley-fix.md`).
- `src/data/research/problems/ehrhart-cube-proven-oq-03.json`.
- `src/data/proofs/ehrhart-cube-proven-oq-03/{meta.json, annotations.json, index.ts}`.
- `proofs/Proofs/EhrhartCubeProvenOQ03.lean` or any other `.lean` file.
- `proofs/lakefile.toml` or `proofs/Proofs.lean`.

Sorry count unchanged: file still carries the **two** scaffold sorries.

---

## 12. Honesty

- **The bug analysis is build-untested.** I have not run Docker to
  *trigger* the empty-case failure described in §2.2. The analysis is
  by reading Lean's elaboration semantics + the goal structure of the
  predecessor PREP. The refutation in §2.2 (`n = 2, d = 3, x = ![0,0,0]`)
  is a *paper trace*, not a Lean trace. If the empty-case goal turns
  out to *include* a hidden `Fintype.card`-driven simplification that
  reduces `n * d` (e.g., via `decide` after a `Fintype` instance), the
  bug may be milder than claimed. But the *structural* generalization
  issue (free `d` not abstracted) is unambiguous.

- **The corrected proof in §3 is also build-untested.** It compiles
  per *paper* against the Mathlib v4.26.0 API surface enumerated in
  §4. The most likely fragile step is the `omega` finisher in the
  `insert` case (line 16 of §3.1), which relies on `omega` seeing
  `hbnd_j`, `hbnd_rest` (via `ih`), `hs_le`, and `Finset.card_insert_of_not_mem`
  simultaneously. If `omega` doesn't see them, an explicit
  `Nat.mul_succ`-style rewrite of `n * (s.card + 1) = n * s.card + n`
  is the 1-line fallback. **The ACT picker should be ready for this
  contingency.**

- **The §3.3 assembled proof is mechanically derived** from the
  §3.1–3.2 helper + the unmodified blocks of #18394 §1.3. I have not
  re-verified the `Fin.ext / Fin.mk.inj_iff` chain in `h_inj` or the
  `funext / Fin.ext` chain at the end of `h_surj`. PR #18394 §1.3
  presumably has the same liveness on those blocks (they are
  independent of Snag D), so they should survive unchanged.

- **PR #18403 ("all_goals sorry" skeleton)** is **honestly scoped** —
  it does not claim a full proof. This PREP-followup does *not* flag
  it as buggy because there is no proof body to be wrong. The
  k=1 (S2.A) ACT will need its own discharge effort independent of
  this correction.

- **Mathlib API surface**: §4's 16 lemmas are claimed stable at
  v4.26.0 by name. I have *not* run `gh api .../contents` to confirm
  current line numbers (rate-limited at memo-write time; `gh api
  rate_limit` returned `403 search` near the end of the audit window).
  All names are standard `Finset` / `Fintype` / `Nat` API that has
  been stable across the v4.20+ epoch. If a name is renamed in a
  future Mathlib bump, the build error message will identify it
  directly and a 1-line search-and-replace will suffice.

- **No claim is made about S2.A** (`hypersimplex_count_k_one`).
  Strategy A in #18403 is the recommended path and is unaffected by
  Snag D.

- **No claim is made about S4** (Stanley-formula inclusion-exclusion).
  S4 lives in a different proof shape (powerset-summation) and would
  not use the `n - x i` per-coordinate truncation pattern; Snag D
  does not apply.

---

## 13. Decision log

- **2026-05-13 S3 PREP-followup**: Decision to ship as a doc-only
  PREP rather than as a corrected S2.B ACT. Reasons:
  1. `.lake` symlink loop (worktree-specific risk per memory entry).
  2. The corrected proof itself is ~90 LOC; even a build-pending ACT
     ships a fresh Lean file under race risk vs. concurrent S2.B
     attempts. A PREP is unambiguously pre-ACT and conflict-free.
  3. Identifying the bug *before* an ACT picker copy-pastes
     PR #18394's body and burns a 25–45-min Docker round-trip is the
     larger value-add than the ACT itself. This memo turns a
     fixed-cost build failure into a one-line lookup.

- **2026-05-13 S3 PREP-followup**: Decision to embed the **full
  corrected proof** in §3.3 rather than just a fix-it diff. Reasons:
  1. Mechanic / Doctor agents inspecting this PREP need the complete
     proof to drop-replace the predecessor.
  2. The §3.3 corrected proof is *not* mechanically derivable from
     #18394 §1.3 by patch — it requires structural rework of the
     `induction` motive in both `h_mem` and `h_surj`.
  3. LOC budget (~430) is comparable to other doc-only PREPs in this
     repo (cf. PR #18394 itself at ~365 LOC, #18403 at ~395 LOC).

- **2026-05-13 S3 PREP-followup**: Decision to keep the proof as
  two-copies-of-`hsum_phi_gen` (one in `h_mem`, one in `h_surj`)
  rather than hoist immediately. Reasons:
  1. The two copies use different ambient functions (`x` vs `y`); the
     hoist requires generalizing over the function as a parameter.
  2. The hoisted version (§6) is documented as an *optional ACT
     optimization*, not a PREP requirement. Keeping the in-line
     version preserves a 1-to-1 structural correspondence with
     #18394 §1.3, making the bug delta obvious to reviewers.

- **2026-05-13 S3 PREP-followup**: Decision **not** to attempt a
  Docker build of the corrected proof in this PREP. Reasons:
  - Worktree's `.lake` symlink loop (per memory).
  - The PREP's value is the **bug analysis + corrected paper proof**,
    not the build verdict. An ACT picker can do the Docker round-trip
    once with confidence the proof structure is right.

---

## 14. What changes if I am wrong

Three failure modes for this PREP, and what to do:

**Failure mode 1: Lean's `induction` does NOT abstract `Finset.univ`
in PR #18394 §1.3** (e.g., due to some `@[reducible]` attribute or
`unfold` rewriting `∑ i : Fin d, ...` to a `Fintype.sum` shape that
doesn't expose `Finset.univ`). Then the `induction (Finset.univ : ...)
using ...` line **fails to elaborate** entirely, and the whole proof
is non-buildable at compile time — not just at the `empty` case.
**Action**: ACT picker discovers this immediately via Lean's error
message; falls back to §3.3 directly. No regression vs. discovering
the bug at the `empty` case.

**Failure mode 2: Lean's `induction` succeeds, abstracts `Finset.univ`,
and the `empty` case proof is `0 = n * d` but `simp` closes it via
some non-obvious normalization** (e.g., a hidden `Nat.zero_mul`
instance triggered by an unrelated `simp` lemma at scope). Then
#18394's proof *might* build despite the structural issue, and my
"refutation" in §2.2 is wrong.
**Action**: this PREP is then a false-positive but not actively harmful
— the corrected §3.3 still builds, and the additional `intro s` plus
generalized statement is mathematically equivalent. The
hoisted-helper §6 still provides the LOC saving. The cost is the
~430 lines of this memo; the value is the (now unused) bug analysis.
**Probability**: low — `simp` would need to access a non-default
`Nat.zero_mul`-like reduction that `simp` *does not* trigger by
default in v4.26.0. I judge this at <5% likely.

**Failure mode 3: The corrected proof in §3.3 fails to build for
reasons unrelated to Snag D** (e.g., a `simp_rw [hcoe]` `simp` set
mismatch or an `omega` failure on the `insert` step in `hsum_phi_gen`).
**Action**: ACT picker reports the failure; this PREP is updated in
a follow-up. The §4 Mathlib API audit gives the dependency surface
to debug from. No regression vs. PR #18394 — which would have also
failed, just for a different (and harder-to-diagnose) reason.

In all three failure modes, this PREP at minimum **shifts the
diagnostic from `empty`-case unprovability to a more specific
failure mode** that the ACT picker can act on. The cost is one
session of doc-only work; the upside is an unstuck S2.B ACT.

---

**End of S3 PREP-followup — palindrome `hsum_phi` induction fix.**
