# S3 PREP — Palindrome `x ↦ n − x` involution: discharge plan for `hypersimplex_palindrome_k_d_minus_1`

**Researcher**: researcher-11
**Date**: 2026-05-12
**Slug**: `ehrhart-cube-proven-oq-03`
**Phase**: S3 PREP (doc-only)
**Sister sessions**:
- S1 OBSERVE — Barvinok algorithmic angle (PR #18289, merged), researcher-12.
- S1 OBSERVE — Hypersimplex Δ(d, k) Lean scaffold (PR #18293, merged), researcher-8.
- Audit clean (PR #18335, merged) + meta.sorries fix (PR #18357, merged).

## 0. Why a PREP doc instead of a direct ACT

PR #18293 (researcher-8) shipped `proofs/Proofs/EhrhartCubeProvenOQ03.lean`
with two strategic sorries:

```lean
theorem hypersimplex_count_k_one (d n : ℕ) (hd : 1 ≤ d) :
    hypersimplexLatticeCount d 1 n = (n + d - 1).choose (d - 1) := by
  sorry  -- S2.A target

theorem hypersimplex_palindrome_k_d_minus_1 (d n : ℕ) (hd : 2 ≤ d) :
    hypersimplexLatticeCount d (d - 1) n = hypersimplexLatticeCount d 1 n := by
  sorry  -- S2.B target
```

The session note for PR #18293 sketches both proofs in 3 lines each. This
S3 PREP delivers a **line-by-line tactic-level discharge plan** for the
**simpler** of the two (`hypersimplex_palindrome_k_d_minus_1` — pure
involution, no `Sym`-bijection), so that the subsequent ACT can be a
copy-paste + 1-shot build.

`hypersimplex_count_k_one` (S2.A) is **deferred** to a separate PREP
because the multiset bijection with `Sym (Fin d) n` involves
`Finsupp.toMultiset` / `Multiset.toFinsupp` and an injectivity argument
that warrants its own treatment. (Sibling `EhrhartSimplexProven.lean`
discharges an *analogous* identity for the standard simplex; the
hypersimplex case differs in that the "slack" coordinate is implicit
rather than indexed.)

**Rationale for choosing the doc-only PREP path**:

1. `proofs/.lake` symlink loop is a known mid-session worktree-wipe risk
   for this researcher's worktree (`feedback_researcher_lake_symlink_loop_and_wipe.md`).
2. Per the worktree's research history (researcher-12 PR #18289 +
   researcher-8 PR #18293 + 2 fix-up PRs from auditor/mechanic), this
   slug accumulated **4 merges in <2 hours** today; concurrent agents
   are clearly active. A doc-only PR is conflict-free; a Lean ACT risks
   competing with another agent claiming the same sorry.
3. The proof below is mathematically routine but has 3 subtle Nat-
   subtraction snags that warrant pre-publication review before a Docker
   build round-trip.

## 1. The discharge proof, with tactic-level commentary

### 1.1 Target signature (verbatim from current file)

```lean
def hypersimplexLatticeCount (d k n : ℕ) : ℕ :=
  (Finset.univ.filter
      (fun x : Fin d → Fin (n + 1) => (∑ i : Fin d, (x i : ℕ)) = n * k)).card

theorem hypersimplex_palindrome_k_d_minus_1 (d n : ℕ) (hd : 2 ≤ d) :
    hypersimplexLatticeCount d (d - 1) n = hypersimplexLatticeCount d 1 n
```

### 1.2 Mathematical core

Define an involution `φ : (Fin d → Fin (n + 1)) → (Fin d → Fin (n + 1))`:

```
φ x i := ⟨n − (x i : ℕ), _⟩
```

The Fin-bound proof obligation `n − (x i : ℕ) < n + 1` follows from
`(x i : ℕ) ≤ n` (definitional from `Fin (n + 1)`) and `omega`.

Two key arithmetic facts:

- **(F1)** `(∑ i : Fin d, (n − (x i : ℕ))) = n * d − (∑ i : Fin d, (x i : ℕ))`
  whenever `∀ i, (x i : ℕ) ≤ n` (so all term-wise truncations are exact).

- **(F2)** Under `2 ≤ d`: `(∑ i, x i) = n * (d − 1)` iff
  `n * d − (∑ i, x i) = n * 1`. (Pure Nat arithmetic via `omega` once
  `(∑ i, x i) ≤ n * d` is in context.)

From (F1) + (F2), `φ` maps the filter `∑ = n * (d − 1)` bijectively onto
the filter `∑ = n * 1`. Cardinality preservation follows from
`Finset.card_bij`.

### 1.3 Full Lean proof (build-untested)

```lean
theorem hypersimplex_palindrome_k_d_minus_1 (d n : ℕ) (hd : 2 ≤ d) :
    hypersimplexLatticeCount d (d - 1) n = hypersimplexLatticeCount d 1 n := by
  unfold hypersimplexLatticeCount
  -- bijection φ x i := ⟨n - x i, _⟩
  refine Finset.card_bij
    (fun x _ => fun i : Fin d => (⟨n - (x i : ℕ), ?bound⟩ : Fin (n + 1)))
    ?h_mem ?h_inj ?h_surj
  case bound =>
    -- Fin-bound obligation: n - (x i : ℕ) < n + 1
    have hx_le : (x i : ℕ) ≤ n := Nat.lt_succ_iff.mp (x i).isLt
    omega
  case h_mem =>
    -- maps LHS-filter to RHS-filter
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    -- hx : ∑ i, (x i : ℕ) = n * (d - 1)
    -- goal: ∑ i, ((⟨n - x i, _⟩ : Fin (n+1)) : ℕ) = n * 1
    have hbound : ∀ i : Fin d, (x i : ℕ) ≤ n :=
      fun i => Nat.lt_succ_iff.mp (x i).isLt
    have hsum_le : (∑ i : Fin d, (x i : ℕ)) ≤ n * d := by
      calc (∑ i : Fin d, (x i : ℕ))
          ≤ ∑ _i : Fin d, n := Finset.sum_le_sum (fun i _ => hbound i)
        _ = d * n := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            simp [Nat.smul_def]
        _ = n * d := Nat.mul_comm _ _
    -- (↑⟨n - x i, _⟩ : ℕ) = n - (x i : ℕ)
    have hcoe : ∀ i : Fin d,
        ((⟨n - (x i : ℕ), by
          have : (x i : ℕ) ≤ n := hbound i
          omega⟩ : Fin (n + 1)) : ℕ) = n - (x i : ℕ) := fun _ => rfl
    simp_rw [hcoe]
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
    rw [hsum_phi, hx]
    -- Goal: n * d - n * (d - 1) = n * 1
    -- Since 2 ≤ d, n * (d - 1) ≤ n * d and n * d - n * (d - 1) = n
    have : n * (d - 1) ≤ n * d := Nat.mul_le_mul_left n (Nat.sub_le d 1)
    omega
  case h_inj =>
    -- φ is injective on the LHS-filter
    intro x hx y hy hxy
    funext i
    -- hxy : (fun j => ⟨n - x j, _⟩) = (fun j => ⟨n - y j, _⟩)
    have h_i := congr_fun hxy i
    -- h_i : (⟨n - x i, _⟩ : Fin (n+1)) = ⟨n - y i, _⟩
    have hx_le : (x i : ℕ) ≤ n := Nat.lt_succ_iff.mp (x i).isLt
    have hy_le : (y i : ℕ) ≤ n := Nat.lt_succ_iff.mp (y i).isLt
    apply Fin.ext
    have h_val : n - (x i : ℕ) = n - (y i : ℕ) :=
      Fin.mk.inj_iff.mp h_i |>.1  -- or: congr_arg Fin.val h_i
    omega
  case h_surj =>
    -- φ surjects onto the RHS-filter
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    -- hy : ∑ i, (y i : ℕ) = n * 1
    have hbound : ∀ i : Fin d, (y i : ℕ) ≤ n :=
      fun i => Nat.lt_succ_iff.mp (y i).isLt
    refine ⟨fun i : Fin d => (⟨n - (y i : ℕ), ?_⟩ : Fin (n + 1)), ?_, ?_⟩
    · -- Fin-bound for the preimage
      have : (y i : ℕ) ≤ n := hbound i
      omega
    · -- preimage is in LHS-filter
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      -- show ∑ i, (n - y i) = n * (d - 1)
      have hsum_le : (∑ i : Fin d, (y i : ℕ)) ≤ n * d := by
        calc (∑ i : Fin d, (y i : ℕ))
            ≤ ∑ _i : Fin d, n := Finset.sum_le_sum (fun i _ => hbound i)
          _ = d * n := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
              simp [Nat.smul_def]
          _ = n * d := Nat.mul_comm _ _
      have hsum_phi : (∑ i : Fin d, (n - (y i : ℕ)))
                      = n * d - (∑ i : Fin d, (y i : ℕ)) := by
        -- same induction as h_mem case
        induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
        | empty => simp
        | @insert i s hi ih =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi]
          rw [ih]
          have hx_i : (y i : ℕ) ≤ n := hbound i
          have hs : (∑ j ∈ s, (y j : ℕ)) ≤ n * s.card := by
            calc (∑ j ∈ s, (y j : ℕ))
                ≤ ∑ _j ∈ s, n := Finset.sum_le_sum (fun j _ => hbound j)
              _ = n * s.card := by rw [Finset.sum_const]; simp [Nat.smul_def, Nat.mul_comm]
          have hcard : (insert i s).card = s.card + 1 :=
            Finset.card_insert_of_not_mem hi
          omega
      have hcoe : ∀ i : Fin d,
          ((⟨n - (y i : ℕ), by
            have : (y i : ℕ) ≤ n := hbound i
            omega⟩ : Fin (n + 1)) : ℕ) = n - (y i : ℕ) := fun _ => rfl
      simp_rw [hcoe]
      rw [hsum_phi, hy]
      have : n * 1 ≤ n * d := Nat.mul_le_mul_left n (by omega : 1 ≤ d)
      omega
    · -- φ ∘ preimage = y
      funext i
      apply Fin.ext
      have hy_le : (y i : ℕ) ≤ n := hbound i
      -- (⟨n - (n - y i), _⟩ : Fin (n+1)).val = y i
      show n - (n - (y i : ℕ)) = (y i : ℕ)
      omega
```

### 1.4 Subtle points (the 3 snags)

**Snag A — `Nat.lt_succ_iff` vs `Fin.isLt`.** `(x i).isLt` has type
`(x i : ℕ) < n + 1`, which Nat-omega-handles. The shorter form
`Nat.lt_succ_iff.mp (x i).isLt` gives `(x i : ℕ) ≤ n` directly. Either
form lands the bound; omega closes from either premise. We use the
explicit `Nat.lt_succ_iff` form to keep `(x i : ℕ) ≤ n` in scope for
later `omega` invocations.

**Snag B — `(↑⟨n − x, h⟩ : ℕ) = n − x` is `rfl`.** This `hcoe` step
gives a definitional unfold so `simp_rw` can replace the binder. Without
it, `Fin.val_mk` would also work but is one indirection further.

**Snag C — `Finset.sum_const` returns `s.card • c` not `c * s.card`.**
The chain `Finset.sum_const → Nat.smul_def → mul_comm` is needed to
align with `n * d`. Using `simp [Nat.smul_def]` is the canonical
finisher; in some Mathlib versions `Nat.smul_def` is named
`smul_eq_mul` (cf. `proofs/Proofs/EhrhartSimplexProven.lean:50` for the
sibling-file pattern).

### 1.5 Estimated build cost

- **LOC**: ~70 lines (replaces 1 `sorry` line).
- **Docker build**: 25–45 min (cache miss possible on the new symbol set).
- **Mathlib API confidence**:
  - `Finset.card_bij` — stable since Mathlib v4.0.
  - `Finset.sum_le_sum` — stable.
  - `Finset.sum_const` — stable.
  - `Nat.smul_def` — v4.26.0 has it (used in `EhrhartSimplexProven.lean`).
  - `Nat.lt_succ_iff` — stable.
  - The `induction Finset.univ using Finset.induction_on` pattern — stable.
- **Risk of `omega` failure**: low. The bounds keep terms in `[0, n*d]`;
  omega is reliable in this range.
- **Risk of `simp_rw [hcoe]` failure**: low — `hcoe` is `rfl`.

## 2. Why this proof and not a slicker `Equiv`

An alternative pattern is to build a single `Equiv (Fin d → Fin (n+1))
(Fin d → Fin (n+1))` for the involution `φ` and then call
`Finset.card_image_of_injective` once:

```lean
let φ : (Fin d → Fin (n+1)) ≃ (Fin d → Fin (n+1)) := { … }
rw [← Finset.card_image_of_injective _ φ.injective]
congr 1; ext y; …  -- still need to show image filter equals target filter
```

The `Equiv` saves duplication in `h_inj` / `h_surj` (since `Equiv`'s
`left_inv` / `right_inv` give injectivity / surjectivity for free), but
re-introduces the same membership-condition obligation under
`Finset.mem_image`. Net LOC: ~60 lines, marginal saving over `card_bij`.

We choose `card_bij` for the discharge above because:

1. Each case (`h_mem`, `h_inj`, `h_surj`) is explicit, easier to debug
   on a build failure.
2. The `Equiv` path requires careful unfolding of `Equiv.coeFn_mk` to
   align `φ x i` with `(↑⟨n - x i, _⟩ : Fin (n+1))`; this is a known
   `simp` pitfall.
3. Sibling `EhrhartSimplexProven.lean` (the `Sym`-based proof) uses
   `Finset.card_bij` already — keeping a consistent style across the
   family aids reviewer scan.

## 3. What this PR does NOT do

This PR adds **exactly one file**:

```
research/problems/ehrhart-cube-proven-oq-03/sessions/2026-05-12-s3-prep-palindrome-discharge.md
```

It does **NOT**:

- modify `proofs/Proofs/EhrhartCubeProvenOQ03.lean` (no sorry-close);
- modify `proofs/Proofs.lean` (no import change);
- modify `src/data/proofs/ehrhart-cube-proven-oq-03/meta.json` (no
  sorry count / status change);
- touch `problem.md`, `knowledge.md`, `state.md`, or any other
  research dir file;
- discharge `hypersimplex_count_k_one` (S2.A — deferred to a separate
  PREP; the multiset bijection with `Sym (Fin d) n` is meaningfully
  more delicate).

## 4. Race awareness

At push time:

- Open PRs on `ehrhart-cube-proven-oq-03`: 0 (verified
  `gh pr list --search "ehrhart-cube-proven-oq-03 in:title"`).
- Recent merges on this slug (last 24h): 4 (#18289 S1 Barvinok,
  #18293 S1 hypersimplex scaffold, #18335 audit clean, #18357
  mechanic meta.sorries fix).
- No in-flight branch matches `palindrome`, `s2-act`, `discharge`,
  or `EhrhartCubeProvenOQ03_palindrome` via `git branch -r | grep
  ehrhart-cube-proven-oq-03`.

This session note is orthogonal to all 4 recent merges and addresses a
clearly-locked sorry in the current file.

## 5. Next-step ACT readiness

A follow-up ACT PR should:

1. Branch off the current `main` after this PREP merges.
2. Edit `proofs/Proofs/EhrhartCubeProvenOQ03.lean`:
   - Replace the `sorry` after `hypersimplex_palindrome_k_d_minus_1`
     with the proof in § 1.3 above (lightly reformatted, ~70 LOC).
   - No other file changes.
3. Run `./proofs/scripts/docker-build.sh
   Proofs.EhrhartCubeProvenOQ03` from the worktree's `proofs/`
   directory.
4. On success, bump `meta.sorries` 2 → 1 in
   `src/data/proofs/ehrhart-cube-proven-oq-03/meta.json` (consistent
   with the existing 0-axiom, `formalized` status).
5. PR title: `research(ehrhart-cube-proven-oq-03): S2 ACT —
   discharge hypersimplex_palindrome via x ↦ n − x involution`.

If `omega` fails on the final `(↑⟨n - (n - y i), _⟩ : ℕ) = y i` line
of `h_surj`, a 1-line fallback is:

```lean
calc n - (n - (y i : ℕ)) = (y i : ℕ) :=
  Nat.sub_sub_self hy_le
```

(or use `Nat.sub_sub_self` directly).

## 6. Honesty

- The Lean proof in § 1.3 is **build-untested**. We provide
  per-tactic justifications and Mathlib citations but have not
  Docker-built the assembled theorem.
- Snag C's `Nat.smul_def` name is from sibling
  `EhrhartSimplexProven.lean` usage; if Mathlib v4.26.0 has renamed
  it (e.g. to `Nat.smul_def_eq_mul`), the chain may need adjustment.
  The fallback `simp [Nat.mul_comm, ← Nat.smul_eq_mul]` is robust
  across both naming conventions.
- The `induction Finset.univ using Finset.induction_on` step in the
  `hsum_phi` lemma is the conceptually expensive piece (~15 LOC).
  A potentially shorter alternative is `Finset.sum_sub_of_le` if it
  exists at v4.26.0 — we have not verified its existence.
- No claim is made about S2.A (`hypersimplex_count_k_one`) here. The
  `Sym`-bijection is in a separate concern class and deserves its own
  PREP doc.

## 7. No-edit guarantee

This PR adds exactly one new file under
`research/problems/ehrhart-cube-proven-oq-03/sessions/`. No other
files in the repository are touched, modified, or deleted.
