# erdos-998-oq-04 — Session 7 (researcher-3, 2026-06-19)

## Context

The three STEP A *primitives* are committed on branch
`research/erdos-998-oq04-step-a-transport` (HEAD `138b3b17`, awaiting first build
+ PR via the gated build watcher):

- `fract_fract_sub_fract` — `{ {x} − {y} } = { x − y }`
- `orbit_index_injective` — `i ↦ {iα}` is `Function.Injective` (irrational α)
- `orbit_erase_eq` — `(orbit α N).erase {kα} = image f ((range N).erase k)`

This session does **no Lean edits** (the committed primitives are still UNBUILT —
the watcher's pending build is their first verification, so appending more
unverified code would risk turning that build RED and sinking the STEP A PR).
Aristotle is still down (`prove_file` → 404 "Resource not found", consistent with
sessions 4–6). Docker fleet busy (load ~14–20, 5 lean containers).

Instead it records the **next lemma** — the forwardGap → index-difference-min
reduction that *combines* the three primitives — as a turnkey proof with
mathlib signatures verified against
`proofs/.lake/packages/mathlib/Mathlib/Data/Finset/Lattice/Fold.lean`.

## Verified mathlib signatures (Fold.lean)

```
-- line 919, @[simp]
theorem Finset.inf'_image [DecidableEq β] {s : Finset γ} {f : γ → β}
    (hs : (s.image f).Nonempty) (g : β → α) :
    (s.image f).inf' hs g = s.inf' hs.of_image (g ∘ f)

-- line 907, @[congr]
theorem Finset.inf'_congr {t : Finset β} {f g : β → α}
    (h₁ : s = t) (h₂ : ∀ x ∈ s, f x = g x) :
    s.inf' H f = t.inf' (h₁ ▸ H) g
```

`Finset.Nonempty s` is a `Prop`, so the nonemptiness witnesses carried by `inf'`
are proof-irrelevant — `s.inf' H f = s.inf' H' f` definitionally. No need to
thread the exact `H`.

## Turnkey lemma (STEP A completion — UNBUILT, integrate after watcher lands)

Place after `orbit_erase_eq` (≈ line 191), before the proof-path comment.

```lean
/-- **STEP A — forward gap as a min of index-difference fractional parts.**
    For irrational `α` and `k` with the other indices nonempty, the cyclic
    forward gap at the orbit point `{kα}` equals the minimum, over the remaining
    indices `i ∈ (range N).erase k`, of `{ (i − k)·α }` (written additively as
    `Int.fract ((i:ℝ)*α − (k:ℝ)*α)`).  Combines all three STEP A primitives. -/
theorem forwardGap_eq_index_min {α : ℝ} (hα : Irrational α) (N k : ℕ)
    (hne : ((Finset.range N).erase k).Nonempty) :
    forwardGap α N (Int.fract ((k : ℝ) * α)) =
      ((Finset.range N).erase k).inf' hne
        (fun i => Int.fract ((i : ℝ) * α - (k : ℝ) * α)) := by
  -- The punctured orbit is nonempty (image of the nonempty index set).
  have horbit_ne : ((orbit α N).erase (Int.fract ((k : ℝ) * α))).Nonempty := by
    rw [orbit_erase_eq hα]; exact hne.image _
  -- Unfold the total `forwardGap` on its nonempty branch.
  unfold forwardGap
  rw [dif_pos horbit_ne]
  -- Transport the inf' across `orbit_erase_eq` (set rewrite under inf').
  rw [Finset.inf'_congr horbit_ne (orbit_erase_eq hα N k) (fun _ _ => rfl)]
  -- Push inf' through the image: g ∘ f with f i = {iα}, g y = {y − {kα}}.
  rw [Finset.inf'_image]
  -- Now the summand is `fun i => Int.fract (Int.fract (i·α) − Int.fract (k·α))`;
  -- collapse it via the fract-of-fract primitive to `Int.fract (i·α − k·α)`.
  refine Finset.inf'_congr _ rfl (fun i _ => ?_)
  simpa using fract_fract_sub_fract ((i : ℝ) * α) ((k : ℝ) * α)
```

### Risk notes for the integrator

1. `Finset.inf'_image` is `@[simp]` and stated with `(s.image f).inf' hs g`.
   After the `inf'_congr` rewrite the LHS set is literally
   `((range N).erase k).image (fun i => Int.fract ((i:ℝ)*α))`, so `inf'_image`
   should fire by `rw`. If `rw` cannot unify the implicit `hs`, fall back to
   `simp only [Finset.inf'_image]` (proof-irrelevant witness).
2. The final `simpa using fract_fract_sub_fract (i·α) (k·α)` discharges
   `Int.fract (Int.fract (i·α) − Int.fract (k·α)) = Int.fract (i·α − k·α)`. If
   the `g ∘ f` β-redex is not reduced, prefix with `simp only [Function.comp]`.
3. Proof-irrelevance means the `hne`/`horbit_ne`/`hs.of_image` witnesses never
   need to match syntactically.

## After this lemma — remaining frontier (unchanged from session 6)

- **STEP B**: split the index-difference min on the sign of `d = i − k` into
  forward `F_k` / backward `B_k` halves (`Finset.inf'_union`, range reindexing).
- **STEP C**: subset-min bounds `F_k ≥ a`, `B_k ≥ b` + extremal attainment
  (`Finset.inf'_le`, `Finset.le_inf'`, `Finset.inf'_mem`).
- **STEP D**: the genuine Steinhaus crux — `min(F_k,B_k) ∈ {a,b,a+b}` via
  minimality of the first-return generators `p,q`. Pure `Nat`/order arithmetic,
  no new mathlib infra. This is the one HARD (known, not open) obligation.

When Aristotle recovers: submit the whole file to `prove_file` with STEPS A–C as
warm-up lemmas, or attack STEP D directly.
