# Knowledge Base: abel-ruffini-galois-extensions-oq-03-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-07-02 (Session 1, researcher-4) — Isolate the classical core

**Mode**: FRESH · **Outcome**: progress (ORIENT) · **PR**: #33855

### What I did
- Read Mathlib `GroupTheory/SpecificGroups/Alternating.lean`: confirmed Mathlib
  proves simplicity only for `Fin 5` (`isSimpleGroup_five`) but supplies all the
  generic converse machinery (`IsThreeCycle.alternating_normalClosure`,
  `isThreeCycle_isConj`, `closure_three_cycles_eq_alternating`).
- Confirmed the parent `AbelRuffiniGaloisExtensionsOQ03` already **verified** the
  formal reduction (simplicity ⇐ every nontrivial normal subgroup has a 3-cycle).
- Isolated the sole open content as the single lemma
  `exists_mem_isThreeCycle_of_normal` and wrote a self-contained (Mathlib-only)
  WIP file `AbelRuffiniGaloisExtensionsOQ03OQ01.lean`:
  re-inlined reduction (0 sorry) + stated lemma (1 sorry, HARD) + assembled
  `isSimpleGroup_alternating`.
- **Single-file elaborated** the file against Mathlib v4.26.0 via `lake env lean`:
  0 errors, only the expected `sorry` warning ⇒ statement + assembly typecheck.

### Key findings
- The entire remaining mathematical content of general Aₙ simplicity is this one
  lemma; the assembly is a one-liner once it lands.
- Correct proof route is **Jordan's minimal-support / commutator argument** (pick
  σ ∈ H of minimal support; commutators [τ,σ] ∈ H of strictly smaller support
  force σ to be a 3-cycle), *not* Mathlib's Fin-5 explicit casework (does not
  generalize). Base case: even perm on exactly 3 points is a 3-cycle
  (`card_support_eq_three_iff`).
- Confirmed all needed Mathlib API exists: `support_conj`, `card_support_conj`,
  `support_mul_le`, `sum_cycleType`, `two_le_of_mem_cycleType`,
  `isThreeCycle_swap_mul_swap_same`, `Normal.conj_mem`, `Finset.exists_min_image`.

### Blockers (environment, not mathematical)
- Aristotle MCP down all session (`Resource not found` / 404) — could not delegate
  the HARD lemma remotely.
- Local Docker build corrupted (containerd metadata I/O error, lingering from a
  prior disk-full episode) — could not run `docker-build.sh`; used single-file
  `lake env lean` against prebuilt Mathlib oleans instead.

### Next steps
- When Aristotle returns: submit `exists_mem_isThreeCycle_of_normal` async with the
  minimal-support/commutator hint (KNOWN math → Aristotle's strength).
- Manual route (needs working build loop): prove a reusable commutator-support
  bound, then the two cycle-type cases (≥3-cycle present; product of ≥2
  transpositions), reducing support to 3.
- On completion: promote to a verified gallery entry + consider a Mathlib PR
  (general `alternatingGroup.isSimpleGroup`).

---

## Session 2026-07-02 (Session 2, researcher-14) — Decompose the crux; discharge the scaffolding

**Mode**: CONTINUE (on #33855) · **Outcome**: progress (REDUCE) · **PR**: (this session)

### What I did
- Took researcher-4's monolithic `sorry` (the whole 3-cycle containment lemma) and
  **decomposed + discharged the entire surrounding argument**, leaving a *single*
  sharply-focused `sorry` (the strict-support-decrease commutator step for
  `#support ≥ 4`).
- **Proved (0 sorry, machine-checked)** four reusable lemmas:
  - `three_le_card_support_of_mem` — a nontrivial *even* perm moves ≥ 3 points
    (support ≠ 0 via `support_eq_empty_iff`; ≠ 1 via `card_support_ne_one`; ≠ 2
    because `card_support_eq_two → IsSwap → sign = -1`, contradicting evenness).
  - `commutator_mem_of_normal` — `τ σ τ⁻¹ σ⁻¹ ∈ H` for `H ⊴ Aₙ`, `σ ∈ H`
    (`Normal.conj_mem` + `inv_mem`).
  - `exists_min_support_ne_one` — minimal-support nonidentity element exists
    (`Finset.exists_min_image` over `univ.filter (· ∈ H ∧ · ≠ 1)`).
  - `support_commutator_subset` — **the containment half of the crux**: if
    `τ.support ⊆ σ.support` then `(τστ⁻¹σ⁻¹).support ⊆ σ.support`
    (`τ` maps `σ.support` into itself; `support_mul_le` + `support_conj` +
    `support_inv`).
- Reassembled `isThreeCycle_of_min_support` (the crux) with its `3 ≤ #support` and
  `#support = 3 ⇒ 3-cycle` branches proved in-line; `exists_mem_isThreeCycle_of_normal`
  and `isSimpleGroup_alternating` now compile (0 sorry beyond the crux).
- **Verified**: single-file `lake env lean` against Mathlib v4.26.0 → EXIT 0, exactly
  one `sorry` warning; 1 code-level `sorry` (line ~233). md5-checked the worktree file.

### Key findings
- The remaining kernel is exactly: *for a minimal-support even σ with `#support ≥ 4`,
  produce a 3-cycle `τ ⊆ σ.support` whose commutator `[τ,σ]` is `≠ 1` and fixes at
  least one point that σ moves.* Given that, `support_commutator_subset` +
  `commutator_mem_of_normal` + minimality + `card` monotonicity finish it (the
  commutator lands strictly inside `σ.support`, contradicting minimality).
- Two Lean gotchas fixed: `simp [Subtype.ext_iff]` and `simp [Finset.mem_filter]`
  both hit `maximum recursion depth` on nested-subgroup membership — replaced with
  `OneMemClass.coe_eq_one` and explicit `Finset.mem_filter.mp/.mpr`.

### Blockers (environment, not mathematical)
- Aristotle MCP still down all session (`Resource not found` / 404).
- Main-repo Mathlib olean cache intermittently corrupted by concurrent builds
  (`*.olean.private invalid header`); elaborated against a *sibling worktree's*
  warm cache (`lg-r13-oq03/proofs`) instead. Cache location churns as other agents
  run `lake update`.

### Next steps
- The sole remaining `sorry` (`isThreeCycle_of_min_support`, `#support ≥ 4`): supply
  the existence of the adapted 3-cycle `τ` and the "fixes a moved point" property.
  Split on cycle type (Case A: a cycle of length ≥ 3; Case B: ≥ 2 disjoint
  transpositions). This is the ~300–800-line kernel; best via Aristotle (down) or a
  focused session.
- On completion: verified gallery entry + candidate Mathlib PR (general
  `alternatingGroup.isSimpleGroup`).

## Session 2026-07-03 (Session 3, researcher-16) — Prove the Case A strict-decrease engine

**Mode**: DEEP DIVE (continues #33855 isolate → #33912 four-lemma decomposition)
**Outcome**: progress (1 new 0-sorry lemma; still 1 crux sorry) · **PR**: (this session)

### What I did
- Aristotle MCP still down (`Resource not found`/404) — manual formalization only.
  Elaborated via `lake env lean <abs worktree path>` against main's prebuilt
  Mathlib oleans (durable worktree `/Users/rwalters/lg-r16-abelruffini`; the
  `.loom/worktrees/researcher-16` copy was reaped mid-session, as usual).
- Proved **`exists_smaller_commutator_of_five_points`** (0 sorry): the quantitative
  *engine* of the `#support ≥ 4` crux branch for the cycle-of-length-≥3 case.
  Given five distinct points `a,b,c,d,e` with `b,c,d,e ∈ supp σ`, `σ a = b`,
  `σ b = c`, the commutator `ρ = τ σ τ⁻¹ σ⁻¹` with the 3-cycle
  `τ = swap c d * swap c e = (c d e)` is a nonidentity element of `H` with
  `#supp ρ < #supp σ`.
- Re-elaborated whole file: EXIT 0, exactly one `sorry` (crux `#support ≥ 4`
  branch), 10 theorems.

### Key findings (the exact working construction)
- Take `τ = swap c d * swap c e` (`isThreeCycle_swap_mul_swap_same hcd hce hde`
  gives `IsThreeCycle`, hence `mem_alternatingGroup`). `τ.support ⊆ {c,d,e}` via
  `support_mul_le` + `support_swap` (no need for the *exact* support set).
- **ρ ≠ 1**: compute `ρ c = τ(σ(τ⁻¹(σ⁻¹ c))) = τ(σ(τ⁻¹ b)) = τ(σ b) = τ c = e ≠ c`.
  Uses `σ⁻¹ c = b` (from `σ b = c`, `Equiv.symm_apply_apply`), `τ⁻¹ b = b` and
  `τ b = b` (as `b ∉ τ.support`), `τ c = e` (`mul_apply`+`swap_apply_left`+
  `swap_apply_of_ne_of_ne`).
- **strict decrease**: `ρ b = τ(σ(τ⁻¹(σ⁻¹ b))) = τ(σ(τ⁻¹ a)) = τ(σ a) = τ b = b`,
  so `b ∉ ρ.support`; with `ρ.support ⊆ σ.support` (the already-proved
  `support_commutator_subset`) and `b ∈ σ.support` this gives a *strict* subset
  (`Finset.ssubset_iff_of_subset` + `Finset.card_lt_card`).
- Note: the a,b,c hypothesis `σ a = b, σ b = c` are exactly what `σ² ≠ 1` yields
  (set `a` with `σ² a ≠ a`, `b = σ a`, `c = σ² a`; all three are moved & distinct).
- `Equiv.Perm.inv_apply_self` is DEPRECATED → use `Equiv.symm_apply_apply` (works
  on `sp⁻¹` by defeq `sp⁻¹ = sp.symm`).

### What remains for the crux (`#support ≥ 4` branch)
1. **Case A extraction**: when `σ² ≠ 1`, produce `a,b,c` (above) plus two more
   moved points `d,e` — needs `#supp σ ≥ 5`. Ruling out `#supp σ = 4` in this case
   needs the parity fact "even + `σ² ≠ 1` ⇒ not a single 4-cycle" (cycleType).
   Then `exists_smaller_commutator_of_five_points` closes it against minimality.
2. **Case B (`σ² = 1`, disjoint transpositions, ≥2 of them)**: needs its OWN engine
   — `σ = (a b)(c d)…`, pick a 5th point `e` (n ≥ 5), `τ = (c d e)`; then
   `[τ,σ]` is a 3-cycle on `{c,d,e}` (support 3 < 4), NOT ⊆ supp σ. A second
   engine lemma with a general `#supp([τ,σ]) < #supp σ` count is required.

### Blockers (environment, not mathematical)
- Aristotle MCP down all session (404). Docker build not attempted (single-file
  `lake env lean` sufficed and is faster with warm oleans).

## Session 2026-07-03 (Session 4, researcher-4) — Crux discharged: file VERIFIED (0 sorry, 0 axiom)

**Mode**: DEEP DIVE (continues #33855 → #33912 → #33923) · **Outcome**: SOLVED · **PR**: (this session)

### What I did
- **Proved `exists_smaller_commutator_of_involution` (Case B engine, 0 sorry)** — the
  missing counterpart to the existing Case A engine. Parity-free: needs only five
  distinct points `a,b,c,d,e` with `σ` swapping `a↔b`, `c↔d` (no global `σ²=1`, no
  condition on `σe`). Take `τ=(c e d)=swap c d * swap c e`; then `ρ=τστ⁻¹σ⁻¹∈H`,
  `ρ d = e ≠ d` (so `ρ≠1`), `ρ` **fixes both `a` and `b`**, and
  `ρ.support ⊆ {c,d,e,σe}`. Case-split on `e∈σ.support`: if not, `σe=e` ⟹
  `ρ.support⊆{c,d,e}` (≤3<4≤#σ); if so, `σ` moves all five points ⟹ `#σ≥5>4≥#ρ`.
- **Wired the crux `isThreeCycle_of_min_support` completely (0 sorry):**
  `by_cases σ²=1`.
  - `σ²=1` (**Case B**): extract `a`(∈support), `b=σa`, `c`(∈support\{a,b}),
    `d=σc`, `e`(∉{a,b,c,d}); apply Case B engine → smaller element → contradict `hmin`.
  - `σ²≠1` (**Case A**): `a=x, b=σx, c=σ²x` (three distinct moved points on one
    cycle); sub-split on `#support`. `≥5`: two more moved points `d,e` → Case A
    engine. `=4`: `σ` is the 4-cycle `(x,σx,σ²x,d)`, **odd** by `IsCycle.sign`
    (`sign = -(-1)^4 = -1`), contradicting `σ∈Aₙ` (`sign=1`).
- **Verified**: single-file `lake env lean` against Mathlib v4.26.0 → EXIT 0, **0
  errors, 0 sorry, 0 warnings**. `#print axioms isSimpleGroup_alternating` →
  `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`, no `Lean.ofReduceBool`).

### Key Lean lessons
- `Finset.card_sdiff` in Mathlib v4.26 has **no subset-hypothesis form**
  (`(s\t).card = s.card - (t∩s).card`). For "a point outside a small set exists",
  use `Finset.ssubset_iff_subset_ne` + `Finset.exists_of_ssubset` instead.
- Cycle recognition: `SameCycle.refl` + `sameCycle_apply_right.mpr` chains one step
  at a time (`x → σx → σ²x → σ³x`); `Equiv.Perm.apply_mem_support` keeps images in
  the support; `Equiv.Perm.IsCycle.sign : sign f = -(-1)^#f.support` gives parity.
- `rcases hy' with rfl | …` can substitute the WRONG variable (kills `x`); use named
  `h` + `rw [h]` (which also auto-closes `SameCycle x x` via its `@[refl]` lemma).

### Result / next steps
- The single classical open content of general Aₙ-simplicity is now fully machine-
  checked. Candidate for promotion to a verified gallery entry and a Mathlib PR
  (`alternatingGroup.isSimpleGroup` for `5 ≤ card α`).
- Aristotle MCP was **down all session** (`Resource not found`/404); the entire crux
  was formalized by hand.
