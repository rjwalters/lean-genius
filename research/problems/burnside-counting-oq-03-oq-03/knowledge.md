# Knowledge Base: burnside-counting-oq-03-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

The problem asks to eliminate 5 axioms from `BurnsideCounting.lean` by bridging
`AddAction (ZMod n)` to the `MulAction` orbit-counting API.

**KEY FINDING (researcher-6, 2026-07-01):** All 5 axioms are ALREADY eliminated in
the current `proofs/Proofs/BurnsideCounting.lean` (0 `axiom` declarations, 0 sorries):

1. `rotatedIndex_add` — full unconditional Nat-modular proof (8-leaf case split, PR #21148 / S1)
2. `coloringSetoid` — now `def ... := AddAction.orbitRel (ZMod n) (Coloring n k)` (S2)
3. `coloringQuotientFintype` — now `def` via `Quotient.fintype` + a decidable-orbit-relation instance (S2)
4. `fixed_point_sum_binary_4` — `native_decide` (S3)
5. `binary_necklaces_4` — `native_decide` on the computable orbit-quotient card (S4)

So the *literal* goal ("collapse to native_decide or Mathlib lemmas") is DONE. The
gallery meta correctly reports `status: axiomatized`, `axiomCount: 1`, `badge: axiom`,
because the two `native_decide` calls introduce `Lean.ofReduceBool` (per the project's
Axiom Integrity Policy).

## The only remaining upgrade: native_decide → kernel-checked (badge → verified)

To reach `badge: verified` the two `native_decide` calls must become kernel-checked.
Mapped route (all API confirmed present in the vendored Mathlib):

- **No MulAction bridge is needed.** Mathlib has the *additive* Burnside lemma directly:
  `AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup (G) (X)` (the `to_additive`
  image of `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`,
  `Mathlib/GroupTheory/GroupAction/Quotient.lean:257`). It states
  `∑ a : G, card (AddAction.fixedBy X a) = card (AddAction.orbitRel.Quotient G X) * card G`.
- `AddAction.orbitRel.Quotient G X` is *definitionally* `Quotient (AddAction.orbitRel G X)`
  (`orbitRel.Quotient` is an `abbrev := _root_.Quotient (orbitRel G α)`,
  `Mathlib/GroupTheory/GroupAction/Defs.lean:344`), i.e. exactly `Quotient (coloringSetoid 4 2)`.
- `AddAction.mem_fixedBy : a ∈ fixedBy X g ↔ g +ᵥ a = a` is `Iff.rfl` (to_additive of
  `mem_fixedBy`, `Defs.lean:138`), so `fixedBy (Coloring 4 2) r` is the same subtype as
  `{c // IsFixedByRotation r c}` (recall `IsFixedByRotation r c := r +ᵥ c = c`).
- `ZMod.card 4 : Fintype.card (ZMod 4) = 4` (`Mathlib/Data/ZMod/Defs.lean:168`).
- `Fin.sum_univ_four` decomposes the sum over `ZMod 4 ≡ Fin 4`.
- Then `24 = card(quotient) * 4 ⟹ card(quotient) = 6` by `omega`.

The four fixed-point counts (16, 2, 4, 2) can be obtained WITHOUT `native_decide` by
reusing the file's already-fully-proved bijection lemmas
(`binary_4_colorings_count = 16`, `constant_coloring_count = 2`, `period2_count = 4`)
through characterization iffs and `Equiv.subtypeEquivRight`:
- `IsFixedByRotation 0 c ↔ True`      (Fix(0) = all colorings, via `zero_vadd`) → 16
- `IsFixedByRotation 1 c ↔ IsConstant c`   → 2
- `IsFixedByRotation 2 c ↔ HasPeriod2 c`   → 4
- `IsFixedByRotation 3 c ↔ IsConstant c`   → 2

## Insights

- The whole "AddAction → MulAction bridge" framing in problem.md is a NON-issue:
  Mathlib's `to_additive` already provides the entire additive orbit-counting API,
  including Burnside. Future necklace/orbit-counting formalizations should use the
  `AddAction.*` names directly rather than constructing a `MonoidHom` bridge.
- `orbitRel.Quotient`/`AddAction.orbitRel.Quotient` being a plain `abbrev` for
  `Quotient (orbitRel …)` means the file's `coloringSetoid`/`coloringQuotientFintype`
  line up definitionally with Mathlib's Burnside statement — no `Fintype`-diamond
  rewriting beyond `Subsingleton (Fintype _)` / `Fintype.card_eq`.

## Open experiment (build-gated)

Does *kernel* `decide` (not `native_decide`) evaluate `Fintype.card {c : Fin 4 → Fin 2 // P c}`
(16-element function-space enumeration)? If yes, `fixed_point_sum_binary_4` closes by
`decide` with a one-token change and `binary_necklaces_4` closes via the additive-Burnside
chain above — the whole entry becomes kernel-verified. If kernel `decide` blows up on
the Pi-type enumeration (the likely reason S3/S4 chose `native_decide`), the bijection
route above is the fallback. Draft scaffold: `drafts/BurnsideCountingVerified.draft.lean`.

## Dead Ends

- Building was blocked this session: 5–7 concurrent `lean-build` docker containers share
  one `.lake/build` cache volume; building concurrently causes SIGBUS (see r6 memory notes).
  Build only when `docker ps | grep lean-build` is empty.
