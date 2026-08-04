import Proofs.CycleDoubleCoverPort.GeneralGraph
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Cast.Lemmas

/-
# Cycle Double Cover port, step 5a: reducing an integral 6-flow modulo eight

Slice of the port of the openai/cdc-lean development of the Cycle Double Cover
theorem (Szekeres 1973 / Seymour 1979, resolved 2026) into this gallery. It
corresponds to upstream `CDCLean/SixFlow.lean`; see #37507 for the porting
order, #43625 for step 1 (`GeneralGraph.lean` / `CycleDecomposition.lean`) and
#43626 for step 2 (`Basic.lean` / `EvenCover.lean`).

## Provenance and licensing

`openai/cdc-lean` carries **no license file**, so default copyright applies and
no proof text may be vendored. This file is an *independent re-derivation*: the
upstream source was consulted only for the mathematical content — the shape of
the definition and the statement of the result — and every proof script here was
written from scratch against this repository's Mathlib pin. In particular the
conservation half is obtained from a general pushforward lemma
(`FiniteGraph.IsFlow.map`, new here) rather than by rewriting the cast through
the flow equation by hand, and the nowhere-zero half runs on a divisibility
witness plus `omega` rather than on `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs`.

## Mathematical content

Seymour's six-flow theorem produces an *integral* circulation whose edge values
`n` satisfy `1 ≤ |n| ≤ 5`. The first step towards the `F₂³`-valued flow that the
labelling stage consumes is to view that circulation modulo eight.

Two things have to be checked, and they are of very different weights.

* Conservation survives, for the cheap reason that reduction `ℤ → ZMod 8` is an
  additive homomorphism and the flow condition is a linear identity. This is not
  special to `8`, or even to `ZMod`: `IsFlow.map` below records it for an
  arbitrary `φ : A →+ B`.
* Nowhere-zeroness survives because the reduction cannot collapse a value of
  absolute value at most `5` onto `0`: that would force `8 ∣ n` with `n ≠ 0`,
  hence `|n| ≥ 8`. This *is* where the numerical slack is spent, and it is the
  only place in the file where the bound from `SixFlow` is used.

The choice of modulus `8` is not forced by the second point — any modulus `≥ 6`
would keep the values nonzero, and `ZMod 6` would do. Eight is chosen because
`ZMod 8` and `F₂³ = Gamma` are the two groups of order eight that the next stage
compares: the transfer from a nowhere-zero `ZMod 8`-flow to a nowhere-zero
`Gamma`-flow is a genuine theorem about the *number* of nowhere-zero flows
(Tutte's flow-count invariance, upstream `FlowCount.lean`, followed by the
Jaeger–Kilpatrick eight-flow theorem), not a reindexing. Nothing of that content
is hidden in the definition below; this file is exactly the elementary first
step.

## Deliberate omissions

Upstream's `FlowCount.lean` — the flow-count polynomial invariance that turns
this `ZMod 8`-flow into a `Gamma`-flow — is a sibling slice of step 5 and is
**not** ported here. This file does not discharge
`CycleDoubleCover.cycleDoubleCover_of_bridgeless`, nor does it prove Seymour's
theorem: `FiniteGraph.SeymourSixFlowStatement` (step 1) remains an explicit
hypothesis, carried as an argument by the corollary at the end of the file
rather than as an ambient axiom.
-/

namespace CycleDoubleCover

namespace FiniteGraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : FiniteGraph V E)

omit [DecidableEq E] in
/-- Flows push forward along additive homomorphisms. Conservation is a linear
identity in the edge values, so any `φ : A →+ B` carries an `A`-valued flow to a
`B`-valued one; no hypothesis on `φ` beyond additivity is needed, and in
particular nothing here sees the modulus used later. -/
theorem IsFlow.map {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A →+ B)
    {f : E → A} (hf : G.IsFlow f) : G.IsFlow fun e => φ (f e) := by
  intro v
  have h : φ ((∑ e : E, if G.endAt e 0 = v then f e else 0) -
      (∑ e : E, if G.endAt e 1 = v then f e else 0)) = 0 := by
    rw [hf v, map_zero]
  simpa only [map_sub, map_sum, apply_ite, map_zero] using h

omit [DecidableEq E] in
/-- The edge values of an integral 6-flow are nonzero. Immediate from the lower
half of the bound, but worth naming: it is the hypothesis that survives the
reduction. -/
theorem SixFlow.val_ne_zero (sf : G.SixFlow) (e : E) : sf.val e ≠ 0 := by
  have h := (sf.bound e).1
  intro hz
  rw [hz] at h
  simp at h

omit [DecidableEq E] in
/-- The edge values of an integral 6-flow have absolute value at most five: the
numerical slack that makes reduction modulo eight harmless. -/
theorem SixFlow.natAbs_le_five (sf : G.SixFlow) (e : E) :
    Int.natAbs (sf.val e) ≤ 5 :=
  Nat.lt_succ_iff.mp (sf.bound e).2

/-- Reduction of Seymour's integral circulation modulo eight.

Conservation is inherited from `IsFlow.map` applied to `Int.castAddHom`.
Nowhere-zeroness is the only step that consumes the `SixFlow` bound: a value
killed by the reduction would be a nonzero multiple of eight of absolute value
at most five. -/
def SixFlow.toZModEight (sf : G.SixFlow) : G.NowhereZeroFlow (ZMod 8) where
  val e := ((sf.val e : ℤ) : ZMod 8)
  conservation := by
    have h := IsFlow.map G (Int.castAddHom (ZMod 8)) sf.conservation
    simpa only [Int.coe_castAddHom] using h
  nowhereZero := by
    intro e he
    have hdvd : (8 : ℤ) ∣ sf.val e := by
      have h8 := (ZMod.intCast_zmod_eq_zero_iff_dvd (sf.val e) 8).mp he
      exact_mod_cast h8
    obtain ⟨k, hk⟩ := hdvd
    obtain ⟨hpos, hlt⟩ := sf.bound e
    rcases Int.natAbs_eq (sf.val e) with hcase | hcase <;> omega

omit [DecidableEq E] in
@[simp]
theorem SixFlow.toZModEight_val (sf : G.SixFlow) (e : E) :
    (sf.toZModEight).val e = ((sf.val e : ℤ) : ZMod 8) :=
  rfl

/-- Every bridgeless graph carries a nowhere-zero `ZMod 8`-flow, *given*
Seymour's six-flow theorem. Seymour's theorem is taken as an explicit hypothesis
(`SeymourSixFlowStatement`, the trust boundary fixed in step 1) rather than as an
axiom, so this statement is unconditional Lean content: it says precisely that
the reduction step above loses nothing. -/
theorem nonempty_nowhereZeroFlow_zmodEight_of_seymour
    (hs : SeymourSixFlowStatement.{u, v}) (hb : G.Bridgeless) :
    Nonempty (G.NowhereZeroFlow (ZMod 8)) :=
  (hs V E G hb).map fun sf => sf.toZModEight

end FiniteGraph

end CycleDoubleCover

