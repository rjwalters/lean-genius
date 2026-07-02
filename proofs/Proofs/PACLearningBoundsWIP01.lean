import Mathlib

/-
# PAC Learning, wip-01 — Foundations of VC Dimension: Shattering, Traces, and the |H| Bound

The parent entry `pac-learning-bounds` (PAC Learning and VC Dimension) is
*axiomatized*, and its combinatorial core is a placeholder: `growthFunction H n := 0`
returns `0` regardless of input, so no genuine statement about shattering is available.
Its third open question asks to

> Formalize the full equivalence (not just the placeholder `True`) — requires defining
> PAC learnability, ERM, and uniform convergence as proper Lean types.

This file supplies the missing combinatorial foundation with *proper* definitions and
genuinely proved (`0`-axiom) lemmas. A hypothesis class is a `Finset (Finset α)` (each
hypothesis is the set of points it labels positive). Its **trace** on a finite set `S`
is the family of restrictions `{h ∩ S : h ∈ H}` — the correct, non-placeholder growth
quantity — and `H` **shatters** `S` when the trace realises *every* subset of `S`.

## What is proved

* `trace_subset_powerset` — every restriction `h ∩ S` is a subset of `S`.
* `trace_card_le_pow` — the growth quantity is at most `2^|S|` (the correct bound the
  placeholder `growthFunction` could never express).
* `shatters_iff_card` — `H` shatters `S` iff its trace has the maximal size `2^|S|`.
* `shatters_card_le` — if `H` shatters `S` then `2^|S| ≤ |H|` (shattering a large set
  needs a large class).
* `shatters_card_le_log` — hence `|S| ≤ log₂ |H|`: the **VC-dimension–vs–size bound**, the
  finite half of the Sauer–Shelah circle of ideas.
* `shatters_mono` — shattering is monotone in the hypothesis class.

Fully machine-checked; `0` axioms beyond Mathlib's foundations; no `native_decide`.

Tags: pac-learning, vc-dimension, shattering, combinatorics, learning-theory
-/

namespace PACLearningBoundsWIP01

open Finset

variable {α : Type*} [DecidableEq α]

/-- The **trace** (restriction) of a hypothesis class `H` on a finite set `S`: the family
of intersections `h ∩ S` as `h` ranges over `H`. This is the genuine growth quantity
`Π_H(S)`, replacing the parent entry's placeholder `growthFunction := 0`. -/
def trace (H : Finset (Finset α)) (S : Finset α) : Finset (Finset α) :=
  H.image (· ∩ S)

/-- `H` **shatters** `S` when its trace realises every subset of `S`, i.e. the restriction
map `H → 2^S` is surjective. -/
def Shatters (H : Finset (Finset α)) (S : Finset α) : Prop :=
  trace H S = S.powerset

/-- Every restriction `h ∩ S` is a subset of `S`, so the trace lies inside the powerset. -/
theorem trace_subset_powerset (H : Finset (Finset α)) (S : Finset α) :
    trace H S ⊆ S.powerset := by
  intro T hT
  simp only [trace, Finset.mem_image] at hT
  obtain ⟨h, _, rfl⟩ := hT
  exact Finset.mem_powerset.mpr Finset.inter_subset_right

/-- **The growth bound.** The trace of `H` on `S` has at most `2^|S|` members — the correct
statement the parent's placeholder `growthFunction H n := 0` could not express. -/
theorem trace_card_le_pow (H : Finset (Finset α)) (S : Finset α) :
    (trace H S).card ≤ 2 ^ S.card :=
  calc (trace H S).card ≤ S.powerset.card := Finset.card_le_card (trace_subset_powerset H S)
    _ = 2 ^ S.card := Finset.card_powerset S

/-- **Shattering ⟺ maximal trace.** `H` shatters `S` exactly when its trace attains the
maximal possible size `2^|S|`. -/
theorem shatters_iff_card (H : Finset (Finset α)) (S : Finset α) :
    Shatters H S ↔ (trace H S).card = 2 ^ S.card := by
  rw [Shatters]
  constructor
  · intro h; rw [h, Finset.card_powerset]
  · intro h
    exact Finset.eq_of_subset_of_card_le (trace_subset_powerset H S)
      (by rw [Finset.card_powerset]; omega)

/-- **Shattering needs a large class.** If `H` shatters `S`, then `2^|S| ≤ |H|`: realising
all `2^|S|` subsets of `S` requires at least that many distinct hypotheses. -/
theorem shatters_card_le (H : Finset (Finset α)) (S : Finset α) (h : Shatters H S) :
    2 ^ S.card ≤ H.card := by
  rw [shatters_iff_card] at h
  calc 2 ^ S.card = (trace H S).card := h.symm
    _ ≤ H.card := Finset.card_image_le

/-- **The VC-dimension–vs–size bound.** Any set shattered by `H` has size at most
`log₂ |H|`. In particular the VC dimension of a finite class `H` is at most `log₂ |H|` —
the finite, elementary half of the Sauer–Shelah circle of results. -/
theorem shatters_card_le_log (H : Finset (Finset α)) (S : Finset α) (h : Shatters H S) :
    S.card ≤ Nat.log 2 H.card := by
  have hle : 2 ^ S.card ≤ H.card := shatters_card_le H S h
  have hpos : H.card ≠ 0 := by
    have := Nat.one_le_pow S.card 2 (by norm_num)
    omega
  exact (Nat.le_log_iff_pow_le (by norm_num) hpos).mpr hle

/-- **Monotonicity.** Enlarging the hypothesis class preserves shattering: if `H ⊆ H'` and
`H` shatters `S`, then `H'` shatters `S`. -/
theorem shatters_mono {H H' : Finset (Finset α)} (S : Finset α) (hHH : H ⊆ H')
    (h : Shatters H S) : Shatters H' S := by
  refine Finset.eq_of_subset_of_card_le (trace_subset_powerset H' S) ?_
  rw [Finset.card_powerset]
  have h1 : trace H S ⊆ trace H' S := Finset.image_subset_image hHH
  rw [shatters_iff_card] at h
  calc 2 ^ S.card = (trace H S).card := h.symm
    _ ≤ (trace H' S).card := Finset.card_le_card h1

end PACLearningBoundsWIP01
