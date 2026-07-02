/-
  Stationary Reflection — the ZFC base layer
  (`Proofs/Reflection/Basic.lean`, answering the tractable fragment of
  `fodor-pressing-down-oq-03`)

  The open question asks whether the club/stationary substrate of
  `Proofs/Club/Basic.lean` extends to reflection phenomena and the □-principle.
  The honest answer is **partial**, and this file proves the part that is a
  genuine ZFC theorem, 0-axiom and 0-sorry:

  ## What IS provable here (this file)

  * **Clubs reflect (base case).** `clubReflects` : if `C` is a club below `o`
    and `α ≤ o` is an *accumulation point* of `C`, then `C ∩ Iio α` is a club
    below `α`. This is the precise formal content of "a club reflects at its
    accumulation points": the reflected object is again closed and unbounded.
  * **The reflection points of a club.** `Trace C o = {α < o | α.IsAcc C}` is
    the set of ordinals below `o` at which `C` accumulates; `clubReflects`
    says `C` reflects (to a club) at every point of `Trace C o`
    (`reflects_of_mem_trace`), and every such point already lies in `C`
    (`trace_subset`, since a club contains its accumulation points).
  * Monotonicity and nonemptiness bookkeeping (`Trace_mono`,
    `reflected_nonempty`).

  ## What is deliberately NOT claimed (and why)

  * **"The trace of a club is itself a club" is FALSE for `cf(o) = ω`.** For
    example `C = Iio ω` is a club below `ω` (`isClubBelow_Iio_of_isSuccLimit`),
    yet its accumulation points below `ω` are the *limit* ordinals `< ω`, of
    which there are none: `Trace (Iio ω) ω = ∅`, which is not unbounded below
    `ω`. The statement becomes true only under `cf(o) > ω` (it is the source of
    the ω₁-vs-ω₂ distinction in reflection theory), so we do not prove the
    unconditional version; only the always-true base case `clubReflects` is
    shipped.
  * **Full stationary reflection is independent of ZFC** (it can fail, e.g.
    under □), so it must never be recorded as a verified theorem.
  * The □-principle itself needs an order-type/coherence module beyond the
    current `Set Ordinal` club idiom; "□ ⇒ a non-reflecting stationary set" is
    reachable only in hypothesis-taking form. Both are out of scope here.

  Everything below reuses `Proofs.Club.Basic` unchanged and is verified
  axiom-free (`#print axioms` reports only propext / Classical.choice /
  Quot.sound).
-/

import Proofs.Club.Basic

namespace Ordinal

open Set Order

variable {C D : Set Ordinal} {o α : Ordinal}

/-- `C` **reflects at** `α` when the initial segment `C ∩ Iio α` is a club
below `α`: the club structure of `C` is "seen" locally at `α`. -/
def Reflects (C : Set Ordinal) (α : Ordinal) : Prop :=
  IsClubBelow (C ∩ Iio α) α

/-- The **trace** of `C` below `o`: the ordinals `α < o` at which `C`
accumulates. These are exactly the candidate reflection points. -/
def Trace (C : Set Ordinal) (o : Ordinal) : Set Ordinal :=
  {α | α < o ∧ α.IsAcc C}

@[simp]
theorem mem_Trace : α ∈ Trace C o ↔ α < o ∧ α.IsAcc C := Iff.rfl

theorem Trace_subset_Iio (C : Set Ordinal) (o : Ordinal) : Trace C o ⊆ Iio o :=
  fun _ h => h.1

/-- **Clubs reflect at their accumulation points (base case of stationary
reflection).** If `C` is a club below `o` and `α ≤ o` is an accumulation
point of `C`, then `C ∩ Iio α` is a club below `α`.

Both club fields transfer locally: closedness of `C` below `o` already checks
accumulation points below `α ≤ o`, and unboundedness of `C ∩ Iio α` below `α`
is *exactly* the assumption that `α` is an accumulation point of `C`. No
cofinality hypothesis is needed — this is the unconditional, ZFC-true core. -/
theorem clubReflects (hC : IsClubBelow C o) (hαo : α ≤ o) (hα : α.IsAcc C) :
    Reflects C α where
  subset_Iio := inter_subset_right
  closed := by
    rw [isClosedBelow_iff]
    intro p hp hpAcc
    -- an accumulation point of `C ∩ Iio α` below `α` is one of `C` below `o`,
    -- hence lies in `C` by closedness of `C`; and it is `< α` by hypothesis.
    have hpC : p.IsAcc C := hpAcc.mono inter_subset_left
    have hpo : p < o := lt_of_lt_of_le hp hαo
    exact ⟨hC.closed.forall_lt p hpo hpC, hp⟩
  unbounded := by
    intro p hp
    -- unboundedness of the reflected set below `α` is `α.IsAcc C` unpacked.
    obtain ⟨δ, hδC, hδp, hδα⟩ := hα.forall_lt p hp
    exact ⟨δ, ⟨hδC, hδα⟩, hδp, hδα⟩

/-- A club below `o` contains its whole trace: every accumulation point of `C`
below `o` already lies in `C` (closedness). -/
theorem trace_subset (hC : IsClubBelow C o) : Trace C o ⊆ C :=
  fun _ hα => hC.mem_of_isAcc hα.1 hα.2

/-- `C` reflects at every point of its trace. -/
theorem reflects_of_mem_trace (hC : IsClubBelow C o) (hα : α ∈ Trace C o) :
    Reflects C α :=
  clubReflects hC (le_of_lt hα.1) hα.2

/-- The trace is monotone in the set: accumulation points only grow as the set
grows. -/
theorem Trace_mono (h : C ⊆ D) : Trace C o ⊆ Trace D o :=
  fun _ hα => ⟨hα.1, hα.2.mono h⟩

/-- Where `C` reflects, the reflected club is nonempty (a club below a positive
ordinal is nonempty). -/
theorem reflected_nonempty (h : Reflects C α) (hα : 0 < α) :
    (C ∩ Iio α).Nonempty :=
  h.nonempty hα

-- Axiom-free: only the standard foundational axioms (propext, Classical.choice,
-- Quot.sound) — no native_decide, no sorryAx.
#print axioms clubReflects
#print axioms trace_subset
#print axioms reflects_of_mem_trace

end Ordinal
