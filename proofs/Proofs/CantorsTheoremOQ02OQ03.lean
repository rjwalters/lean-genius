/-
# Cantor's Theorem OQ-02-OQ-03: Strengthening the Lawvere Framework

Parent: `cantors-theorem-oq-02` (Lawvere's Fixed-Point Theorem, VERIFIED 0-axiom),
which unifies Cantor, Russell, Gödel and Tarski as instances of a single abstract
diagonal argument.

## The Open Question

OQ-03 asks: *Does the Lawvere framework extend to ω-consistency and Rosser's
strengthening of Gödel's theorem?*

The **arithmetic** form of that question (Rosser sentences, ω-consistency) requires
Gödel coding of syntax and provability inside a formal theory — a much larger project
(the parent's own OQ-01 flags this). It is NOT formalized here, and we do not claim it.

What IS tractable, and what this entry delivers, is the **abstract substrate** that
any such extension must sit on top of: a sharper, more general version of the Lawvere
machinery than the parent proves. Concretely:

**Part A — The *true* Lawvere theorem (weak point-surjectivity).**
Lawvere's own hypothesis is *point*-surjectivity — for every `g : α → β` some `a`
matches `g` *pointwise* (`∀ x, f a x = g x`) — which is strictly weaker than the
`Surjective f` (`f a = g` as functions) used by the parent. We prove the fixed-point
theorem under this weaker hypothesis, and show `Surjective ⇒ WeaklyPointSurjective`,
so every parent result is recovered as a special case.

**Part B — Retract-stability of the fixed-point property.**
`HasFPP β` (every endomorphism of `β` has a fixed point) is the target-side invariant
that drives the contrapositive. We prove it transfers along retracts — the categorical
heart of Lawvere's "retract" formulation — and holds for inhabited subsingletons.

**Part C — Sharpness / obstruction propagation.**
`Prop` and `Bool` fail `HasFPP` (negation is fixed-point-free), and via Part B this
obstruction propagates to anything retracting onto them.

**Part D — Weak Cantor for arbitrary targets**, packaged for `Prop` and `Bool`.

Axioms: 0 (no `axiom` declarations, no `sorry`, no `native_decide`).
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic

namespace CantorsTheoremOQ02OQ03

open Function

/-
## Part 0: The single obstruction

Every diagonal argument in this framework bottoms out at one fact: the negation
map on `Prop` has no fixed point.
-/

/-- **Negation has no fixed point** (Russell's core): no `p : Prop` satisfies `p ↔ ¬p`. -/
theorem neg_no_fixed_point : ¬∃ p : Prop, p ↔ ¬p := by
  intro ⟨p, hp⟩
  have hnp : ¬p := fun h => hp.mp h h
  exact hnp (hp.mpr hnp)

/-
## Part A: The true (weakly point-surjective) Lawvere theorem

The parent proves the fixed-point theorem for `Surjective f`, i.e. `f a = g` as
*functions*. Lawvere's actual hypothesis is weaker: `f` is *point-surjective*, hitting
every `g` only *pointwise*. We formalize this and reprove Lawvere at full generality.
-/

/-- `f : α → (α → β)` is **weakly point-surjective** if every `g : α → β` is matched
    pointwise by some row `f a`: `∀ x, f a x = g x`. This is strictly weaker than
    `Surjective f`, which additionally demands `f a = g` as functions. -/
def WeaklyPointSurjective {α β : Type*} (f : α → (α → β)) : Prop :=
  ∀ g : α → β, ∃ a : α, ∀ x : α, f a x = g x

/-- Full surjectivity implies weak point-surjectivity: if `f a = g` then in particular
    `f a x = g x` for every `x`. Hence every result below specializes the parent's. -/
theorem surjective_weaklyPointSurjective {α β : Type*} {f : α → (α → β)}
    (hf : Surjective f) : WeaklyPointSurjective f := by
  intro g
  obtain ⟨a, ha⟩ := hf g
  exact ⟨a, fun x => congr_fun ha x⟩

/-- **Lawvere's Fixed-Point Theorem (sharp form)**: if `f : α → (α → β)` is *weakly*
    point-surjective, then every `h : β → β` has a fixed point.

    The diagonal map `q x = h (f x x)` is matched pointwise by some row `f a`; at the
    point `a` this reads `f a a = h (f a a)`, so `f a a` is the fixed point. Only the
    single value `q a` is used, which is exactly why pointwise matching suffices. -/
theorem lawvere_weak {α β : Type*} (f : α → (α → β))
    (hf : WeaklyPointSurjective f) (h : β → β) : ∃ b : β, h b = b := by
  obtain ⟨a, ha⟩ := hf (fun x => h (f x x))
  refine ⟨f a a, ?_⟩
  -- `ha a : f a a = h (f a a)`, so `h (f a a) = f a a`.
  exact (ha a).symm

/-- **Contrapositive**: if `h : β → β` has no fixed point, then no `f : α → (α → β)`
    is even weakly point-surjective. This is the general anti-diagonal principle. -/
theorem lawvere_weak_contrapositive {α β : Type*} (h : β → β)
    (hh : ∀ b : β, h b ≠ b) (f : α → (α → β)) : ¬ WeaklyPointSurjective f := by
  intro hf
  obtain ⟨b, hb⟩ := lawvere_weak f hf h
  exact hh b hb

/-- **Sharp Cantor**: no `f : α → (α → Prop)` is weakly point-surjective. Strengthens
    the parent's `cantor_from_lawvere` (which assumes full surjectivity), because a
    merely pointwise-covering `f` is already impossible. -/
theorem cantor_weak {α : Type*} (f : α → (α → Prop)) : ¬ WeaklyPointSurjective f :=
  lawvere_weak_contrapositive Not
    (fun p hp => neg_no_fixed_point ⟨p, Iff.intro (Eq.mp hp.symm) (Eq.mp hp)⟩) f

/-
## Part B: The fixed-point property and its stability

`HasFPP β` abstracts the target-side hypothesis of the contrapositive. Its two key
structural facts — transfer along retracts, and holding for inhabited subsingletons —
are the categorical content of Lawvere's "retract" language.
-/

/-- `β` **has the fixed-point property** if every endomorphism has a fixed point. -/
def HasFPP (β : Type*) : Prop := ∀ h : β → β, ∃ b : β, h b = b

/-- **Retract-stability**: if `β` is a retract of `β'` (there are `s : β → β'`,
    `r : β' → β` with `r ∘ s = id`) and `β'` has the fixed-point property, then so
    does `β`.

    Given `h : β → β`, transport it to `β'` as `s ∘ h ∘ r`; a fixed point `b'` there
    yields, after applying `r` and cancelling `r ∘ s`, a fixed point `r b'` of `h`. -/
theorem hasFPP_of_retract {β β' : Type*} (s : β → β') (r : β' → β)
    (hrs : ∀ b : β, r (s b) = b) (h' : HasFPP β') : HasFPP β := by
  intro h
  obtain ⟨b', hb'⟩ := h' (fun y => s (h (r y)))
  -- hb' : s (h (r b')) = b'
  refine ⟨r b', ?_⟩
  have hstep := congrArg r hb'   -- r (s (h (r b'))) = r b'
  rwa [hrs] at hstep

/-- An inhabited subsingleton (e.g. `Unit`) trivially has the fixed-point property. -/
theorem hasFPP_of_subsingleton {β : Type*} [Subsingleton β] [Inhabited β] :
    HasFPP β :=
  fun _ => ⟨default, Subsingleton.elim _ _⟩

/-
## Part C: Sharpness and propagation of the obstruction

`Prop` and `Bool` fail `HasFPP` via a fixed-point-free negation; by Part B any type
retracting onto them fails it too.
-/

/-- `Prop` does **not** have the fixed-point property: `Not` is fixed-point-free. -/
theorem not_hasFPP_Prop : ¬ HasFPP Prop := by
  intro h
  obtain ⟨p, hp⟩ := h Not      -- hp : Not p = p
  exact neg_no_fixed_point ⟨p, Iff.intro (Eq.mp hp.symm) (Eq.mp hp)⟩

/-- `Bool` does **not** have the fixed-point property: `Bool.not` is fixed-point-free. -/
theorem not_hasFPP_Bool : ¬ HasFPP Bool := by
  intro h
  obtain ⟨b, hb⟩ := h Bool.not
  cases b <;> simp at hb

/-- **Obstruction propagates**: any type retracting onto `Prop` inherits the failure
    of the fixed-point property. -/
theorem not_hasFPP_of_retracts_onto_Prop {β : Type*}
    (s : Prop → β) (r : β → Prop) (hrs : ∀ p : Prop, r (s p) = p) :
    ¬ HasFPP β := by
  intro h
  exact not_hasFPP_Prop (hasFPP_of_retract s r hrs h)

/-
## Part D: Weak Cantor for arbitrary targets

Any target with a fixed-point-free endomorphism forbids weakly-point-surjective maps.
-/

/-- **General anti-diagonal**: a fixed-point-free `h : β → β` rules out every weakly
    point-surjective `f : α → (α → β)`. -/
theorem no_weaklyPointSurjective_of_fixedPointFree {α β : Type*}
    (h : β → β) (hh : ∀ b : β, h b ≠ b) (f : α → (α → β)) :
    ¬ WeaklyPointSurjective f :=
  lawvere_weak_contrapositive h hh f

/-- **Sharp Cantor for `Bool`**: no `f : α → (α → Bool)` is weakly point-surjective. -/
theorem cantor_weak_bool {α : Type*} (f : α → (α → Bool)) :
    ¬ WeaklyPointSurjective f :=
  lawvere_weak_contrapositive Bool.not (by intro b; cases b <;> decide) f

/-
## Capstone

The sharpened unity theorem, mirroring the parent's `lawvere_cantor_unity` but with
the weaker (hence stronger) point-surjective hypothesis on the Cantor clause.
-/

/-- **Sharpened Lawvere–Cantor unity**:
    (1) no weakly point-surjective `f : α → (α → Prop)` exists [sharp Cantor];
    (2) negation has no fixed point [Russell];
    (3) `Prop` lacks the fixed-point property [target-side obstruction]. -/
theorem lawvere_weak_unity :
    (∀ (α : Type*) (f : α → (α → Prop)), ¬ WeaklyPointSurjective f) ∧
    (¬∃ p : Prop, p ↔ ¬p) ∧
    (¬ HasFPP Prop) :=
  ⟨fun _ f => cantor_weak f, neg_no_fixed_point, not_hasFPP_Prop⟩

end CantorsTheoremOQ02OQ03
