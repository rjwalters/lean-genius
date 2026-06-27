/-
# The Halting Problem in the Arithmetical Hierarchy: where the approximation gap lives

## What This Proves
The companion file `Proofs.HaltingApproximation` proves a *schematic* barrier for
partial approximators `A : ℕ → ℕ → Option Bool`: every **sound** approximator
(one that is correct wherever it commits) must **decline** (answer `none`) at its
own diagonal point. That theorem is honest but coarse — it locates a *single*
forced gap and uses no model of computation, so it cannot say how *large* the
decline set is, nor where the halting problem sits in the arithmetical hierarchy.

This file supplies the genuine computational-complexity reading (gallery open
question **OQ-01c**) using Mathlib's computability library
(`Nat.Partrec.Code`, `REPred`, `ComputablePred`). Fix an input `n` and let

  `Halts n c  :=  (eval c n).Dom`            -- code `c` halts on input `n`

be the parametrized halting set `K`. The results:

* **Hierarchy placement.** `K` is recursively enumerable (`halts_re`, i.e. `Σ⁰₁`)
  but *not* computable (`halts_not_computable`), and its complement is *not*
  recursively enumerable (`halts_compl_not_re`). So `K` is **properly `Σ⁰₁`**:
  the approximation gap lives exactly in `Π⁰₁ ∖ Σ⁰₁`. (These three repackage the
  Mathlib theorems `ComputablePred.halting_problem_re / halting_problem /
  halting_problem_not_re` under the gallery's framing.)

* **The decline set is genuinely large — not a single point.** Model a *computable*
  approximator as a **partial computable** function `f : Code →. Bool`
  (`none`/undefined = decline). We prove:
  - `re_confirmedFalse` — for any partial computable `f`, the set of codes on which
    `f` *confirms non-halting* (commits `false`) is recursively enumerable.
  - `no_sound_approx_confirms_all_nonhalting` — **no** sound computable approximator
    can confirm non-halting on *all* of `Kᶜ`; if it did, `Kᶜ` would be r.e.,
    contradicting `halts_compl_not_re`.
  - `sound_approx_undefined_on_nonhalting` — consequently every sound computable
    approximator **declines** (is undefined) on some genuinely non-halting input.
    This is the real-model analog of the schematic
    `HaltingApproximation.sound_approx_declines_on_diagonal`, and it is *not*
    confined to a diagonal point: the obstruction is the asymmetry "`K` is r.e.,
    `Kᶜ` is not", i.e. halting is *semi-decidable* (you can confirm halting, since
    `K` is r.e.) but non-halting is *not* (no computable process confirms looping
    on every looping input).
  - `decline_set_on_nonhalting_not_re` — the sharp form: the decline set
    *restricted to the non-halting inputs* is **itself not recursively
    enumerable** (hence infinite), not merely nonempty. Since at a non-halting
    code a sound approximator either declines or commits `false`,
    `Kᶜ = {confirmed false} ∪ {non-halting ∧ declines}`; the first piece is r.e.,
    so were the second r.e. the union `Kᶜ` would be r.e. (`REPred.or`),
    contradicting `halts_compl_not_re`. The earlier nonempty statement is
    recovered as the corollary `sound_approx_declines_nonempty`.

## Approach
- **Foundation (from Mathlib):** `Mathlib.Computability.Halting` — the universal
  partial recursive function, `Nat.Partrec.Code.eval`, `REPred`, `ComputablePred`,
  and the three halting-problem theorems. Unlike the zero-import schematic file,
  this file *needs* a real model of computation, which is the whole point of
  OQ-01c.
- **Original Contributions:** The bridge from the schematic `Option Bool`
  approximator to the partial-computable `Code →. Bool` approximator, the lemma
  that the confirmed-non-halting set is r.e., closure of `REPred` under union
  (`REPred.or`, via Mathlib's `Partrec.merge'` dovetailing), and the strengthening
  of "declines at the diagonal point" to "the decline set on `Kᶜ` is non-r.e.
  (hence infinite)" via the `Σ⁰₁`/`Π⁰₁` asymmetry.
- **Proof Techniques Demonstrated:** recursive enumerability as "domain of a
  partial computable function" (`Partrec.dom_re`), closure of `Partrec` under
  `bind`/`cond`, and reduction (`REPred.of_eq`) to Mathlib's halting theorems.

## Honesty Note
The three hierarchy-placement theorems are thin wrappers over Mathlib results; the
genuine new mathematical content is the approximator bridge (`re_confirmedFalse`,
`no_sound_approx_confirms_all_nonhalting`, `sound_approx_undefined_on_nonhalting`),
the union closure `REPred.or`, and its consequence `decline_set_on_nonhalting_not_re`,
which turns the schematic single-point gap into the precise statement that the gap
is the non-r.e. set `Kᶜ`. We do *not* prove a density/measure ("generic-case
complexity") statement — that is OQ-01b and is encoding-sensitive (see `knowledge.md`).
-/

import Mathlib.Computability.Halting

namespace HaltingArithmeticalHierarchy

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)

/-! ## The parametrized halting set `K` -/

/-- The **halting predicate** at a fixed input `n`: code `c` halts on input `n`. -/
def Halts (n : ℕ) (c : Code) : Prop := (eval c n).Dom

/-! ### Arithmetical-hierarchy placement (repackaged from Mathlib)

`K` is `Σ⁰₁` (r.e.) but neither computable (`Δ⁰₁`) nor co-r.e. (`Π⁰₁`); the
approximation gap is therefore exactly `Kᶜ ∈ Π⁰₁ ∖ Σ⁰₁`. -/

/-- `K` is **recursively enumerable** (semi-decidable / `Σ⁰₁`): one can confirm
halting. -/
theorem halts_re (n : ℕ) : REPred (Halts n) :=
  ComputablePred.halting_problem_re n

/-- `K` is **not computable**: there is no total decider for halting. -/
theorem halts_not_computable (n : ℕ) : ¬ ComputablePred (Halts n) :=
  ComputablePred.halting_problem n

/-- The complement of `K` is **not** recursively enumerable: non-halting is *not*
semi-decidable. This is the asymmetry that forces every sound approximator's gap. -/
theorem halts_compl_not_re (n : ℕ) : ¬ REPred (fun c => ¬ Halts n c) :=
  ComputablePred.halting_problem_not_re n

/-! ## Recursive enumerability is closed under union

The strengthening below (the decline set is *not* r.e., not merely nonempty)
needs that `REPred` is closed under `∨`. Mathlib packages the dovetailing
("run both in parallel, accept if either accepts") as `Partrec.merge'`, whose
merged function halts iff *either* input halts — exactly the union of domains. -/

/-- **`REPred` is closed under union.** If `p` and `q` are both recursively
enumerable, so is `fun a => p a ∨ q a`: dovetail the two semi-deciders via
`Partrec.merge'` and read off the domain, which is the union of the two domains. -/
theorem REPred.or {α} [Primcodable α] {p q : α → Prop}
    (hp : REPred p) (hq : REPred q) : REPred (fun a => p a ∨ q a) := by
  -- `(Part.assert (r a) fun _ => some ()).Dom ↔ r a`: the domain of a semi-decider
  -- for `r` is exactly `{a | r a}`.
  have key : ∀ (r : α → Prop) (a : α),
      (Part.assert (r a) fun _ => Part.some ()).Dom ↔ r a := fun r a => by
    simp [Part.dom_iff_mem, Part.mem_assert_iff]
  obtain ⟨k, hk, H⟩ := Partrec.merge' hp hq
  -- `k` is partrec with `(k a).Dom ↔ p a ∨ q a`, so its domain predicate is `p ∨ q`.
  refine hk.dom_re.of_eq fun a => ?_
  rw [(H a).2, key p a, key q a]

/-! ## Computable approximators and the decline set -/

/-- `f` is a **sound** approximator for halting at `n`: every value it *commits*
(`b ∈ f c`) is correct. Where `f c` is undefined, `f` **declines**. We do not
require `f` total or even computable in this predicate — computability is supplied
separately as `Partrec f`. -/
def Sound (n : ℕ) (f : Code →. Bool) : Prop :=
  ∀ c b, b ∈ f c → (b = true ↔ Halts n c)

/-- Soundness, specialized: confirming non-halting (`false ∈ f c`) is correct. -/
theorem Sound.not_halts {n : ℕ} {f : Code →. Bool} (hs : Sound n f) {c : Code}
    (h : false ∈ f c) : ¬ Halts n c := by
  have := (hs c false h)
  simpa using this

/-- **The confirmed-non-halting set of a partial computable approximator is r.e.**

For partial computable `f`, the set `{c | false ∈ f c}` of codes on which `f`
commits `false` is the domain of the partial computable function
`c ↦ (f c) >>= (fun b => bif b then none else some ())`, hence recursively
enumerable. -/
theorem re_confirmedFalse {f : Code →. Bool} (hf : Partrec f) :
    REPred (fun c => false ∈ f c) := by
  -- The witnessing partial computable function.
  have hg : Partrec (fun c => (f c).bind
      (fun b => cond b Part.none (Part.some ()))) :=
    hf.bind (Partrec.cond Computable.snd Partrec.none (Partrec.const' (Part.some ())))
  refine (hg.dom_re).of_eq (fun c => ?_)
  -- Its domain is exactly `{c | false ∈ f c}`.
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨x, hx⟩
    rw [Part.mem_bind_iff] at hx
    obtain ⟨b, hb, hxb⟩ := hx
    cases b with
    | true  => simp at hxb
    | false => exact hb
  · intro hb
    exact ⟨(), Part.mem_bind_iff.2 ⟨false, hb, by simp⟩⟩

/-- **No sound computable approximator confirms non-halting on all of `Kᶜ`.**

If a sound partial computable `f` committed `false` on *every* non-halting code,
then `{c | false ∈ f c}` would equal `Kᶜ`; the former is r.e. (`re_confirmedFalse`)
but the latter is not (`halts_compl_not_re`) — contradiction. So halting is
semi-decidable while non-halting is not: the approximation gap cannot be closed. -/
theorem no_sound_approx_confirms_all_nonhalting {n : ℕ} {f : Code →. Bool}
    (hf : Partrec f) (hs : Sound n f) :
    ¬ ∀ c, ¬ Halts n c → false ∈ f c := by
  intro hall
  have hre : REPred (fun c => ¬ Halts n c) :=
    (re_confirmedFalse hf).of_eq fun c =>
      ⟨fun h => hs.not_halts h, fun h => hall c h⟩
  exact halts_compl_not_re n hre

/-- **Every sound computable approximator declines on some genuinely non-halting
input.**  The real-model analog of the schematic
`HaltingApproximation.sound_approx_declines_on_diagonal`: there is a code `c` with
`¬ Halts n c` on which `f` is *undefined* (declines). Such `c` cannot be confirmed
`false` (else `Kᶜ` would be r.e.) and cannot be committed `true` (soundness forbids
a wrong commit), so `f c` has no value at all. -/
theorem sound_approx_undefined_on_nonhalting {n : ℕ} {f : Code →. Bool}
    (hf : Partrec f) (hs : Sound n f) :
    ∃ c, ¬ Halts n c ∧ ¬ (f c).Dom := by
  -- Some non-halting `c` is not confirmed `false`.
  obtain ⟨c, hc, hcf⟩ : ∃ c, ¬ Halts n c ∧ false ∉ f c := by
    by_contra h
    push_neg at h
    exact no_sound_approx_confirms_all_nonhalting hf hs h
  refine ⟨c, hc, ?_⟩
  -- At such `c`, `f` cannot commit any value, so it declines.
  rintro hdom
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.1 hdom
  cases b with
  | true  => exact hc ((hs c true hb).1 rfl)
  | false => exact hcf hb

/-- **The decline set on the non-halting inputs is itself not recursively
enumerable** — the decline obstruction is not a single point (Session 1's
schematic diagonal), nor merely nonempty (`sound_approx_undefined_on_nonhalting`),
but a genuinely non-r.e. (hence infinite) set.

*Proof.* At a non-halting code a sound approximator either declines or commits
`false` (soundness forbids committing `true`), so the non-halting set splits as
`Kᶜ = {confirmed false} ∪ {non-halting ∧ declines}`. The first piece is r.e.
(`re_confirmedFalse`). If the second piece were r.e. too, then `Kᶜ` — a union of
two r.e. sets (`REPred.or`) — would be r.e., contradicting `halts_compl_not_re`.
So the decline-on-non-halting set is not r.e. -/
theorem decline_set_on_nonhalting_not_re {n : ℕ} {f : Code →. Bool}
    (hf : Partrec f) (hs : Sound n f) :
    ¬ REPred (fun c => ¬ Halts n c ∧ ¬ (f c).Dom) := by
  intro hdn
  -- The two r.e. pieces cover exactly `Kᶜ`.
  have hre : REPred (fun c => ¬ Halts n c) := by
    refine (REPred.or (re_confirmedFalse hf) hdn).of_eq fun c => ?_
    constructor
    · rintro (hbf | ⟨hnh, _⟩)
      · exact hs.not_halts hbf
      · exact hnh
    · intro hnh
      by_cases hdom : (f c).Dom
      · -- `f` commits at `c`; soundness forces the committed value to be `false`.
        obtain ⟨b, hb⟩ := Part.dom_iff_mem.1 hdom
        cases b with
        | true  => exact absurd ((hs c true hb).1 rfl) hnh
        | false => exact Or.inl hb
      · exact Or.inr ⟨hnh, hdom⟩
  exact halts_compl_not_re n hre

/-- The earlier single-witness statement `sound_approx_undefined_on_nonhalting`
is now a corollary: the empty predicate is r.e., so a *non*-r.e. set is nonempty.
This records that `decline_set_on_nonhalting_not_re` strictly strengthens it. -/
theorem sound_approx_declines_nonempty {n : ℕ} {f : Code →. Bool}
    (hf : Partrec f) (hs : Sound n f) :
    ∃ c, ¬ Halts n c ∧ ¬ (f c).Dom := by
  by_contra hcon
  rw [not_exists] at hcon
  -- The empty predicate is r.e.; if the decline set were empty it would be r.e. too.
  have emptyRe : REPred (fun _ : Code => False) :=
    (Partrec.none : Partrec (fun _ : Code => (Part.none : Part Unit))).dom_re.of_eq
      fun _ => by simp [Part.dom_iff_mem]
  exact decline_set_on_nonhalting_not_re hf hs
    (emptyRe.of_eq fun c => iff_of_false not_false (hcon c))

end HaltingArithmeticalHierarchy
