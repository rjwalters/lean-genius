/-
  Large Cardinal Axioms and Arithmetic Independence  (godel-incompleteness-oq-04)

  ## The Open Question

  Gödel's incompleteness theorems show that no consistent, effectively axiomatized
  theory extending arithmetic proves its own consistency.  The *large cardinal*
  hierarchy is the canonical engine that climbs the resulting tower of consistency
  strengths: the existence of an inaccessible cardinal `κ` proves `Con(ZFC)` (and
  much more), and is therefore — by Gödel's second theorem — *independent* of ZFC.

  The mechanism is **Zermelo's theorem**: if `κ` is (strongly) inaccessible then the
  rank-initial segment `V_κ` is a model of ZFC.  All that "`V_κ ⊨ ZFC`" really asks
  of `κ` is a package of *cardinal-arithmetic closure* properties — the universe
  below `κ` must be closed under the set-builders of ZFC (pairing, union, powerset,
  replacement).  At the level of cardinals these become:

    * powerset            ↦  `a < κ  →  2^a < κ`            (strong limit)
    * replacement/union   ↦  sup of `<κ`-many `<κ` cardinals stays `<κ` (regular)

  This file isolates and fully verifies that arithmetic core.  It is the honest,
  formalizable shadow of the independence statement: not the metamathematics of
  unprovability (see "What this does NOT do"), but the exact cardinal-closure facts
  that make an inaccessible a model of ZFC and hence a source of true-but-unprovable
  arithmetic (`Con(ZFC)`).

  ## What This File Proves (all 0 axioms, 0 sorries, self-contained)

  Throughout, `c : Cardinal` is strongly inaccessible (`c.IsInaccessible`).

  ### Part I — the V_c closure package (Zermelo's theorem, arithmetic core)
  * `inaccessible_add_lt`, `inaccessible_mul_lt` : closure under `+`, `*`.  These hold
    for *any* infinite cardinal, so they are not what distinguishes inaccessibles —
    recorded for completeness.
  * `inaccessible_two_power_lt` : **powerset closure** `a < c → 2^a < c` (strong limit).
  * `inaccessible_power_lt` : full exponentiation closure `a^b < c`, derived from
    powerset closure via `a^b ≤ (2^a)^b = 2^(a·b)`.
  * `inaccessible_iSup_lt` : **replacement/union closure** — the supremum of a family
    of `<c` cardinals indexed by a type of size `<c` is again `<c` (regularity).  This
    is the genuinely large-cardinal-specific property.
  * `inaccessible_zermelo_closure` : the two ZFC-critical closures (powerset +
    replacement) bundled as the arithmetic statement of `V_c ⊨ ZFC`.

  ### Part II — structural identity of inaccessibles
  * `inaccessible_isSuccLimit` : `c` is a limit cardinal (never a successor).
  * `inaccessible_cof_eq` : `c` is regular, `cof c = c`.
  * `inaccessible_iff` : the closure data *characterizes* inaccessibility —
    uncountable ∧ regular ∧ strong-limit ⟺ inaccessible.

  ### Part III — non-vacuity and the universe shadow of independence
  * `univ_inaccessible` : a genuine inaccessible exists *one universe up* — the
    cardinality of `Type u`, read inside `Type (u+1)`, is inaccessible.  ZFC is a
    single universe and cannot prove an inaccessible internally; universe
    polymorphism supplies one "from outside", exactly mirroring how the independence
    arises.
  * `univ_powerset_closed`, `univ_iSup_closed` : the closure lemmas instantiated at
    `univ`, witnessing that the hypotheses are satisfiable, not vacuous.

  ## What this does NOT do (honesty note)

  This file does **not** formalize the metamathematics: it does not arithmetize
  provability, does not build the model-existence argument `V_κ ⊨ ZFC` inside Lean's
  logic, and does not prove the independence statement "`Con(ZFC)` is unprovable in
  ZFC".  Those require a formalized object theory and a satisfaction predicate that
  are out of Mathlib's current reach.  What is captured is the *cardinal-arithmetic
  content* on which Zermelo's theorem rests — true, self-contained, and machine-checked.

  ## Relationship to the parent

  The parent `GodelIncompleteness` builds the first incompleteness phenomenon
  syntactically; `OQ-02` recasts it recursion-theoretically.  This `OQ-04` looks one
  level up the consistency-strength tower: it formalizes the cardinal closure that
  makes a large cardinal a *model* of the theory, the structural reason large
  cardinals decide statements (like `Con(ZFC)`) that the base theory leaves open.
-/

import Mathlib.Tactic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Order.SuccPred.Limit

namespace GodelIncompletenessOQ04

open Cardinal

variable {c a b : Cardinal.{u}}

/-! ## Part I — the `V_c` closure package (arithmetic core of Zermelo's theorem) -/

/-- An inaccessible cardinal is uncountable. -/
theorem inaccessible_aleph0_lt (hc : c.IsInaccessible) : ℵ₀ < c :=
  hc.aleph0_lt

/-- Closure under addition.  (True for *any* infinite cardinal — not special to
inaccessibles, recorded so the `V_c`-closure picture is complete.) -/
theorem inaccessible_add_lt (hc : c.IsInaccessible) (ha : a < c) (hb : b < c) :
    a + b < c :=
  add_lt_of_lt hc.aleph0_lt.le ha hb

/-- Closure under multiplication.  (Also true for any infinite cardinal.) -/
theorem inaccessible_mul_lt (hc : c.IsInaccessible) (ha : a < c) (hb : b < c) :
    a * b < c :=
  mul_lt_of_lt hc.aleph0_lt.le ha hb

/-- **Powerset closure** (strong limit): `2^a < c` whenever `a < c`.  This is the
cardinal shadow of "`V_c` is closed under powersets". -/
theorem inaccessible_two_power_lt (hc : c.IsInaccessible) (ha : a < c) :
    2 ^ a < c :=
  hc.isStrongLimit.two_power_lt ha

/-- **Full exponentiation closure**: `a^b < c` whenever `a, b < c`.  Derived from
powerset closure and `a^b ≤ (2^a)^b = 2^(a·b)`, so it needs no extra hypothesis
beyond strong-limit + the (automatic) closure of `·` below an infinite cardinal. -/
theorem inaccessible_power_lt (hc : c.IsInaccessible) (ha : a < c) (hb : b < c) :
    a ^ b < c := by
  calc
    a ^ b ≤ (2 ^ a) ^ b := power_le_power_right (cantor a).le
    _ = 2 ^ (a * b) := by rw [← power_mul]
    _ < c := hc.isStrongLimit.two_power_lt (inaccessible_mul_lt hc ha hb)

/-- **Replacement / union closure** (regularity): the supremum of a `<c`-indexed
family of cardinals each `< c` is again `< c`.  This is the property that genuinely
needs the cardinal to be *regular* — it is the arithmetic form of ZFC's replacement
axiom holding in `V_c`. -/
theorem inaccessible_iSup_lt (hc : c.IsInaccessible) {ι : Type u} (hι : #ι < c)
    {f : ι → Cardinal.{u}} (hf : ∀ i, f i < c) : iSup f < c :=
  Ordinal.iSup_lt (lt_of_lt_of_le hι hc.isRegular.2) hf

/-- The two ZFC-critical closures bundled: an inaccessible cardinal is closed under
powerset (exponentiation) **and** under `<c`-indexed suprema.  This pair is the
arithmetic statement underlying Zermelo's theorem `V_c ⊨ ZFC`. -/
theorem inaccessible_zermelo_closure (hc : c.IsInaccessible) :
    (∀ a < c, (2 : Cardinal) ^ a < c) ∧
    (∀ {ι : Type u}, #ι < c → ∀ f : ι → Cardinal.{u}, (∀ i, f i < c) → iSup f < c) :=
  ⟨fun _ ha => inaccessible_two_power_lt hc ha,
   fun hι _ hf => inaccessible_iSup_lt hc hι hf⟩

/-! ## Part II — structural identity of inaccessibles -/

/-- An inaccessible cardinal is a limit cardinal: it is never a successor. -/
theorem inaccessible_isSuccLimit (hc : c.IsInaccessible) : Order.IsSuccLimit c :=
  hc.isStrongLimit.isSuccLimit

/-- An inaccessible cardinal is regular: it equals its own cofinality. -/
theorem inaccessible_cof_eq (hc : c.IsInaccessible) : c.ord.cof = c :=
  hc.isRegular.cof_eq

/-- The closure data characterizes inaccessibility: uncountable, regular and a
strong limit together are *equivalent* to being inaccessible. -/
theorem inaccessible_iff :
    c.IsInaccessible ↔ ℵ₀ < c ∧ c.IsRegular ∧ c.IsStrongLimit :=
  isInaccessible_def

/-! ## Part III — non-vacuity and the universe shadow of independence -/

/-- A genuine inaccessible cardinal exists *one universe up*: the cardinality of
`Type u`, viewed in `Type (u+1)`, is strongly inaccessible.  ZFC lives in a single
universe and cannot exhibit an inaccessible internally; universe polymorphism
supplies one "from outside", mirroring how the independence of "an inaccessible
exists" arises. -/
theorem univ_inaccessible : (Cardinal.univ.{u, v}).IsInaccessible :=
  IsInaccessible.univ

/-- The powerset-closure hypothesis is satisfiable: it holds at the witnessing
inaccessible `univ`. -/
theorem univ_powerset_closed (a : Cardinal.{max (u + 1) v}) (ha : a < Cardinal.univ.{u, v}) :
    2 ^ a < Cardinal.univ.{u, v} :=
  inaccessible_two_power_lt univ_inaccessible ha

/-- The replacement/union-closure hypothesis is satisfiable: it holds at `univ`. -/
theorem univ_iSup_closed {ι : Type (max (u + 1) v)} (hι : #ι < Cardinal.univ.{u, v})
    {f : ι → Cardinal.{max (u + 1) v}} (hf : ∀ i, f i < Cardinal.univ.{u, v}) :
    iSup f < Cardinal.univ.{u, v} :=
  inaccessible_iSup_lt univ_inaccessible hι hf

end GodelIncompletenessOQ04
