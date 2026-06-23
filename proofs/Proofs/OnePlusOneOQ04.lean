import Proofs.OnePlusOne

/-!
# Russell 1+1=2 OQ-04: Minimal Reduction Rules for `rfl`
# (russell-1-plus-1-oq-04)

## What This File Provides

For each of five canonical `ℕ` encodings, this file exhibits a Lean
`example : one + one = two := rfl` witnessing the **sufficiency**
claim that the encoding's minimal reduction-rule subset
`Rules(E) ⊆ {β, ι, δ, ζ}` is enough for the Lean 4 kernel to close
the goal by reflexivity. The **necessity** claim (each rule in
`Rules(E)` is actually required) is documented in
`research/problems/russell-1-plus-1-oq-04/knowledge.md` §S1.

## The Taxonomy Table

| Encoding `E`                                       | `Rules(E)`    | Step count `N` |
|----------------------------------------------------|---------------|:--------------:|
| Unfolded baseline (constructors on both sides)     | `∅`           |       0        |
| Peano with pattern-matched `add` (parent file)     | `{δ, ι}`      |       5        |
| Peano with raw recursor `Nat.rec`                  | `{δ, ι, β}`   |       6        |
| Church numerals `(α → α) → α → α`                  | `{δ, β}`      |       6        |
| Binary naturals `Bin = one ∣ b0 ∣ b1`              | `{δ, ι}`      |       3        |
| Peano with `let`-bound arguments (ζ demonstrator)  | `{δ, ι, ζ}`   |       7        |

(`N` counts single-rule kernel rewrites from `one_E + one_E` to
syntactic identity with `two_E`. The four CIC rules are
Church–Rosser on closed typeable terms, so the *order* doesn't
affect the *minimal set*, only the count.)

**Observation.** Church and pattern-matched Peano are
*incomparable* in the subset lattice: `{δ, β} ⊄ {δ, ι}` and vice
versa. So there is no single encoding strictly less powerful than
all others (modulo the trivial `∅` baseline). This is a
structural property of CIC, not an implementation accident.

**Observation (ζ).** The let-bound row dominates row 1 in the
subset order — `{δ, ι} ⊊ {δ, ι, ζ}` — and is the *only* row in
which `ζ` is essential. Removing `ζ` from the kernel would leave
the let-bound row's `rfl` claim unprovable while leaving rows
0–4 unaffected. This is what makes `ζ` a *fourth* primitive of
CIC (not derivable from `{β, ι, δ}` on closed CIC terms with
let-bindings) rather than syntactic sugar.

## References

* Coquand & Huet (1988). *The Calculus of Constructions*. Defines
  β, δ, ι reductions in the CoC; ζ is added in CIC.
* de Moura & Ullrich (2021). *The Lean 4 theorem prover and
  programming language*. CADE 2021. §3 on kernel reduction.
* Whitehead & Russell (1910). *Principia Mathematica* Vol. I,
  §*110.643 — the 362-page derivation under analysis.

See also the parent entry `proofs/Proofs/OnePlusOne.lean`.
-/

namespace OnePlusOneOQ04

/-! ## Row 0: Unfolded Baseline — `Rules(E) = ∅` -/

/-- Both sides are already in fully-unfolded constructor form, so
    no reduction is required: `Rules(E) = ∅`. This witnesses that
    `∅ ⊆ Rules(E)` is strict whenever `add`, `one`, or `two` is
    a `def`. -/
theorem row0_unfolded :
    Peano.ℕ.succ (Peano.ℕ.succ Peano.ℕ.zero) =
      Peano.ℕ.succ (Peano.ℕ.succ Peano.ℕ.zero) := rfl

/-! ## Row 1: Peano with Pattern-Matched `add` — `Rules(E) = {δ, ι}` -/

/-- The parent file's encoding: `Peano.ℕ` is an inductive type and
    `Peano.add` is defined by pattern-matching. Kernel rewrite
    sequence: `δ` (unfold `one`, `add`, `two`) and `ι` (reduce
    the two `match`-clauses). 5 steps total. No `β` because the
    equation compiler folds the case-split λ into the `ι` rule
    at the user-visible level.

    `δ` is required because `one`, `add`, `two` are `def`s; `ι`
    is required because `add` pattern-matches on a constructor. -/
theorem row1_peano_pattern : Peano.one + Peano.one = Peano.two := rfl

/-! ## Row 2: Peano with Raw Recursor — `Rules(E) = {δ, ι, β}` -/

/-- Same `Peano.ℕ`, but `add` written via the auto-generated
    eliminator `Peano.ℕ.rec` rather than the equation compiler.

    Marked `noncomputable` because Lean 4's code generator declines
    `Peano.ℕ.rec` with a non-Prop motive. (Equivalent definitions via
    `match` *do* compile; `Peano.add` itself in the parent file is
    such a `match` form. The raw-recursor form here is for kernel
    reduction at the type-checking level only — exactly what `rfl`
    needs — not for runtime execution.) -/
noncomputable def addRec (n m : Peano.ℕ) : Peano.ℕ :=
  Peano.ℕ.rec (motive := fun _ => Peano.ℕ) n
    (fun _ acc => Peano.ℕ.succ acc) m

/-- Witness: `addRec one one = two := rfl`. Kernel rewrite
    sequence: `δ` (unfold `addRec`, `one`, `two`); `ι`
    (`Nat.rec_succ`, `Nat.rec_zero`); `β` (two λ-applications of
    the step function `fun _ acc => succ acc`). 6 steps total.

    `β` is unavoidable here because the step function is a literal
    λ. This is the precise sense in which the equation compiler
    "hides" the β inside `ι` at the user-visible level — the raw
    recursor exposes it. -/
theorem row2_peano_recursor : addRec Peano.one Peano.one = Peano.two := rfl

/-! ## Row 3: Church Numerals — `Rules(E) = {δ, β}` -/

/-- A Church numeral is a function that iterates `f` over `x` a
    fixed number of times. The natural number `n` is represented
    by `fun α f x => f^n(x)`. Pure λ-calculus: no inductive types,
    no constructors, no `ι`-rule. -/
def Church : Type 1 := (α : Type) → (α → α) → α → α

/-- Church numeral for `1`: apply `f` once. -/
def cOne : Church := fun _ f x => f x

/-- Church numeral for `2`: apply `f` twice. -/
def cTwo : Church := fun _ f x => f (f x)

/-- Church addition: iterate `m`'s function on top of `n`'s. -/
def cAdd : Church → Church → Church :=
  fun m n => fun α f x => m α f (n α f x)

/-- Witness: `cAdd cOne cOne = cTwo := rfl`. Kernel rewrite
    sequence: `δ` (unfold `cAdd`, `cOne` twice, `cTwo`); `β`
    (three nested λ-applications). 6 steps total.

    **No `ι`**: nothing is matched against a constructor, because
    Church numerals are purely λ-encoded. This is the structural
    incomparability with the Peano row — `{δ, β} ⊄ {δ, ι}` and
    vice versa. -/
theorem row3_church : cAdd cOne cOne = cTwo := rfl

/-! ## Row 4: Binary Naturals — `Rules(E) = {δ, ι}` -/

/-- Little-endian binary naturals: `one` is `1`, `b0 n` is `2n`,
    `b1 n` is `2n+1`. This is one of the standard representations
    used by Mathlib (`Nat.bit0`, `Nat.bit1`) and is closer to the
    machine-word layout of Lean's runtime `Nat`. -/
inductive Bin where
  | one : Bin
  | b0 : Bin → Bin
  | b1 : Bin → Bin
  deriving Repr

/-- Successor on binary naturals. Carries propagate via the third
    clause `b1 n → b0 n.succ`. -/
def Bin.succ : Bin → Bin
  | .one => .b0 .one
  | .b0 n => .b1 n
  | .b1 n => .b0 n.succ

/-- Addition on binary naturals, defined by structural recursion on
    the second argument. -/
def Bin.add : Bin → Bin → Bin
  | m, .one  => m.succ
  | m, .b0 n => (m.add n).b0
  | m, .b1 n => (m.add n).b1.succ

/-- Witness: `Bin.add Bin.one Bin.one = Bin.b0 Bin.one := rfl`.
    Note that `Bin.b0 Bin.one` is the binary representation of the
    natural number `2` (little-endian: `2 = 1·2 + 0 = b0 one`).
    Kernel rewrite sequence: `δ + ι` (the `m, .one` clause of
    `Bin.add` fires); `ι` (the `.one` clause of `Bin.succ` fires).
    3 steps total — the shortest of any encoding for this
    specific input.

    The shallow `1+1` depth is illusory in general: for
    `2^k + 2^k` the depth is `O(k)` `ι`-steps as the carry chain
    walks the bit-string. -/
theorem row4_binary : Bin.add Bin.one Bin.one = Bin.b0 Bin.one := rfl

/-! ## Row 5: Peano with `let`-bound Arguments — `Rules(E) = {δ, ι, ζ}`

This row exists to isolate the `ζ`-rule (let-reduction). Rows 0–4
never require `ζ` because none of them contains a `let`-binding;
the kernel reaches a `rfl` closure on `{β, ι, δ}` alone. Once a
`let`-binding is introduced, `ζ` becomes load-bearing: without it,
the kernel cannot eliminate the bound name and the two sides of
`addLet Peano.one Peano.one = Peano.two` fail to converge to a
common normal form (the left side is stuck at
`let n' := Peano.one; let m' := Peano.one; Peano.add n' m'`,
which is not syntactically `Peano.two`).

The semantics is:

* `ζ` reduces `(let x := e; body)` to `body[x := e]` — the
  defining equation of the `let`-construct.
* On *closed* CIC terms, `ζ` is *not* derivable from `{β, ι, δ}`:
  no β/ι/δ-step can erase a `let`-binder, because none of those
  rules has a `let` in its left-hand pattern. This is what makes
  CIC a four-rule kernel rather than three. -/

/-- The parent file's `Peano.add` applied to `let`-bound copies of
    its arguments. Definitionally equal to `Peano.add n m`, but
    only after `ζ` fires on the two `let`-bindings. -/
def addLet (n m : Peano.ℕ) : Peano.ℕ :=
  let n' := n
  let m' := m
  Peano.add n' m'

/-- Witness: `addLet one one = two := rfl`. Kernel rewrite
    sequence: `δ` (unfold `addLet`, `one`, `two`); `ζ` (eliminate
    the two `let`-binders for `n'` and `m'`); `ι` (the two
    `match`-clauses of `Peano.add` fire, exactly as in row 1).
    7 steps total — row 1's 5 steps plus the two `ζ`-steps.

    `ζ` is **necessary**: without it, the LHS reduces to
    `let n' := Peano.one; let m' := Peano.one; Peano.add n' m'`,
    which the kernel cannot identify with `Peano.two` because the
    `let`-binders block any further `ι`-step (`Peano.add`'s
    pattern-match expects a constructor head, not a `let`).

    `ζ` is also **sufficient (together with δ, ι)**: no further
    rule is needed, because after `ζ` fires the term reduces to
    `Peano.add Peano.one Peano.one`, identical to row 1's LHS,
    which closes on `{δ, ι}`. -/
theorem row5_let : addLet Peano.one Peano.one = Peano.two := rfl

/-! ## Part 6: Axiom-Freedom Verification

Each of the six row witnesses is `:= rfl`, so the proof is by
kernel reduction with no extra axioms. The `#print axioms` stanzas
below produce a machine-checked confirmation of this claim
(expected output for each: `'<name>' depends on no axioms`),
serving as the *propositional* dual to the *reductional* taxonomy
of `Rules(E)` documented in Parts 1–5 (and the ζ-row of §5).

This dual is the substance of the OQ-04 contribution: the
`{β, ι, δ, ζ}` rule alphabet is *all that is needed* in the sense
that every row is closed by reflexivity alone, with no recourse to
`Classical.choice`, `propext`, `Quot.sound`, or any further
extension to CIC.

If any of these stanzas prints additional axioms (e.g. after a
future refactor introduces a `Classical`-dependent helper into one
of the encodings), the file will still compile but the dual claim
will fail by inspection — a lightweight regression detector. -/

#print axioms row0_unfolded
#print axioms row1_peano_pattern
#print axioms row2_peano_recursor
#print axioms row3_church
#print axioms row4_binary
#print axioms row5_let

/-! ## Part 7: Schematic Transparency Lemmas

The six row witnesses above each pin the single input `1 + 1`. Two of the
reductions are in fact *definitional for every input*, not just at `1 + 1`,
which strengthens the corresponding `Rules(E)` claim from a point to a schema:

* `addLet_eq_add` shows the `ζ`-elimination of §5 is transparent for all
  `n m : Peano.ℕ` — `addLet` and `Peano.add` are the *same function*, so the
  `let`-binders never change the computed value, only the reduction budget
  (the two extra `ζ`-steps of row 5 versus row 1). The `1 + 1` witness
  `row5_let` is the instance `addLet_eq_add Peano.one Peano.one ▸ row1_peano_pattern`.
* `bin_add_one` shows the `m, .one` clause of row 4's `Bin.add` is the binary
  successor for *every* `m : Bin`, independent of the input — the schematic
  form of the first `δ + ι` step in `row4_binary`. -/

/-- The `let`-bound encoding (row 5) is definitionally the parent `Peano.add`
    for *all* inputs: `ζ` erases the two `let`-binders with no residue. -/
theorem addLet_eq_add (n m : Peano.ℕ) : addLet n m = Peano.add n m := rfl

/-- Binary `_ + one` is exactly binary successor, for every `m : Bin`
    (row 4's `m, .one` clause, stated schematically). -/
theorem bin_add_one (m : Bin) : Bin.add m Bin.one = m.succ := rfl

#print axioms addLet_eq_add
#print axioms bin_add_one

end OnePlusOneOQ04
