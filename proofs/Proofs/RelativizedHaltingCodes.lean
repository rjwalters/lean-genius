/-
# Relativized Halting — the OracleCode bridge (OQ-03a, concrete form)

**Research entry: halting-problem-oq-03, Session S10.**

Parent question (OQ-03 of `halting-problem`): "Can interactive systems
(human + machine) solve undecidable problems?" Sub-goal OQ-03a asks for the
literature form of the negative answer: for every oracle `A`, the relativized
halting set `A'` (the Turing jump) is not computable with oracle access to
`A` (Post 1944). The sibling file `Proofs/RelativizedHalting.lean` proves the
*abstract* diagonal (any oracle-aware predictor fails on its own diagonal,
zero imports); its header defers "the Mathlib bridge" — a concrete machine
model whose programs are enumerable, so that genuine *self-reference* (a
program running its own index) becomes expressible. This file builds that
bridge and proves the concrete theorem.

## What is proved

Mathlib (since 2025, `Mathlib.Computability.RecursiveIn`, by Tanner Duve and
Elan Roth) defines `Nat.RecursiveIn O f`: `f : ℕ →. ℕ` is partial recursive
relative to the oracle set `O`, as an inductive Prop with nine closure rules
(zero, succ, left, right, oracle, pair, comp, prec, rfind). Mathlib has *no*
Gödel numbering for oracle machines, no Turing jump, and no relativized
halting theorem. This file supplies them:

1. `OracleCode` — an inductive type of oracle-machine programs whose nine
   constructors mirror the nine closure rules of `Nat.RecursiveIn` exactly,
   with semantics `evalO o c : ℕ →. ℕ` (oracle `o : ℕ → Bool`).
2. **Enumeration theorem** (`exists_code_iff`):
   `Nat.RecursiveIn {oracleFun o} f ↔ ∃ c, evalO o c = f` — the functions
   computable from oracle `o` are exactly the `OracleCode` semantics. Both
   directions are structural inductions; the mirroring makes them exact.
3. Gödel numbering: `encodeCode : OracleCode → ℕ` with decoder
   `ofNatCode : ℕ → OracleCode` and round-trip `ofNatCode_encodeCode`.
4. **Turing jump**: `jumpSet o = {e | (evalO o (ofNatCode e) e).Dom}` — the
   set of indices whose machine halts on its own index under oracle `o`.
5. **Post's theorem, undecidability half** (`jump_not_recursiveIn`,
   `jump_diagonal`): NO function recursive in `o` decides membership in
   `jumpSet o`. Corollary in Mathlib's Turing-degree vocabulary
   (`jumpChar_not_turingReducible`): the characteristic function of the jump
   is not Turing-reducible to the oracle. This is the formal target
   `relativized_halting_undecidable` requested by
   `research/problems/halting-problem-oq-03/problem.md`, with
   `Computable_in A` realized as Mathlib's `Nat.RecursiveIn {oracleFun A}`.

## Proof of the diagonal (§5)

Given a decider `h` recursive in `o`, the enumeration theorem yields a code
`c` with `evalO o c = h`. The **gate** `rfind left` halts on input `v` iff
`v = 0` (unbounded search over a predicate that ignores the search variable
and tests only `v`). The diagonal program `d := comp (rfind left) c`
therefore halts on input `e` iff `h e = some 0`, i.e. iff the decider claims
`e` does NOT halt on itself. Running `d` on its own index
`e₀ = encodeCode d` — the self-application the abstract sibling file could
not express — gives: `e₀ ∈ jumpSet o` iff the decider says
`e₀ ∉ jumpSet o`. Contradiction either way. No axioms, no sorries;
classical reasoning enters only through `Part`/`Set` and the classical
decidability of jump membership in the *statements*.

## Relation to the abstract layer

`Proofs/RelativizedHalting.lean` §3 diagonalizes against arbitrary
predictors `(ℕ → Bool) → ℕ → ℕ → Bool`; nothing there ties a predictor to a
machine model. Here the (classically defined) jump predictor instantiates
that framework (§6), and the new content is precisely that the diagonal is
*realized by a program*: undecidability holds against machines, not just
against function-abstractions.

## References

* Post, E.L. (1944). *Recursively enumerable sets of positive integers and
  their decision problems.* Bull. AMS 50(5). (Jump strictly above.)
* Soare, R.I. (1987). *Recursively Enumerable Sets and Degrees*, ch. III.
* Odifreddi, P. (1989). *Classical Recursion Theory*, ch. II–III.
* Mathlib: `Mathlib.Computability.RecursiveIn`,
  `Mathlib.Computability.TuringDegree` (Duve–Roth, 2025);
  `Mathlib.Computability.PartrecCode` (the unrelativized numbering that
  `encodeCode`/`ofNatCode` below are modeled on).

0 axioms, 0 sorries.
-/

import Mathlib.Computability.RecursiveIn
import Mathlib.Computability.TuringDegree
import Proofs.RelativizedHalting

namespace RelativizedHaltingCodes

/-! ### Section 1. Oracle codes and their semantics

Nine constructors, mirroring the nine closure rules of `Nat.RecursiveIn`
one-for-one. Unlike Mathlib's (unrelativized) `Nat.Partrec.Code`, which uses
the technical `rfind'` variant for `evaln` bookkeeping, plain `rfind`
suffices here: the enumeration theorem below matches derivations — not
step-bounded evaluations — and `Nat.RecursiveIn` closes under plain
`rfind`. -/

/-- Programs for oracle machines: the free syntax over the nine closure
rules of `Nat.RecursiveIn`. -/
inductive OracleCode : Type
  | zero : OracleCode
  | succ : OracleCode
  | left : OracleCode
  | right : OracleCode
  | oracle : OracleCode
  | pair : OracleCode → OracleCode → OracleCode
  | comp : OracleCode → OracleCode → OracleCode
  | prec : OracleCode → OracleCode → OracleCode
  | rfind : OracleCode → OracleCode
  deriving DecidableEq

/-- The oracle `o : ℕ → Bool` packaged as the total partial function
`n ↦ 1` if `o n` else `n ↦ 0` — the shape `Nat.RecursiveIn`'s oracle set
expects. -/
def oracleFun (o : ℕ → Bool) : ℕ →. ℕ :=
  fun n => Part.some (cond (o n) 1 0)

/-- Semantics: `evalO o c` is the partial function computed by the program
`c` with oracle `o`. Each case is textually the closure form of the
corresponding `Nat.RecursiveIn` constructor, so the enumeration theorem's
two inductions close definitionally. -/
def evalO (o : ℕ → Bool) : OracleCode → ℕ →. ℕ
  | .zero => fun _ => 0
  | .succ => Nat.succ
  | .left => fun n => (Nat.unpair n).1
  | .right => fun n => (Nat.unpair n).2
  | .oracle => oracleFun o
  | .pair cf cg => fun n => (Nat.pair <$> evalO o cf n <*> evalO o cg n)
  | .comp cf cg => fun n => evalO o cg n >>= evalO o cf
  | .prec cf cg => fun p =>
      let (a, n) := Nat.unpair p
      n.rec (evalO o cf a) fun y IH => do
        let i ← IH
        evalO o cg (Nat.pair a (Nat.pair y i))
  | .rfind cf => fun a =>
      Nat.rfind fun n => (fun m => m = 0) <$> evalO o cf (Nat.pair a n)

/- Definitional-unfolding API (each is `rfl`; stated once so later proofs
have stable rewrite handles instead of relying on `show`-level defeq). -/

theorem evalO_zero_apply (o : ℕ → Bool) (n : ℕ) :
    evalO o .zero n = Part.some 0 := rfl

theorem evalO_left_apply (o : ℕ → Bool) (n : ℕ) :
    evalO o .left n = Part.some (Nat.unpair n).1 := rfl

theorem evalO_oracle (o : ℕ → Bool) : evalO o .oracle = oracleFun o := rfl

theorem evalO_comp_apply (o : ℕ → Bool) (cf cg : OracleCode) (n : ℕ) :
    evalO o (.comp cf cg) n = evalO o cg n >>= evalO o cf := rfl

theorem evalO_rfind_apply (o : ℕ → Bool) (cf : OracleCode) (a : ℕ) :
    evalO o (.rfind cf) a =
      Nat.rfind fun n => (fun m => m = 0) <$> evalO o cf (Nat.pair a n) := rfl

/-! ### Section 2. The enumeration theorem

`Nat.RecursiveIn {oracleFun o}` and `evalO o` describe the same class of
partial functions. Soundness is induction on the code; completeness is
induction on the `RecursiveIn` derivation. Because the constructors mirror
exactly, every case is the corresponding rule applied to the inductive
hypotheses. -/

/-- Soundness: every oracle-code semantics is recursive in the oracle. -/
theorem evalO_recursiveIn (o : ℕ → Bool) :
    ∀ c : OracleCode, Nat.RecursiveIn {oracleFun o} (evalO o c)
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .oracle => .oracle _ rfl
  | .pair cf cg => .pair (evalO_recursiveIn o cf) (evalO_recursiveIn o cg)
  | .comp cf cg => .comp (evalO_recursiveIn o cf) (evalO_recursiveIn o cg)
  | .prec cf cg => .prec (evalO_recursiveIn o cf) (evalO_recursiveIn o cg)
  | .rfind cf => .rfind (evalO_recursiveIn o cf)

/-- Completeness: every function recursive in the oracle is the semantics of
some code. -/
theorem exists_code_of_recursiveIn {o : ℕ → Bool} {f : ℕ →. ℕ}
    (h : Nat.RecursiveIn {oracleFun o} f) : ∃ c : OracleCode, evalO o c = f := by
  induction h with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | left => exact ⟨.left, rfl⟩
  | right => exact ⟨.right, rfl⟩
  | oracle g hg => exact ⟨.oracle, (Set.eq_of_mem_singleton hg).symm⟩
  | pair _ _ ihf ihh =>
    obtain ⟨cf, rfl⟩ := ihf
    obtain ⟨cg, rfl⟩ := ihh
    exact ⟨.pair cf cg, rfl⟩
  | comp _ _ ihf ihh =>
    obtain ⟨cf, rfl⟩ := ihf
    obtain ⟨cg, rfl⟩ := ihh
    exact ⟨.comp cf cg, rfl⟩
  | prec _ _ ihf ihh =>
    obtain ⟨cf, rfl⟩ := ihf
    obtain ⟨cg, rfl⟩ := ihh
    exact ⟨.prec cf cg, rfl⟩
  | rfind _ ihf =>
    obtain ⟨cf, rfl⟩ := ihf
    exact ⟨.rfind cf, rfl⟩

/-- **Enumeration theorem.** The functions partial recursive in oracle `o`
are exactly the semantics of oracle codes — the relativized analog of
Mathlib's `Nat.Partrec.Code.exists_code`. -/
theorem exists_code_iff {o : ℕ → Bool} {f : ℕ →. ℕ} :
    Nat.RecursiveIn {oracleFun o} f ↔ ∃ c : OracleCode, evalO o c = f :=
  ⟨exists_code_of_recursiveIn, fun ⟨c, hc⟩ => hc ▸ evalO_recursiveIn o c⟩

/-! ### Section 3. Gödel numbering

An injective numbering with an explicit decoder. Atoms take `0..4`; a
composite with tag `r ∈ {0,1,2,3}` (pair/comp/prec/rfind) and payload `m`
takes `4 * m + r + 5`. Only the left-inverse property is needed downstream
(it gives the self-application step `ofNatCode (encodeCode d) = d`), so —
unlike Mathlib's `Denumerable` instance for `Nat.Partrec.Code` — we do not
prove surjectivity. -/

/-- Gödel number of an oracle code. -/
def encodeCode : OracleCode → ℕ
  | .zero => 0
  | .succ => 1
  | .left => 2
  | .right => 3
  | .oracle => 4
  | .pair cf cg => 4 * Nat.pair (encodeCode cf) (encodeCode cg) + 5
  | .comp cf cg => 4 * Nat.pair (encodeCode cf) (encodeCode cg) + 6
  | .prec cf cg => 4 * Nat.pair (encodeCode cf) (encodeCode cg) + 7
  | .rfind cf => 4 * encodeCode cf + 8

/-- Decoder. Numbers not in the range of `encodeCode` decode to junk
(harmlessly); all that matters is the round trip below. -/
def ofNatCode : ℕ → OracleCode
  | 0 => .zero
  | 1 => .succ
  | 2 => .left
  | 3 => .right
  | 4 => .oracle
  | n + 5 =>
    have _h1 : (n / 4).unpair.1 < n + 5 :=
      Nat.lt_succ_of_le (le_trans (le_trans (Nat.unpair_left_le _)
        (Nat.div_le_self _ _)) (Nat.le_add_right _ _))
    have _h2 : (n / 4).unpair.2 < n + 5 :=
      Nat.lt_succ_of_le (le_trans (le_trans (Nat.unpair_right_le _)
        (Nat.div_le_self _ _)) (Nat.le_add_right _ _))
    have _h3 : n / 4 < n + 5 :=
      Nat.lt_succ_of_le (le_trans (Nat.div_le_self _ _) (Nat.le_add_right _ _))
    if n % 4 = 0 then
      .pair (ofNatCode (n / 4).unpair.1) (ofNatCode (n / 4).unpair.2)
    else if n % 4 = 1 then
      .comp (ofNatCode (n / 4).unpair.1) (ofNatCode (n / 4).unpair.2)
    else if n % 4 = 2 then
      .prec (ofNatCode (n / 4).unpair.1) (ofNatCode (n / 4).unpair.2)
    else .rfind (ofNatCode (n / 4))
  termination_by n => n

/-- Unfolding lemma for the composite case of `ofNatCode` (the `have`
bindings in the definition are proof-irrelevant and reduce away). -/
theorem ofNatCode_add_five (n : ℕ) :
    ofNatCode (n + 5) =
      if n % 4 = 0 then
        .pair (ofNatCode (n / 4).unpair.1) (ofNatCode (n / 4).unpair.2)
      else if n % 4 = 1 then
        .comp (ofNatCode (n / 4).unpair.1) (ofNatCode (n / 4).unpair.2)
      else if n % 4 = 2 then
        .prec (ofNatCode (n / 4).unpair.1) (ofNatCode (n / 4).unpair.2)
      else .rfind (ofNatCode (n / 4)) := by
  rw [ofNatCode]

/-- **Round trip**: decoding an encoded program recovers it. This is the
lemma that legitimizes self-application: the diagonal program's index really
denotes the diagonal program. -/
theorem ofNatCode_encodeCode : ∀ c : OracleCode, ofNatCode (encodeCode c) = c
  | .zero => by simp [encodeCode, ofNatCode]
  | .succ => by simp [encodeCode, ofNatCode]
  | .left => by simp [encodeCode, ofNatCode]
  | .right => by simp [encodeCode, ofNatCode]
  | .oracle => by simp [encodeCode, ofNatCode]
  | .pair cf cg => by
    rw [show encodeCode (.pair cf cg) =
        4 * Nat.pair (encodeCode cf) (encodeCode cg) + 5 from rfl,
      ofNatCode_add_five,
      if_pos (show (4 * Nat.pair (encodeCode cf) (encodeCode cg)) % 4 = 0 by omega),
      show (4 * Nat.pair (encodeCode cf) (encodeCode cg)) / 4 =
        Nat.pair (encodeCode cf) (encodeCode cg) by omega,
      Nat.unpair_pair, ofNatCode_encodeCode cf, ofNatCode_encodeCode cg]
  | .comp cf cg => by
    rw [show encodeCode (.comp cf cg) =
        (4 * Nat.pair (encodeCode cf) (encodeCode cg) + 1) + 5 from by
          rw [show encodeCode (.comp cf cg) =
            4 * Nat.pair (encodeCode cf) (encodeCode cg) + 6 from rfl]; omega,
      ofNatCode_add_five,
      if_neg (show ¬(4 * Nat.pair (encodeCode cf) (encodeCode cg) + 1) % 4 = 0 by omega),
      if_pos (show (4 * Nat.pair (encodeCode cf) (encodeCode cg) + 1) % 4 = 1 by omega),
      show (4 * Nat.pair (encodeCode cf) (encodeCode cg) + 1) / 4 =
        Nat.pair (encodeCode cf) (encodeCode cg) by omega,
      Nat.unpair_pair, ofNatCode_encodeCode cf, ofNatCode_encodeCode cg]
  | .prec cf cg => by
    rw [show encodeCode (.prec cf cg) =
        (4 * Nat.pair (encodeCode cf) (encodeCode cg) + 2) + 5 from by
          rw [show encodeCode (.prec cf cg) =
            4 * Nat.pair (encodeCode cf) (encodeCode cg) + 7 from rfl]; omega,
      ofNatCode_add_five,
      if_neg (show ¬(4 * Nat.pair (encodeCode cf) (encodeCode cg) + 2) % 4 = 0 by omega),
      if_neg (show ¬(4 * Nat.pair (encodeCode cf) (encodeCode cg) + 2) % 4 = 1 by omega),
      if_pos (show (4 * Nat.pair (encodeCode cf) (encodeCode cg) + 2) % 4 = 2 by omega),
      show (4 * Nat.pair (encodeCode cf) (encodeCode cg) + 2) / 4 =
        Nat.pair (encodeCode cf) (encodeCode cg) by omega,
      Nat.unpair_pair, ofNatCode_encodeCode cf, ofNatCode_encodeCode cg]
  | .rfind cf => by
    rw [show encodeCode (.rfind cf) = (4 * encodeCode cf + 3) + 5 from by
        rw [show encodeCode (.rfind cf) = 4 * encodeCode cf + 8 from rfl]; omega,
      ofNatCode_add_five,
      if_neg (show ¬(4 * encodeCode cf + 3) % 4 = 0 by omega),
      if_neg (show ¬(4 * encodeCode cf + 3) % 4 = 1 by omega),
      if_neg (show ¬(4 * encodeCode cf + 3) % 4 = 2 by omega),
      show (4 * encodeCode cf + 3) / 4 = encodeCode cf by omega,
      ofNatCode_encodeCode cf]

/-! ### Section 4. The Turing jump -/

/-- **The Turing jump of `o`**: the relativized halting set — indices `e`
such that the `e`-th oracle machine, run with oracle `o`, halts on its own
index `e`. -/
def jumpSet (o : ℕ → Bool) : Set ℕ :=
  {e | (evalO o (ofNatCode e) e).Dom}

theorem mem_jumpSet {o : ℕ → Bool} {e : ℕ} :
    e ∈ jumpSet o ↔ (evalO o (ofNatCode e) e).Dom := Iff.rfl

/-- Non-vacuity, positive side: the program `zero` halts on everything, so
its index `0` is in every jump. -/
theorem zero_mem_jumpSet (o : ℕ → Bool) : 0 ∈ jumpSet o := by
  rw [mem_jumpSet, show ofNatCode 0 = .zero from by simp [ofNatCode],
    evalO_zero_apply]
  exact Part.some_dom 0

/-! ### Section 5. The diagonal: the jump is not computable in its oracle -/

/-- Gate behavior: `rfind left` halts exactly on input `0`. Its `rfind`
searches a predicate that ignores the search variable and tests only the
input, so the search terminates (at once) iff the input is `0`. -/
theorem evalO_rfind_left_dom (o : ℕ → Bool) (v : ℕ) :
    (evalO o (.rfind .left) v).Dom ↔ v = 0 := by
  have hp : ∀ n : ℕ,
      ((fun m => (m = 0 : Bool)) <$> evalO o .left (Nat.pair v n)) =
        Part.some (decide (v = 0)) := by
    intro n
    rw [evalO_left_apply, Part.map_eq_map, Part.map_some, Nat.unpair_pair]
  rw [show (evalO o (.rfind .left) v) =
    Nat.rfind (fun n => (fun m => m = 0) <$> evalO o .left (Nat.pair v n)) from
    evalO_rfind_apply o .left v]
  constructor
  · intro hdom
    obtain ⟨n, hn, -⟩ := Nat.rfind_dom.1 hdom
    rw [hp n, Part.mem_some_iff] at hn
    exact of_decide_eq_true hn.symm
  · rintro rfl
    exact Nat.rfind_dom.2
      ⟨0, by rw [hp 0]; simp, fun {m} hm => absurd hm (Nat.not_lt_zero m)⟩

/-- Non-vacuity, negative side: the gate's own index is NOT in the jump (the
gate halts only on input `0`, and its index is positive). So the jump is a
nonempty proper subset of `ℕ` — the undecidability below is not about a
degenerate set. -/
theorem gate_index_not_mem_jumpSet (o : ℕ → Bool) :
    encodeCode (.rfind .left) ∉ jumpSet o := by
  intro h
  rw [mem_jumpSet, ofNatCode_encodeCode, evalO_rfind_left_dom] at h
  simp [encodeCode] at h

/-- **The diagonal contradiction (Post 1944, undecidability half).** No
function `h` partial recursive in `o` can report membership in `jumpSet o`
(`1` on members, `0` on non-members): composing the gate with `h`'s code
gives the diagonal program, which halts on its own index iff `h` says it
doesn't. -/
theorem jump_diagonal (o : ℕ → Bool) (h : ℕ →. ℕ)
    (hrec : Nat.RecursiveIn {oracleFun o} h)
    (h1 : ∀ e, e ∈ jumpSet o → h e = Part.some 1)
    (h0 : ∀ e, e ∉ jumpSet o → h e = Part.some 0) :
    False := by
  obtain ⟨c, hc⟩ := exists_code_of_recursiveIn hrec
  -- The diagonal program: run the decider, then pass its answer through the
  -- gate — halt iff the answer was 0.
  have hdom : ∀ v : ℕ,
      h (encodeCode (.comp (.rfind .left) c)) = Part.some v →
      ((evalO o (ofNatCode (encodeCode (.comp (.rfind .left) c)))
          (encodeCode (.comp (.rfind .left) c))).Dom ↔ v = 0) := by
    intro v hv
    rw [ofNatCode_encodeCode, evalO_comp_apply, hc, hv, Part.bind_eq_bind,
      Part.bind_some, evalO_rfind_left_dom]
  by_cases hmem : encodeCode (.comp (.rfind .left) c) ∈ jumpSet o
  · -- The decider answers 1, so the diagonal diverges on its own index —
    -- contradicting membership, which says it halts there.
    have hd := mem_jumpSet.1 hmem
    rw [hdom 1 (h1 _ hmem)] at hd
    exact one_ne_zero hd
  · -- The decider answers 0, so the diagonal halts on its own index — which
    -- is exactly membership.
    exact hmem (mem_jumpSet.2 ((hdom 0 (h0 _ hmem)).2 rfl))

open Classical in
/-- **OQ-03a, literature form** (the `relativized_halting_undecidable`
target of `research/problems/halting-problem-oq-03/problem.md`): for every
oracle `o`, the characteristic function of the Turing jump `o'` is not
partial recursive in `o`. Machines with oracle access relativize but do not
transcend: their own halting problem escapes them. -/
theorem jump_not_recursiveIn (o : ℕ → Bool) :
    ¬ Nat.RecursiveIn {oracleFun o}
      (fun e => Part.some (if e ∈ jumpSet o then 1 else 0)) := by
  intro hrec
  exact jump_diagonal o _ hrec
    (fun e he => by simp [he]) (fun e he => by simp [he])

open Classical in
/-- **Turing-degree form**: in Mathlib's reducibility vocabulary, the jump's
characteristic function is not Turing-reducible to the oracle. Together with
`oracleFun_recursiveIn_self` (the oracle trivially computes itself), this is
the "strictly above" half of the strictness of the jump. -/
theorem jumpChar_not_turingReducible (o : ℕ → Bool) :
    ¬ TuringReducible
      (fun e => Part.some (if e ∈ jumpSet o then 1 else 0)) (oracleFun o) := by
  intro hred
  exact jump_not_recursiveIn o (RecursiveIn.iff_nat.1 hred)

/-- The trivial positive counterpart: the oracle is recursive in itself. -/
theorem oracleFun_recursiveIn_self (o : ℕ → Bool) :
    Nat.RecursiveIn {oracleFun o} (oracleFun o) :=
  .oracle _ rfl

/-! ### Section 6. Instantiating the abstract layer

The sibling file `Proofs/RelativizedHalting.lean` diagonalizes against
arbitrary predictors `(ℕ → Bool) → ℕ → ℕ → Bool`. The (classically defined)
jump predictor is such a predictor, so the abstract machinery applies to it —
and §5 above upgrades the abstract "no predictor matches every behavior" to
the concrete "no *machine* decides the jump". -/

open Classical in
/-- Jump membership as an abstract predictor: `H o p i` guesses whether
program `p` (as an index) halts on itself under oracle `o` (the input
argument `i` is ignored — jump membership is about self-application). -/
noncomputable def jumpPredictor : RelativizedHalting.RelativizedHaltingPredictor :=
  fun o p _ => decide (p ∈ jumpSet o)

/-- The abstract diagonal theorem of the sibling file, instantiated at the
concrete jump predictor: some behavior disagrees with it everywhere on the
diagonal. -/
theorem jumpPredictor_diagonalized (o : ℕ → Bool) :
    ∃ b : RelativizedHalting.Behavior,
      ∀ code : ℕ, jumpPredictor o code code ≠ b code :=
  RelativizedHalting.relativized_halting_undecidable o jumpPredictor

end RelativizedHaltingCodes
