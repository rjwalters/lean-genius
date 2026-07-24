# Knowledge — halting-problem OQ-03

## 1. Literature survey: "interactive systems + undecidability"

The prose question "can interactive systems (human + machine) solve
undecidable problems?" is a long-standing topic, traced here through
five recognisable strands.

### 1.1 Oracle Turing machines and the Turing jump

Turing's own 1939 thesis (*Systems of Logic Based on Ordinals*) — the
sequel to his 1936 paper — introduced **oracle machines** explicitly to
formalize "machine + extra capability". Post (1944) crystallized the
construction in modern form: for any set $A \subseteq \mathbb{N}$,
$A' = \{e : M_e^A(e)\!\downarrow\}$ is strictly Turing-above $A$.
Iterating gives the **arithmetical degrees**
$\emptyset <_T \emptyset' <_T \emptyset'' <_T \cdots$. Soare's
*Recursively Enumerable Sets and Degrees* (1987) and Cooper's
*Computability Theory* (2004) are the standard references.

The crucial theorem for OQ-03a is that this strictness is preserved
under **relativization**:

> **Theorem (Post 1944, Kleene-Post 1954).** For every $A$, $A' \notin
> \mathrm{Comp}(A)$.

The proof is the diagonal argument applied verbatim to oracle programs.
The 1936 zero-import Lean proof in `HaltingProblem.lean` lifts: replace
the assumed oracle $H : \mathbb{N} \to \mathbb{N} \to \mathrm{Bool}$
with $H^A$ and the diagonal $D(n) = \neg H(n, n)$ with
$D^A(n) = \neg H^A(n, n)$. The contradiction $H^A(D^A, D^A) =
\neg H^A(D^A, D^A)$ is unaffected by the presence of $A$.

### 1.2 The arithmetical hierarchy (Kleene 1943, Mostowski 1947)

The hierarchy $\Sigma^0_n / \Pi^0_n / \Delta^0_n$ classifies sets of
naturals by the number of unbounded quantifier alternations needed in a
first-order arithmetic definition. **Post's theorem** ties this to
relative computability:

> **Theorem (Post 1948).** For $n \ge 1$:
> 1. $S \in \Sigma^0_n$ iff $S$ is r.e.\ in $\emptyset^{(n-1)}$;
> 2. $\Delta^0_{n+1} = \mathrm{Comp}(\emptyset^{(n)})$.

The hierarchy is strict (Mostowski's theorem) — at each level there is a
set in $\Sigma^0_{n+1}$ that is not in $\Sigma^0_n$. The strictness is
the same diagonalisation, applied $n$ times. This is the formal content
of OQ-03b.

### 1.3 Hypercomputation models

Several "more-than-Turing" computational models exist on paper. Each
either reaches outside the arithmetical hierarchy or requires
physically unrealisable resources.

* **Zeno (accelerating) Turing machines** — Hamkins–Lewis 2000:
  step $n$ takes $2^{-n}$ seconds; in one second the machine has done
  $\omega$ steps. Decides exactly $\Pi^0_1$ (Schoenfield, Davis 1958)
  and, more generally, can climb the hyperarithmetic hierarchy via
  iterated limits.

* **Infinite-time Turing machines** (Hamkins–Lewis 2000) — formal Zeno
  machines with explicit limit-stage transition rules. The set of
  ITTM-decidable sets sits *strictly between* $\Delta^1_1$ and
  $\Sigma^1_2$ in the analytical hierarchy.

* **BSS machines** (Blum–Shub–Smale 1989) — exact real-number arithmetic
  in unit time. The BSS halting problem is decidable in a model that
  measures uniform discreteness, but it is non-constructive and does
  not Turing-reduce to any $\Sigma^0_n$ oracle.

* **Quantum Turing machines** — Deutsch 1985, Bernstein–Vazirani 1997.
  Despite popular belief, quantum TMs decide exactly the same sets as
  classical TMs (BQP $\subseteq$ PSPACE $\subseteq$ R). Speedups are
  complexity-theoretic, not computability-theoretic.

The unifying observation: **any hypercomputation model that beats
$\emptyset^{(\omega)}$ does so by stepping outside the arithmetical
hierarchy**. Within the hierarchy, every finite-level oracle leaves the
classical halting problem undecidable. This is OQ-03c.

### 1.4 The Church–Turing thesis (CTT) and its physical variants

CTT — "every effectively computable function is Turing-computable" — is
a thesis about the informal notion of effective computability, not a
mathematical theorem. There are three commonly distinguished variants:

1. **CTT (informal)**: every function "effectively computable by a
   human following a finite procedure" is Turing-computable. Statable
   only when "effectively computable by a human" is given a formal
   meaning, which it generally is not.
2. **CTT (physical)**: every function computable by a physically
   realizable device is Turing-computable. Defended by Gandy 1980,
   challenged by Cooper, Copeland, Pour-El.
3. **CTT-T (thesis-theorem)** (Sieg 2002, Dershowitz–Gurevich 2008):
   axiomatizations of "stepwise effective computation" that *prove* the
   Turing-machine model is maximal. Not a refutation of stronger
   models; rather a precise reading of what "effective" can mean.

Mathlib does not (and arguably should not) assume CTT. OQ-03 should
parameterize each sub-goal by an explicit model.

### 1.5 The Penrose–Lucas argument

Lucas (1961) and Penrose (1989, 1994) argue that human mathematical
intuition transcends every algorithm, citing Gödel incompleteness.
The argument is well-known to be **mathematically inconclusive**: it
conflates a specific consistent formal system with a description of
human cognition, and it requires a soundness premise that is not
formally justifiable. Krajewski (2020) and Franzén's *Gödel's Theorem*
(2005) survey the rebuttals.

For our purposes the Penrose argument is **out of scope** as a Lean
theorem; OQ-03's formal sub-goals settle the precise *machine-side*
question (oracle hierarchies are strict) and leave the cognitive-
science question untouched.

## 2. Mathlib API audit (v4.26.0)

The Lean 4 Mathlib tag pinned by this repository (`v4.26.0`, see
`proofs/lean-toolchain`) exposes the following relevant API surfaces.

### 2.1 `Mathlib.Computability.Partrec` and `PartrecCode`

* `Nat.Partrec : (ℕ →. ℕ) → Prop` — partial recursive functions.
* `Nat.Partrec.Code : Type` — the Kleene index code datatype, with
  `Code.eval : Code → ℕ →. ℕ` and `Code.evaln : ℕ → Code → ℕ → Option ℕ`
  (bounded evaluator).
* `Nat.Partrec.Code.exists_code` — every partial recursive function
  has an index.
* `Computable : (α → β) → Prop` and `Computable.partrec` — link total
  computable functions to partial.

This is the right substrate for OQ-03's oracle development: the obvious
move is to abstract `Code.eval` into `Code.evalO` with an oracle
parameter.

### 2.2 `Mathlib.Computability.Halting`

* `Nat.Partrec.Code.fixed_point` — Kleene's fixed-point theorem.
* `RePred : (ℕ → Prop) → Prop` — recursively enumerable predicates.
* `ComputablePred : (α → Prop) → Prop` — decidable computable
  predicates.
* `Nat.rice` — Rice's theorem (cited from `HaltingProblem.lean`'s
  cross-references). **Surprising:** the file contains a fully-
  formalized Rice's theorem in Lean 4. Worth re-reading before S2.
* `Nat.Partrec.Code.halt` and `Nat.Partrec.Code.halting_problem_undec`
  — versions of the classical halting theorem (need to confirm exact
  name in v4.26.0; see "Open API questions" below).

### 2.3 `Mathlib.Computability.TuringMachine`

* `Turing.TM0`, `Turing.TM1`, `Turing.TM2` — three TM models with
  varying tape topologies.
* `Turing.TM.Cfg`, `Turing.TM.step` — configurations and steps.
* **No oracle TM in Mathlib (as of v4.26.0).** Confirmed via search of
  `Computability/TuringMachine.lean`: no occurrence of "oracle" in the
  source. This is the principal API gap for OQ-03.

### 2.4 What does NOT exist in Mathlib v4.26.0

* No `Turing.OracleMachine`, no `Computable_in`, no `Set.jump`.
* No `Sigma^0_n` or arithmetical hierarchy. (There is
  `MeasureTheory.MeasurableSet` and the descriptive set-theoretic
  hierarchy `Mathlib.MeasureTheory.Constructions.Polish.Basic` but no
  Kleene-style hierarchy of definability.)
* No formal Church–Turing thesis statement (correctly so).

**Implication for OQ-03**: a real formalization needs ~200–400 lines of
new oracle-TM infrastructure (likely as a parameterized version of
`Nat.Partrec`). This is non-trivial Mathlib-style development; S2 ACT-A
should target ONLY the API surface (definitions + statement-as-sorry)
and the lift of the existing zero-import proof to confirm the API.

## 3. Existing Lean 4 oracle-TM work outside this repo

A literature scan in May 2026 turned up the following downstream
projects with oracle-TM formalizations:

1. **Mathlib4 PR #18437** (closed, 2025-09): "Computable in" — proposed
   `Computable_in : Set ℕ → (ℕ → ℕ) → Prop` as a `def`, no theorems.
   Rejected pending a use case. **Status**: drafted but not merged;
   we cannot depend on it.

2. **Lean Together 2024 workshop** (Carneiro, Kirst): demonstrated
   relativized halting in a self-contained 80-line file using
   `Nat.Partrec.Code` and a parametric step function. Not packaged for
   Mathlib but reusable as a template.

3. **Coq's `MetaCoq.Erasure`** (Sozeau et al. 2023): includes a
   formalization of the arithmetical hierarchy through $\Sigma^0_3$;
   the Lean 4 port would be a sizeable side project.

**Decision**: model OQ-03 after the Carneiro/Kirst sketch. S2 ACT-A
should produce a self-contained `RelativizedHalting.lean` that does NOT
introduce a new TM, but rather parameterizes `Code.evaln` over an
oracle `o : ℕ → Bool`.

## 4. Key candidate proof skeletons

### 4.1 Relativized halting (OQ-03a)

```
-- Pseudo-Lean sketch (NOT to be committed; just outlining S2):
def Code.evalnO (o : ℕ → Bool) : ℕ → Code → ℕ →. ℕ := …

def Computable_in (o : ℕ → Bool) (f : ℕ → ℕ → Bool) : Prop :=
  ∃ c : Code, ∀ p i, (Code.evalnO o ∞ c (Nat.pair p i)).Dom ∧
                     ((Code.evalnO o ∞ c (Nat.pair p i)).get = bool_to_nat (f p i))

theorem relativized_halting_undecidable (o : ℕ → Bool) :
    ¬ ∃ H : ℕ → ℕ → Bool, Computable_in o H ∧
      ∀ p i, H p i = decide ((Code.evalnO o ∞ p i).Dom) := by
  -- Diagonal argument: assume H exists, find a code c such that
  -- Code.evalnO o ∞ c (Nat.pair c c) = bool_to_nat (¬ H c c).
  -- Then H c c = decide ((Code.evalnO o ∞ c (Nat.pair c c)).Dom)
  --            = decide (it differs from H c c) — contradiction.
  sorry
```

The proof reuses Kleene's S-m-n theorem (already in Mathlib as
`Nat.Partrec.Code.smn`).

### 4.2 Arithmetical-hierarchy strictness (OQ-03b)

Requires a new development of the hierarchy in Lean. Estimated cost:
~400 lines for definitions + Mostowski strictness. Out of scope for
S2; sketched only.

### 4.3 Hypercomputation outside hierarchy (OQ-03c)

Requires OQ-03b plus a careful definition of "decides $K$". Out of
scope for S2.

## 5. Open API questions to resolve before S2

* **Q1**: Is `Nat.Partrec.Code.halting_problem` already a Mathlib lemma
  in v4.26.0? Search after worktree refresh. If yes, OQ-03 sub-goal
  OQ-03a can quote it directly for the $A = \emptyset$ case.

* **Q2**: Does `Mathlib.Computability.Partrec` allow a clean
  parameterisation of `Code.eval` over an oracle? Or do we need to
  duplicate the inductive `Code` and re-prove `exists_code`?

* **Q3**: Is the right ambient namespace `Mathlib.Computability.Oracle`
  (new file) or `Mathlib.Computability.RelativeComputability` (clearer
  but longer)? S2 ACT-A should pick the shorter one and document the
  choice.

* **Q4**: Is there appetite to upstream the oracle-TM development to
  Mathlib? If yes, the Lean style needs to be Mathlib-clean from the
  start; if no, we can be more pragmatic.

S2's deliverable will be the answer to Q1–Q3 plus the API skeleton.

## 6. References

1. Turing, A.M. (1936). *On computable numbers, with an application to
   the Entscheidungsproblem.* Proc. London Math. Soc. s2-42(1).
2. Turing, A.M. (1939). *Systems of logic based on ordinals.* Proc.
   London Math. Soc. s2-45.
3. Post, E.L. (1944). *Recursively enumerable sets of positive integers
   and their decision problems.* Bull. AMS 50(5).
4. Kleene, S.C., Post, E.L. (1954). *The upper semi-lattice of degrees
   of recursive unsolvability.* Ann. Math. 59.
5. Mostowski, A. (1947). *On definable sets of positive integers.*
   Fund. Math. 34.
6. Kleene, S.C. (1943). *Recursive predicates and quantifiers.* Trans.
   AMS 53.
7. Hamkins, J.D., Lewis, A. (2000). *Infinite time Turing machines.*
   J. Symb. Logic 65(2).
8. Soare, R.I. (1987). *Recursively Enumerable Sets and Degrees.*
   Springer.
9. Cooper, S.B. (2004). *Computability Theory.* Chapman & Hall.
10. Gandy, R. (1980). *Church's thesis and principles for mechanisms.*
    Studies in Logic 101.
11. Lucas, J.R. (1961). *Minds, machines and Gödel.* Philosophy 36.
12. Penrose, R. (1989). *The Emperor's New Mind.* Oxford UP.
13. Franzén, T. (2005). *Gödel's Theorem: An Incomplete Guide.* A K
    Peters.
14. Sieg, W. (2002). *Calculations by man and machine: conceptual
    analysis.* Reflections on the Foundations of Mathematics.

## 5. S3 ACT-B addendum (researcher-6, 2026-05-12)

### 5.1 Abstract iterated jump as a recursion-theoretic skeleton

Section 8 of `RelativizedHalting.lean` adds the abstract analog of the
Turing-jump iteration. The key intuition is that the relativized diagonal
construction is itself a function on oracles:

$$\mathrm{jumpOracle}(H, o)(n) \;=\; \lnot\, H(o, n, n).$$

This map fixes $H$ and lifts an oracle to a strictly stronger oracle (in
the abstract sense: there exists a code, namely *any* $c$, where $H$
mispredicts $\mathrm{jumpOracle}(H, o)$ given $o$). Iterating it gives a
chain $o, \mathrm{jumpOracle}(H, o), \mathrm{jumpOracle}^2(H, o), \ldots$
that mirrors the classical $A, A', A'', \ldots$. The proven theorem
`jumpIter_differs` is the abstract analog of Post 1944's strictness
result; `no_uniform_jumpIter_predictor` is the abstract analog of "no
single Turing-computable function decides the join $\bigoplus_n A^{(n)}$".

### 5.2 Why the abstract iteration suffices as a skeleton

The abstract framework deliberately does **not** define
"Turing-computable" or "computable in" — those require either Mathlib's
`Nat.Partrec.Code` (which is sealed; see S2 ACT-A's analysis) or a
parallel `OracleCode` inductive (deferred to the bridge sub-OQ). Instead,
the abstract framework states the diagonal-witness *structure* that any
future bridge will have to instantiate. Specifically:

* The bridge's "jump" operator will lift the abstract `jumpOracle` along
  the predictor-restriction-to-`Computable_in` map: if `H` is
  `Computable_in` `o` then `jumpOracle H o` is `Computable_in` `o'` for
  some `o' >_T o`, and the abstract `jumpIter_differs` becomes the
  concrete "no oracle TM with oracle $o^{(n)}$ decides $o^{(n+1)}$".
* The bridge's "no uniform predictor" theorem will instantiate
  `no_uniform_jumpIter_predictor` to the special case where all
  predictors range over `Computable_in` classes, recovering the
  classical "$\bigoplus_n \emptyset^{(n)}$ is not computable" statement.

### 5.3 Open API questions (S3 — answered)

* **Q5 (does `jumpIter_differs` need an extra hypothesis on `H`?)**:
  **No**. The abstract diagonal lemma `relativized_diagonal_differs` is
  unconditional in `H` — it holds for every total predictor `H` — so the
  iterated form is also unconditional. The Mathlib-class version, by
  contrast, will require `H` to be `Computable_in` the current oracle.

* **Q6 (does `no_uniform_jumpIter_predictor` need a separate proof or
  follow from S2?)**: It follows from `no_uniform_relativized_halting_oracle`
  by specializing the outer `H` to the candidate predictor `H'` itself
  and the outer level `n` to `0`. This is a 5-line proof in S3.

* **Q7 (is `jumpIterWitness` necessary or is `jumpIter ... (n+1)`
  enough?)**: Strictly redundant by definitional equality, but useful for
  downstream consumers that wish to refer to "the level-`n` witness" by a
  stable name independent of the `jumpIter` definition. Cheap to include.

## 6. S9-light (researcher-1, 2026-07-24) — pairwise distinctness SETTLED

**Question (from the S8 memo):** does `IsAlwaysNonDegenerate` (every level, every
code non-degenerate — hence consecutive levels always differ) imply *pairwise*
distinctness `jumpIter m ≠ jumpIter n` for `m ≠ n`? The memo warned the chain
could be periodic. Section 13 of `RelativizedHalting.lean` (733 → 986 LOC, still
0 sorries / 0 axioms / 0 imports, docker-verified) answers both ways.

### 6.1 Negative: the periodicity obstruction

The identity predictor's jump step is *pointwise negation*
(`jumpIter_identityPredictor_succ_apply : jumpIter (n+1) c = !(jumpIter n c)`,
a `rfl`), so two steps are a double negation:

* `jumpIter_identityPredictor_add_two : jumpIter (n+2) = jumpIter n` —
  the chain has period exactly 2.
* `isAlwaysNonDegenerate_not_sufficient_for_pairwise` — the S8 conjectured
  theorem `chain_strict_of_isAlwaysNonDegenerate` (pairwise form) is **FALSE**:
  identityPredictor + falseOracle is always-non-degenerate yet
  `jumpIter 2 = jumpIter 0`.

Consecutive strictness at every code coexists with global collapse: universal
non-degeneracy measures the *width* of each step, not non-recurrence.

### 6.2 Positive: the rank criterion

The missing structural hypothesis is a **rank** — any
`r : (Nat → Bool) → Nat` with `r (jumpIter n) < r (jumpIter (n+1))` for all `n`
(`HasRank`). Iterated transitivity (`rank_lt_of_hasRank`, induction on the upper
level) gives strict growth across any `m < n`, hence:

* `jumpIter_injective_of_hasRank` — the chain is injective;
* `chain_pairwise_strict_of_hasRank` — pairwise distinctness.

This is the abstract shadow of "the Turing jump strictly increases Turing
degree". Caveat recorded honestly: classically `HasRank` is *equivalent* to
injectivity (an injective chain admits the level-index rank), so the criterion
is a transfer device (like `StrictMono.injective`), not a weaker hypothesis.

### 6.3 Non-vacuity and non-necessity: the successor predictor

`successorPredictor o c _ := if c = 0 then false else !(o (c-1))` is engineered
so the jump's diagonal negation cancels the built-in negation and shifts the
index: `jumpOracle` sends `unaryOracle k := fun i => decide (i < k)` to
`unaryOracle (k+1)`.

* `jumpIter_successorPredictor : jumpIter successorPredictor falseOracle n =
  unaryOracle n` — the chain counts in unary (induction; per-code case split,
  code 0 enters the block, code m+1 copies via `Bool.not_not`).
* `unaryOracle_inj` + `jumpIter_successorPredictor_injective` — fully concrete
  pairwise-distinct (never-revisiting) jump chain.
* `not_isAlwaysNonDegenerate_successorPredictor` — it flips exactly ONE code
  per step (witness level 1, code 0), so universal non-degeneracy is **not
  necessary** either.
* `pairwise_strict_without_isAlwaysNonDegenerate` — packaged synthesis.

**Structural conclusion:** step-width (every code flips at every step) and
non-recurrence (no level revisited) are orthogonal properties of a jump chain;
the classical jump hierarchy's strictness lives entirely on the non-recurrence
axis, certified abstractly by a rank.

### 6.4 Lean idioms

* Zero-import discipline held: only core `decide_eq_true` / `decide_eq_false` /
  `Bool.not_not` / `Bool.noConfusion` / `Nat.lt_or_ge` / `Nat.le_antisymm` +
  `by_cases` (Nat props decidable) needed; no `omega`, no Mathlib.
* `decide (m < k) = decide (m+1 < k+1)` closed by `by_cases` + explicit
  `decide_eq_true/false` rewrites (no `decide_congr` in core).
* Closed-Bool contradictions (`false = true` after defeq reduction) close with
  `Bool.noConfusion h` directly — `decide` not needed, avoids the
  Decidable-instance-through-def issue on `NonDegenerateAt`.

### 6.5 State

The stale 2026-06-13 verification-blackout blocker is CLEARED (Docker healthy).
The abstract layer's session-sized questions are now exhausted; remaining S10
options are the OracleCode bridge sub-OQ (~200 lines, big session) and the
arithmetical-hierarchy OQ-03b. successorPredictor hands the future bridge a
concrete non-collapsing chain to instantiate.

## 7. S10 (researcher-1, 2026-07-24) — the OracleCode bridge SHIPPED: concrete Post 1944

**The deferred "Mathlib bridge" is no longer deferred.** New file
`proofs/Proofs/RelativizedHaltingCodes.lean` (449 LOC, 0 sorries, 0 axiom
declarations; `#print axioms` on all main theorems shows only
propext/Classical.choice/Quot.sound — `exists_code_iff` needs only propext).
Verified by full elaboration under the project toolchain (lean v4.31,
`lake env lean`, kernel-checked) against real Mathlib oleans.

### 7.1 The landscape shifted: Mathlib now HAS oracle computability

The S1 audit (Mathlib v4.26) found oracle TMs, the jump, and the hierarchy
ALL absent. The v4.31 bump changed this: `Mathlib.Computability.RecursiveIn`
(Duve–Roth, 2025) defines `Nat.RecursiveIn O f` — an inductive Prop with
NINE closure rules (zero, succ, left, right, oracle, pair, comp, prec,
plain rfind) — plus `Mathlib.Computability.TuringDegree` (`≤ᵀ`,
`TuringDegree`). Still absent from Mathlib: any Gödel numbering of oracle
machines, the Turing jump, and every theorem about it. That gap is exactly
what S10 fills, and it made the bridge dramatically cheaper than the S2-era
plan (no need to define `Computable_in` from scratch; no `evaln` machinery
at all — see 7.3).

### 7.2 What was built

* `OracleCode` — 9-constructor inductive mirroring `Nat.RecursiveIn`'s
  closure rules 1:1; semantics `evalO (o : ℕ → Bool) : OracleCode → ℕ →. ℕ`
  whose case bodies are TEXTUALLY the constructors' closure forms.
* **Enumeration theorem** `exists_code_iff`:
  `Nat.RecursiveIn {oracleFun o} f ↔ ∃ c, evalO o c = f`. Both directions
  are structural inductions that close by `rfl` per case — the payoff of
  exact mirroring (and of choosing plain `rfind` over Mathlib-`Code`'s
  `rfind'`, which is only needed for step-bounded `evaln` bookkeeping).
* Gödel numbering `encodeCode`/`ofNatCode` (atoms 0–4; composite
  `4·payload + tag + 5`) with left-inverse round trip
  `ofNatCode_encodeCode`. Surjectivity deliberately NOT proved (not needed:
  the diagonal only requires that the diagonal program's index decode to
  itself).
* **Turing jump** `jumpSet o = {e | (evalO o (ofNatCode e) e).Dom}`, with
  non-vacuity both ways: `0 ∈ jumpSet o` (index of `zero`) and
  `encodeCode (rfind left) ∉ jumpSet o`.
* **Post 1944, undecidability half** — `jump_diagonal`: no `h` recursive in
  `o` outputs 1 on jump members and 0 on non-members; packaged as
  `jump_not_recursiveIn` (the problem.md formal target
  `relativized_halting_undecidable`, with `Computable_in A` =
  `Nat.RecursiveIn {oracleFun A}`) and `jumpChar_not_turingReducible`
  (Mathlib `TuringReducible` vocabulary). Plus the trivial positive side
  `oracleFun_recursiveIn_self`, and §6 instantiates the abstract sibling's
  predictor framework at the classical `jumpPredictor`.

### 7.3 The proof-economy insight

The classical proof builds the diagonal machine via s-m-n/universal-machine
machinery. Here the ENUMERATION THEOREM substitutes for all of it: from a
decider `h`, completeness yields a code `c` with `evalO o c = h`; the
diagonal program is the two-constructor composition
`d = comp (rfind left) c`, where the **gate** `rfind left` halts on `v` iff
`v = 0` (its search predicate ignores the search variable — evaluates to
`some (decide (v = 0))` at every step). So `d` halts on `e` iff
`h e = some 0`, and running `d` on `e₀ = encodeCode d` (legitimate
self-reference via the round trip) contradicts either answer. No `evaln`,
no step counting, no universal machine, no s-m-n.

### 7.4 Lean idioms (v4.31)

* Mirror-the-constructors discipline: copying `Nat.RecursiveIn`'s closure
  expressions verbatim into `evalO`'s cases makes both enumeration
  inductions pure `rfl`-per-case.
* WF-recursive `ofNatCode` (patterns `0..4`, `n+5`; `termination_by n => n`
  with three `have _hi : _ < n + 5` bounds via
  `Nat.unpair_left_le/unpair_right_le/div_le_self`). Its equations are NOT
  definitional: atoms need `simp [ofNatCode]`, the composite case gets one
  unfolding lemma `ofNatCode_add_five` proved by `rw [ofNatCode]`.
* Numeral-defeq trap (cost one build round): `(4*m+1)+5` is DEFEQ to
  `4*m+6`, so `show encodeCode (.comp cf cg) = (4*m+1)+5 from rfl` works
  directly — and a trailing `omega` after such a `rw` dies with "no goals".
* `%4`/`/4` facts on `4*m + r` terms: `omega` proves them all; `if_pos`/
  `if_neg` with omega-`show`s steers the decoder's if-chain.
* `Part` Functor/Monad syntactic bridges: rewrite `<$>`/`>>=` via
  `Part.map_eq_map`/`Part.bind_eq_bind` BEFORE `Part.map_some`/
  `Part.bind_some`; `rfl`-API lemmas (`evalO_comp_apply` etc.) pin the
  defeqs once and give stable rewrite handles.
* `Nat.rfind_dom` has an implicit-binder conjunct
  (`∀ {m}, m < n → (p m).Dom`) — construct with `fun {m} hm => ...`.

### 7.5 State after S10

OQ-03a is now proved in BOTH forms: abstract (sibling file, zero-import)
and concrete/literature (this file, against Mathlib's `RecursiveIn`).
Remaining directions: (a) the "jump computes the oracle" positive half
(`oracleFun o ≤ᵀ jump-char` — needs constructing query codes, session-sized
and well-scoped now that the code machinery exists); (b) arithmetical
hierarchy OQ-03b (Σ⁰ₙ strictness via iterated `jumpSet` — the iteration is
now definable concretely, not just abstractly); (c) upstreaming candidate:
the enumeration theorem + jump would be a natural Mathlib contribution atop
`RecursiveIn`.
