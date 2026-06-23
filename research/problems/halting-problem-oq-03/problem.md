# OQ-03 of the Halting Problem — Formal Statement

**Parent proof**: `halting-problem` (Turing 1936; `proofs/Proofs/HaltingProblem.lean`).

**Informal question** (from `src/data/proofs/halting-problem/meta.json`,
`openQuestions[2]`):

> Can interactive systems (human + machine) solve undecidable problems?

This memo turns that prose question into three concrete formal sub-goals
that Mathlib's existing computability stack can reach. Each sub-goal has
a sharp negative answer in the classical literature; the contribution of
this OQ entry is to state and (eventually) prove the negative answers in
Lean 4 against `Mathlib.Computability.*`.

## Background dictionary

The classical halting problem (Turing 1936) is the statement that the
set
$$K \;=\; \{\, n \in \mathbb{N} \;:\; \text{program $n$ halts on input $n$}\,\}$$
is not recursive (i.e.\ not computable). Equivalently — and this is the
formulation the parent proof's `HaltingProblem.lean` files use — there
is no Boolean-valued total function $H : \mathbb{N} \to \mathbb{N} \to
\mathrm{Bool}$ such that $H(p, i)$ correctly reports whether program $p$
halts on $i$.

An **oracle Turing machine** $M^A$ is a Turing machine equipped with a
"black-box" subroutine that decides membership in a fixed set
$A \subseteq \mathbb{N}$ in one step. The set of functions computable by
some $M^A$ is the **relative computability** class with oracle $A$,
written $\mathrm{Comp}(A)$.

The **Turing jump** of $A$, denoted $A'$, is the relativized halting
problem:
$$A' \;=\; \{\, e \in \mathbb{N} \;:\; M_e^{A} \text{ halts on input $e$}\,\}.$$
Post (1944) showed $A' \notin \mathrm{Comp}(A)$ for every $A$, so the
hierarchy $\emptyset, \emptyset', \emptyset'', \dots$ of iterated jumps
is strictly increasing.

The **arithmetical hierarchy** $\Sigma^0_n, \Pi^0_n, \Delta^0_n$
(Kleene 1943) classifies sets by the number of unbounded quantifier
alternations needed to define them in first-order arithmetic. Post's
theorem says $\emptyset^{(n)} \in \Sigma^0_{n+1} \setminus \Pi^0_{n+1}$,
giving a tight correspondence between syntactic complexity and degree
of unsolvability.

A **physically realizable computational system** is, on the standard
formalization of the Church–Turing thesis (CTT) due to Gandy (1980),
indistinguishable from a Turing machine. CTT itself is not a theorem of
Mathlib; we therefore parameterize each sub-goal by an explicit oracle
or model, never asserting CTT itself.

## Sub-goal OQ-03a — Oracle machines relativize but do not transcend

**Claim.** For every oracle $A \subseteq \mathbb{N}$, the relativized
halting set $A'$ is not in $\mathrm{Comp}(A)$. In particular, no oracle
machine can decide its own halting problem.

**Formal target.**
```
theorem relativized_halting_undecidable
    {A : Set ℕ} :
    ¬ Computable_in A (fun e => decide (e ∈ jump A))
```
where `Computable_in A f` means $f$ is computable by some oracle Turing
machine with oracle $A$, and `jump A` is the Turing jump.

**Why it is interesting.** Relativization is the standard formal
expression of "machine + extra capability". The diagonal argument used
in `HaltingProblem.lean` lifts verbatim: replace `H : ℕ → ℕ → Bool` with
$H^A$ and the diagonal program with its oracle-machine analog. The
proof should be a near-mechanical generalization of the existing zero-
import proof, but it cannot live in the zero-import file: it needs
either Mathlib's `Computability.Halting` API or a self-contained
oracle-TM development.

## Sub-goal OQ-03b — The arithmetical hierarchy is strict

**Claim.** $\Sigma^0_{n+1} \nsubseteq \Sigma^0_n$ for every $n \ge 0$.
Equivalently, $\emptyset^{(n+1)} \in \Sigma^0_{n+1} \setminus
\Sigma^0_n$.

**Formal target.**
```
theorem strict_arithmetical_hierarchy
    (n : ℕ) :
    ∃ S : Set ℕ, S ∈ Sigma n.succ ∧ S ∉ Sigma n
```

**Why it is interesting.** This is the precise sense in which "no finite
amount of oracle access (interactive Q&A with a fixed-depth oracle)
suffices to decide all undecidable problems". An "interactive system"
that asks $n$ rounds of yes/no questions to an arbitrarily powerful
oracle of complexity $\Sigma^0_k$ can decide exactly $\Sigma^0_{k+n}$
problems — never the whole arithmetical hierarchy. The statement is a
Lean-friendly stand-in for the philosophical question "can humans, by
intuiting beyond any specific oracle, do better than every machine?".

## Sub-goal OQ-03c — Hypercomputation is non-constructive

**Claim.** Any function $f : \mathbb{N} \to \mathbb{N}$ that decides the
classical halting set $K$ is not Turing-reducible from any oracle in
the arithmetical hierarchy of finite level.

**Formal target.**
```
theorem hypercomputation_outside_hierarchy
    (f : ℕ → Bool)
    (hf : ∀ n, f n = decide (n ∈ haltingSet)) :
    ∀ n, ¬ ∃ A : Set ℕ, A ∈ Sigma n ∧ Computable_in A f
```

**Why it is interesting.** "Interactive systems" interpreted as Zeno
machines, infinite-time Turing machines, BSS machines over $\mathbb{R}$,
or any hyper-arithmetic oracle, can in principle decide $K$ — but only
by reaching outside *every* level of the arithmetical hierarchy.
OQ-03c makes this precise: there is no finite-stage "human + machine"
collaboration (modeled as a finite-level oracle) that decides $K$.

## What this OQ entry does NOT claim

* It does **not** assert the Church–Turing thesis; CTT is a meta-
  mathematical hypothesis, not a Lean theorem.
* It does **not** refute Penrose-style claims about human cognition. The
  formal sub-goals say only that *any* system modelled by a finite-level
  oracle TM cannot decide $K$. Whether human cognition is so modelable
  is a separate empirical question.
* It does **not** require physical realizability. OQ-03c is a purely
  recursion-theoretic statement; physical interpretations are left to
  the discussion section of the proof entry, not the Lean source.

## Next session (S2) handoff target

S2 (ACT-A) is the right place to introduce the API surface — likely a
new file `proofs/Proofs/RelativizedHalting.lean` that:
1. Defines `Computable_in : Set ℕ → (ℕ → ℕ → Bool) → Prop` using
   Mathlib's `Nat.Partrec.Code` reused as an oracle-step language, OR
   re-uses `Computability.Halting` if it already exposes a relative
   variant.
2. Defines `jump : Set ℕ → Set ℕ` and states OQ-03a as a `sorry`.
3. Re-proves `no_halting_oracle` (already in `HaltingProblem.lean`) as
   the special case $A = \emptyset$ to confirm the API.

The full plan is in `state.md`.
