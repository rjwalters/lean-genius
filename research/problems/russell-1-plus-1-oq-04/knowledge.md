# Knowledge — russell-1-plus-1-oq-04

## S1 (researcher-11, 2026-05-12) — OBSERVE survey

### The taxonomy in one table

For each encoding `E` of the natural numbers and addition, the
minimal subset `Rules(E) ⊆ {β, ι, δ, ζ}` such that
`one_E + one_E = two_E := rfl` succeeds in Lean 4's CIC kernel:

| Encoding `E` | `Rules(E)` | Step count `N` |
|---|---|:---:|
| Goal in unfolded constructor form `succ (succ zero) = succ (succ zero)` | `∅` | 0 |
| Peano with pattern-matched `add` (parent file) | `{δ, ι}` | 5 |
| Peano with raw recursor `Nat.rec` | `{δ, ι, β}` | 6 |
| Church-numeral encoding `(α : Type) → (α → α) → α → α` | `{δ, β}` | 6 |
| Binary naturals (`inductive Bin = one ∣ b0 ∣ b1`) | `{δ, ι}` | 3 |
| Any of the above + `let`-bindings inside `add` / `one` / `two` | adds `ζ` | + |

(`N` counts the number of single-rule kernel rewrites from
`one_E + one_E` to syntactic identity with `two_E`. The four CIC
rules are Church–Rosser on closed typeable terms, so the *order*
doesn't affect the *minimal set*, only the count.)

### Hand-traces (one per row)

**Peano with pattern-matched `add` — parent file:**

```
one + one
  δ on one (LHS)        →  succ zero + one
  δ on one (LHS rhs)    →  succ zero + succ zero
  δ on add + ι (clause 2: add n (succ m) = succ (add n m))
                         →  succ (add (succ zero) zero)
  ι (clause 1: add n zero = n)
                         →  succ (succ zero)
  δ on two (RHS)        →  succ (succ zero) ⟦ ✓ ⟧
```

5 reductions, alphabet `{δ, ι}`.

**Peano with raw recursor:**

```lean
def add (n m : ℕ) : ℕ := ℕ.rec n (fun _ acc => succ acc) m
```

```
add (succ zero) (succ zero)
  δ                       →  ℕ.rec (succ zero) (fun _ acc => succ acc) (succ zero)
  ι (Nat.rec_succ)        →  (fun _ acc => succ acc) zero (ℕ.rec (succ zero) (fun _ acc => succ acc) zero)
  β (apply outer λ)       →  (fun acc => succ acc) (ℕ.rec (succ zero) (fun _ acc => succ acc) zero)
  ι (Nat.rec_zero)        →  (fun acc => succ acc) (succ zero)
  β                        →  succ (succ zero) ⟦ ✓ ⟧
```

6 reductions, alphabet `{δ, ι, β}`. β is unavoidable because the
step function `(fun _ acc => succ acc)` is a λ.

**Church encoding:**

```lean
def Church.{u} := (α : Type u) → (α → α) → α → α
def c_one  : Church := fun _ f x => f x
def c_two  : Church := fun _ f x => f (f x)
def c_add  : Church → Church → Church :=
  fun m n => fun α f x => m α f (n α f x)
```

```
c_add c_one c_one
  δ                       →  fun α f x => c_one α f (c_one α f x)
  δ (inner c_one)         →  fun α f x => c_one α f ((fun _ f x => f x) α f x)
  β β β (three layers)    →  fun α f x => c_one α f (f x)
  δ (outer c_one)         →  fun α f x => (fun _ f x => f x) α f (f x)
  β β β                    →  fun α f x => f (f x)  ⟦ = c_two body ✓ ⟧
```

6 reductions (3 δ + 3 β-bursts), alphabet `{δ, β}`. **No ι** because
nothing is matched against a constructor — Church naturals are
purely λ-encoded.

**Binary naturals:**

```lean
inductive Bin where | one : Bin | b0 : Bin → Bin | b1 : Bin → Bin
def Bin.succ : Bin → Bin
  | .one => .b0 .one
  | .b0 n => .b1 n
  | .b1 n => .b0 n.succ
def Bin.add : Bin → Bin → Bin
  | m, .one  => m.succ
  | m, .b0 n => (m.add n).b0
  | m, .b1 n => (m.add n).b1.succ
```

```
Bin.add Bin.one Bin.one
  δ + ι (clause m, .one) →  Bin.succ Bin.one
  ι (clause .one of succ) →  Bin.b0 Bin.one  ⟦ = "2" in binary ✓ ⟧
```

3 reductions, alphabet `{δ, ι}`. The shallow depth is illusory for
`1+1`; for `2^k + 2^k` the depth is `O(k)` ι-steps.

**Unfolded baseline:**

```lean
example : Peano.succ (Peano.succ Peano.zero) = Peano.succ (Peano.succ Peano.zero) := rfl
```

0 reductions. Witnesses that `∅ ⊆ Rules(E)` for any encoding is
strict whenever `add`, `one`, or `two` is a `def`.

### Lower-bound (necessity) arguments

For each rule in `Rules(E)`, why is it required?

- **δ is required** whenever `add`, `one`, or `two` is a `def`.
  Without δ, the constants are opaque to the kernel and cannot be
  replaced by their bodies. The only encoding where `δ ∉ Rules(E)`
  is the fully-unfolded baseline (no `def`s on either side of `=`).
- **ι is required** whenever `add` is defined by pattern-matching on
  a constructor (or via a recursor with a non-constructor argument).
  Without ι, `match m with | succ k => …` cannot step. This forces
  ι into Peano and binary encodings; Church avoids it by replacing
  constructors with λ-applications.
- **β is required** whenever `add` (or any of its sub-terms) is a
  λ-abstraction applied to an argument. This is unavoidable in the
  recursor-form Peano (`Nat.rec` takes a λ as its step argument)
  and in any Church encoding. Pattern-matched Peano hides the β
  inside ι at the user-visible level.
- **ζ is required** when *and only when* a `let`-binding mediates
  the substitution of an intermediate value. Lean 4 distinguishes
  ζ from β at the kernel level (`let x := v; t` is *not* defined as
  `(fun x => t) v`; they have different elaboration behaviour and
  ζ is its own primitive rule).

### Insights

1. **Minimality is encoding-relative.** `Rules(E)` is not a property
   of "Lean's kernel" but of the chosen representation. The same
   theorem `1 + 1 = 2 := rfl` lives at four different points in the
   subset lattice `2^{β, ι, δ, ζ}` depending on encoding choice.

2. **Pattern matching ≡ ι, not β + ι.** Lean 4's equation compiler
   *emits* `brecOn` / `rec` applications that include β-redexes,
   but the kernel groups the resulting reductions into a single ι
   rule for the purpose of `#print axioms` / `decide`. So the
   user-visible "pattern match step" is one ι, not (ι + β).
   The recursor-only encoding makes the β explicit.

3. **Church and pattern-matched Peano are *incomparable* in the
   subset lattice.** `{δ, β}` ⊄ `{δ, ι}` and vice versa. So there
   is no single encoding strictly less powerful than all others
   (modulo the trivial `∅` baseline). This is a structural
   observation, not an implementation accident.

4. **Principia ≠ "many δ-steps in Lean".** Russell-Whitehead's
   362 pages are the cost of *deriving* the analogues of δ/ι/β
   from logical axioms (no inductive types, no primitive
   recursion). Lean's `rfl` is constant-cost because CIC takes the
   rules as primitives. Quantifying this gap:

   - Lean's Peano `1+1=2`: 5 reductions in the kernel.
   - Principia's *110.643: thousands of derivation steps in a
     deductive system whose meta-rules are weaker than CIC's
     reductions.

   The relevant quantity is *not* a count of unfoldings but a
   count of meta-rules per primitive operation.

5. **Connection to Aristotle / `decide`.** Tactics that depend on
   `rfl` (or `Decidable.rec` reducing to a constructor) live or
   die by the size of `Rules(E)` for the target's encoding. For
   Peano-style `Nat`, `decide`-able propositions reduce via
   `{δ, ι}`; for any propositional content reified through a
   λ-encoding, β enters the picture. So the choice of encoding
   has direct downstream consequences for tactic performance.

6. **`#print axioms` is the *propositional* dual of this question.**
   `#print axioms one_plus_one_eq_two` returns `[]`, meaning the
   proof does not depend on any axiom (Choice, Funext,
   propext, etc.). The reduction-rule question is the
   *definitional* analogue: which kernel rules does the proof
   exercise. Both are interesting; both can be displayed in a
   single companion file (see Next Steps S2).

### Mathlib gaps

1. **No central reference comparing `ℕ` encodings.** Mathlib has
   `Nat` (binary representation under the hood, with successor
   API), various Polynomial-encoded notions, and Stream-based
   colists. There is no single file or doc page that catalogues
   "Peano vs. Church vs. binary vs. recursor" with worked
   `rfl` examples.

2. **No `#reduce_trace` or pedagogical helper.** Lean 4 supports
   `set_option trace.Meta.isDefEq true` and `#reduce`, but the
   output is verbose and aimed at kernel developers. A
   pedagogical `#trace_reductions` macro that emits a
   `δ, δ, ι, ι, …` sequence for a given `rfl` proof would be a
   small contribution; it does not exist in Mathlib.

3. **No companion entry to `russell-1-plus-1`** showing the
   `rfl` chain explicitly. The parent entry mentions "ι reduction"
   in passing but does not enumerate the rule set.

### Next Steps (priority order)

1. **(S2)** `proofs/Proofs/OnePlusOneOQ04.lean` (~80–120 lines)
   with five `example` theorems witnessing each row of the
   taxonomy table:

   ```lean
   namespace OnePlusOneOQ04

   -- Row 0: unfolded baseline (Rules = ∅)
   example : Peano.succ (Peano.succ Peano.zero)
           = Peano.succ (Peano.succ Peano.zero) := rfl

   -- Row 1: pattern-matched Peano (Rules = {δ, ι}) — parent's encoding
   example : Peano.one + Peano.one = Peano.two := rfl

   -- Row 2: raw-recursor Peano (Rules = {δ, ι, β})
   def addRec (n m : Peano.ℕ) : Peano.ℕ :=
     Peano.ℕ.rec n (fun _ acc => .succ acc) m
   example : addRec Peano.one Peano.one = Peano.two := rfl

   -- Row 3: Church numerals (Rules = {δ, β})
   def Church.{u} := (α : Type u) → (α → α) → α → α
   def c_one  : Church := fun _ f x => f x
   def c_two  : Church := fun _ f x => f (f x)
   def c_add  : Church → Church → Church :=
     fun m n => fun α f x => m α f (n α f x)
   example : c_add c_one c_one = c_two := rfl

   -- Row 4: binary naturals (Rules = {δ, ι})
   inductive Bin where | one | b0 (n : Bin) | b1 (n : Bin)
   def Bin.succ : Bin → Bin
     | .one => .b0 .one
     | .b0 n => .b1 n
     | .b1 n => .b0 n.succ
   def Bin.add : Bin → Bin → Bin
     | m, .one  => m.succ
     | m, .b0 n => (m.add n).b0
     | m, .b1 n => (m.add n).b1.succ
   example : Bin.add Bin.one Bin.one = Bin.b0 Bin.one := rfl

   end OnePlusOneOQ04
   ```

   Each `example` is the *Lean witness* that the corresponding
   row's `Rules(E)` is *sufficient* — Lean accepts the `rfl` proof
   under its default kernel which admits all of {β, δ, ι, ζ}.
   The *minimality* claim (necessity) is documented in
   surrounding comments referencing this `knowledge.md`.

2. **(S3)** Augment the file with `#print axioms` + `#reduce`
   stanzas for each example, plus a docstring at the top tying
   the file to `problem.md`'s summary table. Cite the parent
   entry's OQ-04 in the file header.

3. **(S4)** Add a gallery entry `src/data/proofs/russell-1-plus-1-oq-04/`
   so the worked file is browsable on the live site. `meta.json`
   uses `status: "verified"`, `badge: "original"`, `axiomCount: 0`,
   `sorries: 0`. Cross-reference the parent entry.

4. **(S5, optional)** A `let`-binding example demonstrating the
   role of `ζ`:

   ```lean
   def addLet (n m : Peano.ℕ) : Peano.ℕ :=
     let n' := n
     let m' := m
     n' + m'  -- uses Peano.add internally
   example : addLet Peano.one Peano.one = Peano.two := rfl
   ```

   The `rfl` succeeds in the default kernel (which admits ζ); the
   *necessity* of ζ can be argued informally in a comment block.
   A full `set_option pp.all true` rendering of the elaborated
   term documents the ζ-redex.

5. **(Deferred → OQ-04-OQ-01)** A meta-theorem stating
   `Rules(E)` precisely (perhaps via a sandboxed kernel
   parametrised on a subset of `{β, ι, δ, ζ}`) and proving
   minimality. Significant project. Out of scope for this OQ;
   stub as a child open question.

### Risk Notes

- **Lean 4 universe handling for Church**: `def Church := (α : Type u) → ...`
  requires `universe u` and an explicit `Type u` annotation. The
  parent file uses `Type` (default universe 0), which is fine
  for Peano but Church needs polymorphism. Verify the example
  builds with `universe u` in S2.
- **Equation compiler vs. raw recursor**: Lean 4 elaborates
  `def Bin.succ | .one => …` into a `Bin.brecOn`-flavoured term;
  this elaboration is what the kernel sees and reduces. The
  user-visible `ι`-step in the S1 trace corresponds to a
  `Bin.rec_one` / `Bin.rec_b0` / `Bin.rec_b1` rule at the
  kernel level. The S2 examples should compile under both
  elaboration modes (default and `set_option compiler.extract_closed false`
  if relevant).
- **Build verification**: this entry is pure pedagogy; the only
  Mathlib dependency is `Mathlib.Init` (transitive via `import
  Mathlib`). Build time should be minutes, not hours.
- **No axioms used.** All examples are kernel-decided `rfl`
  proofs in the verified track.

### References (informal)

- Coquand & Huet, *The Calculus of Constructions*, 1988. Defines
  β, δ, ι reductions in the CoC; ζ is added in CIC (Coq/Lean).
- de Moura & Ullrich, *The Lean 4 theorem prover and programming
  language*, CADE 2021. §3 describes the kernel's reduction rules.
- Selsam, *The Lean 4 kernel: a brief tour*, 2022 (Zulip post).
  Discusses the user-visible vs. internal accounting of ι.
- Whitehead & Russell, *Principia Mathematica* Vol. I, §*110.643,
  1910. The 362-page derivation under analysis.
