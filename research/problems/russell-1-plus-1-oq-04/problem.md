# Problem: Minimal reduction rules for `1 + 1 = 2 := rfl`

## Statement

### Plain Language

In Lean 4 (and any dependent type theory based on CIC), the proof
`one + one = two := rfl` succeeds because the kernel reduces both
sides to the same normal form using a fixed catalogue of definitional
reductions. The standard names for these rules in the Coq/Lean
literature are:

- **β** — application of a λ to an argument: `(λ x. t) v ↦ t[v/x]`
- **δ** — unfolding of a defined constant: `c ↦ body_of c`
- **ι** — reduction of a recursor / pattern match on a constructor
- **ζ** — unfolding of a `let`-binding: `let x := v; t ↦ t[v/x]`

(Eta, proof-irrelevance and structural-eta are additional kernel
rules but are not part of the question.)

For each of several common representations of "the natural numbers"
and "addition", we ask:

> Which *subset* of `{β, ι, δ, ζ}` is **minimal** — i.e. necessary
> and sufficient — for the kernel to prove `one + one = two` by
> reflexivity?

### Formal Statement

For each encoding `E` (Peano `def add`, Peano via raw recursor,
Church numerals, binary naturals, `let`-laden definitions, …) let
`Rules(E) ⊆ {β, ι, δ, ζ}` denote the smallest subset such that

```lean
example : one_E + one_E = two_E := by rfl
```

succeeds under a kernel that admits only the reductions in `Rules(E)`.
Determine `Rules(E)` and explain the dependency structure.

## Classification

```yaml
tier: B
significance: 6
tractability: 7
tags:
  - seeker-selected
  - foundations
  - type-theory
  - peano-arithmetic
  - cic
  - principia
  - reduction-rules
```

**Significance**: 6/10 — A clean pedagogical question that exposes
the structure of Lean's kernel. Useful for teaching the mechanics of
`rfl`, for understanding why some encodings of `ℕ` are "more
definitional" than others, and as a concrete entry point into the
Curry–Howard reading of the parent gallery proof.

**Tractability**: 7/10 — Each encoding's analysis is a short
hand-trace plus a Lean witness (the encoded `add`, plus `theorem
ex : one + one = two := rfl`). The "minimality" claim is an
informal argument (no kernel can reduce `add` without δ, since `add`
is a defined name) backed by syntactic inspection.

## Why This Matters

1. **Pedagogy for type theory.** The parent entry advertises `1+1=2`
   as a one-line `rfl` proof, but obscures *why* it works at the
   level of the kernel. A clean reduction taxonomy makes the
   computation visible — exactly the kind of insight that motivates
   the propositions-as-types correspondence.

2. **Comparison with Principia Mathematica.** Russell & Whitehead's
   362-page derivation is, in modern terminology, the cost of
   δ-unfolding within a set-theoretic encoding (cardinal arithmetic,
   ramified type theory, equinumerosity machinery). The
   type-theoretic δ-chain is bounded by a small constant. Quantifying
   this contrast gives a *concrete* witness to the architectural
   advantage cited in the parent gallery entry.

3. **Foundations of `rfl`-driven decision procedures.** Many tactics
   in Lean (`decide`, `norm_num` in some configurations, kernel-level
   `Decidable` instances) rest on `rfl` reducing constructor terms.
   The reduction taxonomy here gives a principled basis for asking
   when those tactics can be expected to terminate quickly.

4. **Mathlib coverage.** Mathlib has no central reference comparing
   `ℕ` encodings (Peano, recursor-only, Church-encoded, binary)
   side-by-side. A worked file in the gallery would fill a small
   pedagogical gap; the Lean-Zulip community periodically rediscovers
   pieces of this taxonomy in ad-hoc threads.

## Theoretical Framework

### Reduction rules (CIC kernel, Lean 4 conventions)

| Rule | Trigger | Effect | Example |
|------|---------|--------|---------|
| β    | `(λ x. t) v` | `t[v/x]` | `(λ x. x + 1) 2 → 2 + 1` |
| δ    | a defined name `c` | substitute `body c` | `one → succ zero` |
| ι    | recursor / pattern match on a constructor | step into the matching branch | `Nat.rec_succ` |
| ζ    | `let x := v; t` | `t[v/x]` | `let p := 3; p + 1 → 3 + 1` |

(`η`, proof irrelevance, structural-eta for structures, and Lean-4
specific *smart-unfolding*/*hypoeta* normalisation are additional
kernel features but are not in the question's catalogue.)

### Confluence and normal forms

CIC's definitional equality is *Church–Rosser*: any sequence of
{β, ι, δ, ζ} reductions starting from a term `t` terminates (on
typeable closed terms) at a unique normal form `nf(t)`. So `t₁ = t₂`
holds by `rfl` iff `nf(t₁) = nf(t₂)` syntactically, *after*
permitting whichever subset of reductions you enabled.

This means `Rules(E)` has a natural meaning: it is the smallest
subset `S` such that `nf_S(one_E + one_E) = nf_S(two_E)`.

### Lower bounds via δ-unavoidability

If `one_E`, `two_E`, or `add_E` is a *defined name* (not a raw
constructor application), then **δ is in `Rules(E)`** — without δ,
the name can never be replaced by its body. So every encoding that
uses `def` is at least `{δ, …}`.

Conversely, the question is what *else* is needed once names are
unfolded:

- Pattern-matched `add` → need **ι** (and possibly β if the
  desugaring uses an explicit recursor application).
- Lambda-encoded `add` (Church) → need **β**.
- Recursor-only `add` → need **ι** *and* **β** (because the
  recursor's step argument is a λ).
- `let`-bindings inside any of these → need **ζ**.

## Representation Catalogue

### Encoding 1: Peano with pattern-matched `add` (parent file)

```lean
inductive ℕ where | zero | succ : ℕ → ℕ
def one : ℕ := succ zero
def two : ℕ := succ (succ zero)
def add : ℕ → ℕ → ℕ
  | n, zero   => n
  | n, succ m => succ (add n m)
```

Hand-trace of `add one one = two`:

```
add one one
 ↓ δ (one)
add (succ zero) one
 ↓ δ (one)
add (succ zero) (succ zero)
 ↓ δ (add) + ι (second clause matches)
succ (add (succ zero) zero)
 ↓ ι (first clause matches)
succ (succ zero)
 ↓ δ (two on the RHS)
two = succ (succ zero) ✓
```

Minimal set: **`{δ, ι}`**.

(In Lean 4, the equation compiler desugars `add` into a
`ℕ.rec`/`ℕ.brecOn` application, which technically introduces a
β-step when the step branch is applied; but the user-visible kernel
behaviour bundles that into a single ι-step. We adopt the
user-visible accounting here.)

### Encoding 2: Peano with raw recursor

```lean
def add (n m : ℕ) : ℕ := ℕ.rec n (fun _ acc => succ acc) m
```

Trace:

```
add (succ zero) (succ zero)
 ↓ δ (add)
ℕ.rec (succ zero) (fun _ acc => succ acc) (succ zero)
 ↓ ι (ℕ.rec_succ rule)
(fun _ acc => succ acc) zero (ℕ.rec (succ zero) (fun _ acc => succ acc) zero)
 ↓ β (apply outer λ to zero)
(fun acc => succ acc) (ℕ.rec (succ zero) (fun _ acc => succ acc) zero)
 ↓ ι (ℕ.rec_zero rule)
(fun acc => succ acc) (succ zero)
 ↓ β
succ (succ zero) = two ✓
```

Minimal set: **`{δ, ι, β}`**.

### Encoding 3: Church numerals

```lean
def Church := (α : Type) → (α → α) → α → α
def c_one : Church := fun _ f x => f x
def c_two : Church := fun _ f x => f (f x)
def c_add (m n : Church) : Church := fun α f x => m α f (n α f x)
```

`c_add c_one c_one` reduces to a λ-term whose body, after a chain of
β-steps, matches `c_two`'s body. **No constructors are involved**
(Church numerals are an inductive-free encoding inside Type, using
the impredicative-Prop trick disabled by default in Lean 4 but
available with `Type` indices).

Minimal set: **`{δ, β}`**.

In Lean 4, Church naturals are typically defined as
`def Church := (α : Type) → (α → α) → α → α`, and the proof
`example : c_add c_one c_one = c_two := rfl` succeeds **if and only
if** the kernel permits β reduction inside `fun`. (It does — that's
the definition of β.) The example builds with `funext` not required,
since both sides are λ-expressions and definitional equality goes
under binders.

### Encoding 4: Binary naturals

```lean
inductive Bin where
  | one : Bin
  | b0  : Bin → Bin
  | b1  : Bin → Bin
def Bin.succ : Bin → Bin
  | .one => .b0 .one
  | .b0 n => .b1 n
  | .b1 n => .b0 n.succ
def Bin.add : Bin → Bin → Bin
  | m, .one   => m.succ
  | m, .b0 n  => (m.add n).b0
  | m, .b1 n  => (m.add n).b1.succ
```

For `Bin.one + Bin.one = Bin.b0 Bin.one` (the binary "1 + 1 = 2"):

```
add one one
 ↓ ι (.one branch of add)
succ one
 ↓ ι (.one branch of succ)
b0 one ✓
```

Minimal set: **`{δ, ι}`** (same as Peano with pattern-matched add).

The depth of the ι-chain grows with the bit-length of the inputs, not
with the numeric magnitude — for `1 + 1` it is still constant, but
for `2^k + 2^k` it is `O(k)` ι-steps rather than `O(2^k)` as in Peano.

### Encoding 5: Definitions with `let`

```lean
def add_let (n m : ℕ) : ℕ :=
  let acc := m
  let base := n
  acc + base  -- or whatever expression
```

If `acc` and `base` appear in the body, a `let` desugars to a
β-redex of a λ in some compilers, but in Lean 4 the kernel exposes
**ζ-reduction** as a separate primitive (`let x := v; t ↦ t[v/x]`)
which is distinct from β. Any encoding that places intermediate
bindings inside `add` or `one`/`two` will require ζ in addition to
the base set.

Minimal set: **`{δ, ι, ζ}`** for `let`-laden Peano-style add.

### Encoding 0: Fully unfolded — the lower bound

If we state the goal as

```lean
example : succ (succ zero) = succ (succ zero) := rfl
```

then **no reductions are needed at all**; this is `Eq.refl (succ (succ zero))`. Minimal set: **`∅`**.

This is the strict lower bound: any encoding that uses defined names
or pattern-matched functions has `Rules(E) ⊋ ∅`.

## Summary table

| Encoding `E` | `Rules(E)` |
|---|---|
| Fully unfolded `succ (succ zero) = succ (succ zero)` | `∅` |
| Peano, pattern-matched `add` (parent file) | `{δ, ι}` |
| Peano, raw recursor `add` | `{δ, ι, β}` |
| Church numerals | `{δ, β}` |
| Binary naturals (`Bin`) | `{δ, ι}` |
| Any of the above + `let`-bindings | adds `ζ` |

## Connection to Principia Mathematica

Russell-Whitehead's *110.643 lives in a foundation where `1`, `2`,
and `+` are all *defined names* (cardinals, disjoint unions). In
modern terms, they are δ-redexes. The 362 pages are essentially:

1. **Definitional unfolding chain.** Each "definition" (`1 = {X : |X| = 1}`,
   `2 = {X : |X| = 2}`, `+` via disjoint unions, equinumerosity via
   bijection-existence) is a δ-step in a hypothetical Principia
   kernel. The chain is *long* — many hundreds of intermediate
   definitions.

2. **Inductive principles encoded as theorem schemata.** Principia
   does not have constructive `ι`-reduction; induction is a
   *theorem schema* parameterised by predicates, with each
   instantiation requiring a proof. CIC packages this into the
   primitive recursor.

3. **Auxiliary lemmas to substitute for β.** Without first-class
   functions (Russell's ramified type theory is technically
   higher-order but the function abstraction is more cumbersome than
   λ-calculus), function application is mediated by relations and
   descriptions, each requiring proof.

So the difference between Principia's 362 pages and Lean's `rfl` is
**not a difference in the number of reductions** — it is a
difference in the *primitiveness* of the reductions available to
the meta-system. CIC takes δ, ι, β, ζ as kernel primitives;
Principia derives every analogue from logical axioms.

A precise statement: **let `N(E)` be the length of the longest
reduction chain in `nf_{Rules(E)}(one_E + one_E)`.** Then:

| System | `Rules` | `N` (1+1=2) |
|---|---|---|
| Lean's CIC, Peano | `{δ, ι}` | 5 |
| Lean's CIC, recursor-only | `{δ, ι, β}` | 6 |
| Principia (set-theoretic) | derived from logical axioms only | thousands |

So the "362 pages" maps to "thousands of derivation steps in a system
without primitive δ/ι/β", not to "thousands of δ-steps in Lean's
kernel".

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `russell-1-plus-1` (parent) | Provides the inductive `Peano.ℕ`, the recursive `add`, and the `rfl` proof under analysis |
| `cantor-diagonalization` | Same family of "what does the kernel actually do" foundational entries |
| `derangements` | Uses Lean's built-in `Nat.add` (definitionally identical to `Peano.add`), so the `Rules({Peano, pattern-match})` analysis transfers verbatim |
| `arithmetic-series` | Builds on `Nat.add` commutativity proved in the parent file |

## Mathlib Infrastructure Map

This problem is largely *kernel-theoretic* — it asks about Lean's
reduction rules, not about a Mathlib theorem. Relevant
infrastructure for stating the lemmas:

| Need | Mathlib name (Lean 4) | Module |
|------|----------------------|--------|
| Inductive `ℕ` (Peano-style) | `Nat` (built-in) | core |
| Recursor for `ℕ` | `Nat.rec`, `Nat.casesOn` | core |
| Pattern-match desugaring | `Nat.rec`-elaboration in equation compiler | Lean 4 internals |
| `Eq.refl` | `Eq.refl` / `rfl` | core |
| Reflection of definitional equality | `#print axioms`, `#reduce` | Lean 4 tactics |
| Reduction tracing | `set_option trace.Meta.isDefEq true` | Lean 4 meta |

No external Mathlib dependency is needed for the worked file.

## Suggested Next-Action Decomposition

This is **OBSERVE** phase. No Lean changes yet — only this survey
and the worked taxonomy above. Concrete next-step deliverables:

1. **(S2)** A new `proofs/Proofs/OnePlusOneOQ04.lean` with five
   `example` theorems, one per encoding from the catalogue:
   - `ex_unfolded : succ (succ zero) = succ (succ zero) := rfl`
   - `ex_peano   : Peano.one + Peano.one = Peano.two := rfl`
   - `ex_recursor : ... := rfl` using `ℕ.rec`-based add
   - `ex_church  : c_one + c_one = c_two := rfl` (Church)
   - `ex_binary  : Bin.one + Bin.one = Bin.b0 Bin.one := rfl`

   Each `rfl` is the *witness* that the corresponding rule set
   suffices; a `#reduce` and a `set_option trace.Meta.isDefEq true`
   stanza adjacent to each example documents the chain.

2. **(S3)** Comment-block documentation in the file mapping each
   `example` to the table in this `problem.md`. The gallery entry
   for `russell-1-plus-1` already has a Part 4–7 narrative; the
   OQ-04 file is a parallel "what does the kernel do" companion.

3. **(S4)** Optional: a Church-encoded section that uses
   `def Church := (α : Type) → (α → α) → α → α` and verifies the
   `{δ, β}` claim. (Type universes in Lean 4 may force a `Type 1`
   annotation; verify against the pinned revision.)

4. **(S5)** Optional: a `let`-laden encoding to witness `ζ`'s
   role; build a single example that fails without ζ and succeeds
   with it (using `@[reducible]` annotations to expose the kernel
   behaviour).

5. **(Deferred)** A meta-theorem at the kernel level: define
   `Rules(E)` precisely and prove that each entry in the summary
   table is minimal. This is a *project-level* deliverable
   approaching a small paper rather than a single Lean file; punt
   to OQ-04-OQ-01.

Steps 1–2 are a tractable single-PR S2 deliverable (~80–120 lines).
Step 4 (`let`) is a tractable S3 deliverable. Steps 5+ are deferred.

## Risk Notes

- **Lean 4 kernel changes**: the Lean 4 elaborator has been
  refactored several times since 4.0; the exact desugaring of
  pattern matching into `brecOn`/`rec` may shift in future
  toolchain bumps. The `Rules(E)` analysis is robust to such
  changes (the rules are CIC primitives, not Lean 4 conveniences),
  but the *number* of intermediate steps in `#reduce` output may
  vary.
- **Church numerals + Lean 4 universes**: Lean 4 disallows
  `Church := (α : Type) → ...` at `Sort u` without explicit
  universe annotation. Use `Type 1` or `Type _` and verify the
  example builds.
- **Definitional vs. propositional equality**: this entire
  question is about *definitional* (`rfl`) equality, **not**
  propositional `=`. The propositional version of "1+1=2 needs no
  reductions" is trivially true; the definitional version
  (what the kernel can decide automatically) is the substantive
  one. Frame all theorems and examples as `:= rfl` to keep the
  scope unambiguous.
- **No axioms required** at any stage. Each example is in the
  `verified` track. `#print axioms` will be empty for the worked
  file.
