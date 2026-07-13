# Mathlib Style Scan

Actionable checklist derived from the
[Mathlib style guide](https://leanprover-community.github.io/contribute/style.html)
and
[Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html).
Each item cites the section of the upstream guide it derives from so
this file stays auditable when Mathlib updates its guidelines.

Items are split into **Automatable** (runnable as a shell or Python
one-liner) and **LLM** (requires reading the file and reasoning).

The target file in all examples below is `proofs/Proofs/YourFile.lean`.
Substitute the real file when running the scan.

---

## Automatable checks

These checks should run as part of any red-team pass and require no
LLM judgement.

### A1. Line length ≤ 100 columns

Source: [Style guide → "Line length"](https://leanprover-community.github.io/contribute/style.html#line-length).
Mathlib's hard cap is 100 columns.

```bash
awk 'length > 100 {print FILENAME ":" NR ": " length " cols: " $0}' \
    proofs/Proofs/YourFile.lean
```

A clean file produces no output. Each hit is a violation.

### A2. No trailing whitespace

Source: [Style guide → "Whitespace"](https://leanprover-community.github.io/contribute/style.html#whitespace).
Mathlib's CI lints trailing whitespace.

```bash
grep -nP ' +$' proofs/Proofs/YourFile.lean
```

A clean file produces no output. **Auto-fix is safe** — strip trailing
whitespace and re-run `./proofs/scripts/docker-build.sh`.

### A3. No double blank lines

Source: [Style guide → "Whitespace"](https://leanprover-community.github.io/contribute/style.html#whitespace).
Mathlib uses single blank lines for separation; double blanks read as
intentional gaps but rarely are.

```bash
awk 'NR>1 && $0=="" && prev=="" {print FILENAME ":" NR ": double blank"} {prev=$0}' \
    proofs/Proofs/YourFile.lean
```

**Auto-fix is safe** — collapse runs of blank lines to a single blank.

### A4. Copyright header present

Source: [Style guide → "Copyright header"](https://leanprover-community.github.io/contribute/style.html#header-and-imports).
Every Mathlib file starts with an Apache 2.0 copyright block naming
authors.

```bash
head -5 proofs/Proofs/YourFile.lean | grep -E "Copyright \\(c\\) [0-9]{4}|Apache 2.0|Authors:"
```

A clean file produces three lines (copyright, Apache 2.0 reference,
authors). Missing any is a flag for human review.

### A5. No `import Mathlib` glob

Source: [Style guide → "Imports"](https://leanprover-community.github.io/contribute/style.html#header-and-imports).
Mathlib bans `import Mathlib` (the broad glob) in finished PRs; imports
must be narrowed to the modules actually used.

```bash
grep -n '^import Mathlib$' proofs/Proofs/YourFile.lean
```

A clean file produces no output. This is **not** auto-fixable; narrowing
imports requires reading the file. Flag for human review and suggest
running `lake exe mathlib4_dep_finder` or equivalent from inside the
Docker build wrapper to find the minimal import set.

### A6. No `_root_.` redundant prefixes

Source: [Naming guide → "Namespaces"](https://leanprover-community.github.io/contribute/naming.html#namespaces).
`_root_.` is only needed when there is a genuine name clash; otherwise
it adds noise.

```bash
grep -n '_root_\.' proofs/Proofs/YourFile.lean
```

Each hit needs reasoning: is there a name clash, or is the prefix
gratuitous? Flag for human review (the type checker will catch
incorrect removal).

### A7. No `import Mathlib.Tactic` glob

Source: [Style guide → "Imports"](https://leanprover-community.github.io/contribute/style.html#header-and-imports).
The `Mathlib.Tactic` module aggregates every tactic; upstream files
should import only the tactics they use.

```bash
grep -nE '^import Mathlib\.Tactic$' proofs/Proofs/YourFile.lean
```

A clean upstream-bound file produces no output. Like A5, this is not
auto-fixable; flag for human review.

### A8. No `set_option autoImplicit true`

Source: [Style guide → "Variables and binders"](https://leanprover-community.github.io/contribute/style.html#variables-and-binders).
Mathlib disables `autoImplicit`; any file that relies on it must be
fixed before submission.

```bash
grep -n 'set_option autoImplicit true' proofs/Proofs/YourFile.lean
```

A clean file produces no output. Auto-removal is unsafe — declarations
that relied on auto-implicit must be edited to use explicit binders.

### A9. No `<;> rfl` after `simp`

Source: [Style guide → "Tactic style"](https://leanprover-community.github.io/contribute/style.html#tactic-style).
`simp <;> rfl` is almost always redundant; `simp` already closes goals
reducible by `rfl`.

```bash
grep -n 'simp.*<;> rfl' proofs/Proofs/YourFile.lean
```

Each hit is a candidate for replacing `simp <;> rfl` with `simp`.
**Auto-fix is gated** by `./proofs/scripts/docker-build.sh` succeeding
after the edit.

### A10. No bare `sorry` outside `Mathlib`-internal files

Source: [Contribution guide → "What goes in Mathlib"](https://leanprover-community.github.io/contribute/index.html).
Mathlib PRs cannot contain `sorry`.

```bash
grep -nE '\bsorry\b' proofs/Proofs/YourFile.lean
```

A clean PR-ready file produces no output. This is a hard block; the PR
will fail CI.

---

## LLM checks

These checks require reading the file and reasoning. Each item cites
the Mathlib guide section it derives from.

### L1. Identifier naming: `lowerCamelCase` for terms and theorems

Source: [Naming guide → "General conventions"](https://leanprover-community.github.io/contribute/naming.html#general-conventions).
Theorems, definitions, and term-level names use `lowerCamelCase`.
Type-level names (structures, classes, types) use `UpperCamelCase`.

When scanning, list every `def`, `theorem`, `lemma`, `instance` and
flag any that use `snake_case` (other than mathematically-traditional
names like `inv_mul_cancel`, where Mathlib does use snake_case in the
*lemma name* — see L2). Pay special attention to local helpers that
might still carry a research-style name.

### L2. Lemma names follow the binders-first / connectives-last pattern

Source: [Naming guide → "Theorem naming conventions"](https://leanprover-community.github.io/contribute/naming.html#theorem-naming-conventions).
Mathlib lemma names read left-to-right matching the statement
structure. The classical example is `le_iff_forall_gt`: read as
"`≤` iff `∀ … >`", matching `a ≤ b ↔ ∀ c, c < a → c < b`.

For each `theorem`/`lemma`, check:

- Does the name's word order match the statement's binder structure?
- Are connectives (`iff`, `and`, `or`, `imp`) in the right positions?
- Are predicates ordered hypothesis-first, conclusion-last where
  applicable?

Flag deviations for human review; this is taste-heavy and not safely
auto-fixed.

### L3. `convert` only when explicit rewriting is materially worse

Source: [Style guide → "Tactic style"](https://leanprover-community.github.io/contribute/style.html#tactic-style)
and Mathlib reviewer convention: `convert` is fragile because it
depends on the term that Lean elaborates, so small changes elsewhere
can break the proof.

For each use of `convert`, check whether a `rw`/`simp`-based proof of
the same goal would be materially worse (much longer, much less
readable). If yes, keep `convert`; if no, suggest replacing it. Flag
for human review.

### L4. Prefer `exact?` results over manual term proofs when shorter

Source: Mathlib reviewer convention: prefer the shortest stable proof.

For short manual term proofs (e.g. one- or two-line `by` blocks that
construct an obvious term), invoke `exact?` mentally — if the suggested
proof is shorter and still passes the type checker, propose it. Flag
candidates for human review; do not auto-apply (the `exact?` suggestion
is sometimes stylistically worse even when shorter).

### L5. Redundant hypothesis detection

Source: [Style guide → "Definitions and theorems"](https://leanprover-community.github.io/contribute/style.html#definitions-and-theorems)
and Mathlib reviewer convention: unused hypotheses inflate signatures
and slow elaboration.

For each `theorem`/`lemma`, check whether every named hypothesis is
actually used in the proof body. The Lean type checker will not catch
this — it accepts unused hypotheses silently. Flag candidates by
running through each hypothesis and asking "if I removed this, would
the proof still go through?" (Often you can just try it and see.)

### L6. Candidate signature simplifications

Source: Mathlib reviewer convention and Tao's demo (flipping explicit
args to implicit can unlock shorter proofs).

For each `theorem`/`lemma` with an `(x : α)` argument, ask:

- Could this be `{x : α}` (implicit)? It can be if `x` is determined by
  the conclusion or by another argument.
- Could it be `[x : α]` (instance)? It can be if `α` is a class.

When a signature change is plausible, it belongs in the Mechanic queue,
not in a Researcher PR. The Mechanic can re-elaborate downstream files
and look for shortened proofs (Tao's demo demonstrates this exact
opportunity).

Flag candidates with a one-line rationale; do not auto-apply.

### L7. Docstring presence on public declarations

Source: [Style guide → "Documentation"](https://leanprover-community.github.io/contribute/style.html#documentation).
Every public theorem/definition in Mathlib has a `/--` docstring.
Private declarations (those prefixed `private`) do not strictly need
one, but it is encouraged.

For each public `def`/`theorem`/`lemma`/`structure`/`inductive`, verify
a `/--` docstring is present and not just a `--` line comment. Flag
missing docstrings.

### L8. Use `/-` block comments, not `/-!` docstring sections

Source: Parser incompatibility note from `research/SORRY-CLASSIFICATION.md`.
For files that may pass through Aristotle, the `/-!` form is parsed
differently and causes problems. Mathlib *itself* uses `/-!` for
section headers, so this check applies only if the file is also an
Aristotle target.

For Aristotle-targeted files: flag every `/-!` and suggest replacing
with `/-`. For pure Mathlib-bound files: this check is informational,
not a violation.

### L9. Module docstring at file top

Source: [Style guide → "Documentation"](https://leanprover-community.github.io/contribute/style.html#documentation).
Every Mathlib file starts with a `/-! # Title ...` module docstring
introducing the file. The docstring should include the main results
and key references.

Verify the file has a module docstring after the copyright block, with
at least a `# Title`, a one-paragraph summary, and a `## Main results`
or `## References` section if applicable.

### L10. `simp only [...]` over bare `simp` where the lemma list is detectable

Source: [Style guide → "Tactic style"](https://leanprover-community.github.io/contribute/style.html#tactic-style).
`simp only [<lemmas>]` is more robust because it does not pick up new
`@[simp]` lemmas added upstream. Bare `simp` is fine when the goal is
trivially closed; it is a smell when `simp` is doing real work.

For each bare `simp`, ask: can I name the specific lemmas that fired?
If yes, the call should become `simp only [...]`. Use
`set_option trace.Meta.Tactic.simp true in` (in an exploratory session,
not the committed file) to harvest the lemma list. Flag candidates for
human review; auto-applying is gated by re-running
`./proofs/scripts/docker-build.sh`.

---

## Running the scan

A bash one-liner that runs all automatable checks against a file:

```bash
FILE=proofs/Proofs/YourFile.lean
echo "=== A1 line length ==="
awk 'length > 100 {print NR ": " length " cols"}' "$FILE"
echo "=== A2 trailing whitespace ==="
grep -nP ' +$' "$FILE" || echo "(clean)"
echo "=== A3 double blank lines ==="
awk 'NR>1 && $0=="" && prev=="" {print NR ": double blank"} {prev=$0}' "$FILE"
echo "=== A4 copyright header ==="
head -5 "$FILE" | grep -E "Copyright \\(c\\) [0-9]{4}|Apache 2.0|Authors:" || echo "(missing!)"
echo "=== A5 import Mathlib glob ==="
grep -n '^import Mathlib$' "$FILE" || echo "(clean)"
echo "=== A6 _root_. prefixes ==="
grep -n '_root_\.' "$FILE" || echo "(clean)"
echo "=== A7 import Mathlib.Tactic glob ==="
grep -nE '^import Mathlib\.Tactic$' "$FILE" || echo "(clean)"
echo "=== A8 set_option autoImplicit true ==="
grep -n 'set_option autoImplicit true' "$FILE" || echo "(clean)"
echo "=== A9 simp <;> rfl ==="
grep -n 'simp.*<;> rfl' "$FILE" || echo "(clean)"
echo "=== A10 sorry ==="
grep -nE '\bsorry\b' "$FILE" || echo "(clean)"
```

The LLM checks (L1–L10) must be run by reading the file and applying
the criteria above. Capture findings in the PR description per
`SKILL.md` step 4.
