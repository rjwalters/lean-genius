# Mathlib Contribution Gotchas (Curated)

Human-curated, PR-reviewed gotchas that have tripped up actual
Mathlib-bound work in this repository. Each entry should explain the
problem, the underlying cause, and the fix.

This file is updated **only** through PR review. Agents capturing
in-flight discoveries should append to `GOTCHAS-pending.md` instead.
The Curator and Hermit periodically promote well-formed entries from
the pending file into this one and trim the pending file. Promotion
sweeps should cite issue #20854.

---

## G1. Do not name a lemma `*.def`

**Problem.** Lean 4 reserves `def` as a keyword. A name like
`Sperner.is_door.def` parses ambiguously and is rejected (or, worse,
silently shadows something).

**Cause.** The dotted-name convention from Lean 3 / Mathlib 3 sometimes
ended in `.def` to mean "the underlying definitional unfolding lemma".
That dies in Lean 4.

**Fix.** Use `_def` as the suffix instead — e.g. `is_door_def` rather
than `is_door.def`. Mathlib already follows this convention everywhere
the underlying unfolding lemma matters (see e.g. `Finset.card_def`).

Reference: [Lean 4 reserved keywords](https://leanprover-community.github.io/contribute/naming.html).

---

## G2. Drop `import Mathlib` before opening a PR

**Problem.** The broad `import Mathlib` glob pulls in every Mathlib
module. Mathlib CI flags it, and even if it built, it would slow down
the entire library's compile time for every downstream user.

**Cause.** While drafting in `proofs/Proofs/`, `import Mathlib` is
convenient — you do not need to know which sub-module a lemma lives in.
That convenience does not transfer to upstream.

**Fix.** Narrow imports to the modules actually used. Iteratively:
remove `import Mathlib`, replace with the specific modules the error
messages demand, re-run `./proofs/scripts/docker-build.sh`. Tools that
help: `lake exe mathlib4_dep_finder` (run via Docker), the
`Mathlib.Tactic.MinImports` linter once dropped in.

Reference: [Style guide → "Imports"](https://leanprover-community.github.io/contribute/style.html#header-and-imports).
Detected by automatable check **A5** in `STYLE-SCAN.md`.

---

## G3. Drop `set_option autoImplicit true` before submission

**Problem.** Mathlib disables `autoImplicit` globally. Files relying on
it will fail upstream's lint or, more subtly, will silently introduce
type-class arguments that the file's authors did not realize they had.

**Cause.** Auto-implicit makes drafting fast — undeclared identifiers
are inferred as implicit arguments rather than errors. This is fine
locally; it is forbidden upstream.

**Fix.** Remove `set_option autoImplicit true`. The build will then
fail on undeclared identifiers; promote each to an explicit
`variable` / argument / binder. This is *not* safely auto-removable
because the upgrade decisions are per-identifier.

Reference: [Style guide → "Variables and binders"](https://leanprover-community.github.io/contribute/style.html#variables-and-binders).
Detected by automatable check **A8** in `STYLE-SCAN.md`.

---

## G4. Avoid `import Mathlib.Tactic` (the tactic aggregate)

**Problem.** `import Mathlib.Tactic` imports every tactic Mathlib
provides. Upstream files import only the tactics they use.

**Cause.** Drafting convenience again. `import Mathlib.Tactic` means
you do not need to know which file `omega` or `polyrith` lives in.

**Fix.** Narrow to the specific tactic modules. The build's error
messages will tell you which one each unresolved tactic name comes
from. Common ones to remember:

- `omega` → `Mathlib.Tactic.Omega`
- `linarith` → `Mathlib.Tactic.Linarith`
- `polyrith` → `Mathlib.Tactic.Polyrith`
- `decide` → built-in, no import needed

Reference: [Style guide → "Imports"](https://leanprover-community.github.io/contribute/style.html#header-and-imports).
Detected by automatable check **A7** in `STYLE-SCAN.md`.

---

## G5. Module docstring uses `/-! ... -/`, not block comment

**Problem.** A top-of-file `/- ... -/` block is parsed as an ordinary
comment, not a module docstring. Mathlib's `docBlame` linter flags
this and several upstream tools (docs generation, declaration search)
miss the file's documentation.

**Cause.** The `/-!` prefix marks the block as a docstring rather than
a comment. Drafting often uses `/-` because it is more comfortable to
type.

**Fix.** Use `/-! # Title ... -/` for the file's top-level module
documentation. The body follows the same Markdown conventions as
ordinary docstrings — `## Main results`, `## References`, etc.

**Caveat.** This conflicts with the Aristotle parser rule in
`research/SORRY-CLASSIFICATION.md`, which prefers `/-` over `/-!`. If
the file is *also* an Aristotle target, you have to pick one — Mathlib
submission usually wins, so use `/-!` and remove the file from the
Aristotle queue. See LLM check **L8** in `STYLE-SCAN.md`.

Reference: [Style guide → "Documentation"](https://leanprover-community.github.io/contribute/style.html#documentation).
