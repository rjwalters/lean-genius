# Mathlib Contribution Gotchas (Pending)

**Agent-append-only.** Add new gotchas you discover at the bottom of
this file. Do **not** edit existing entries. Curator and Hermit sweeps
will promote well-formed entries into `GOTCHAS.md` and trim this file.
Cite issue #20854 in any promotion PR.

Each pending entry should follow the same shape as `GOTCHAS.md` (G1,
G2, …) but with a `P` prefix to indicate it is pending review:

```
## P<N>. <Title>

**Problem.** What goes wrong.

**Cause.** Why it goes wrong.

**Fix.** How to avoid or repair it.

**Source.** Issue/PR/commit that exposed it.

**Discovered by.** Agent ID or session.
```

Promotion criteria (a Curator or Hermit will apply these):

- Reproducible: the problem must be observable on a known file or PR.
- General: not a one-off typo or research mistake.
- Distinct: not already covered by a curated `GOTCHAS.md` entry.
- Citable: references a specific Mathlib style/naming section, an
  issue, a PR, or a commit.

If a pending entry sits here for more than two Curator sweeps without
being promoted or rejected, it should be trimmed with a one-line note
in the sweep PR explaining why.

---

<!-- Append new entries below this line. -->
