# external/

Git submodules vendoring upstream Erdős-problem data (see `.gitmodules`):

| Path | Upstream | Used for |
|------|----------|----------|
| `erdosproblems/` | https://github.com/teorth/erdosproblems | Authoritative problem metadata (status, tags, prize, OEIS) |
| `formal-conjectures/` | https://github.com/google-deepmind/formal-conjectures | Lean formalizations (`FormalConjectures/ErdosProblems/`) |

The submodules are not checked out by default (`git submodule status` shows them
uninitialized in a fresh clone). Fetch them with:

```bash
git submodule update --init external/erdosproblems external/formal-conjectures
```

Consumers: `scripts/erdos/external-sync.ts` (cross-references both trees and writes
`scripts/erdos/data/`), `scripts/erdos/create-stub.sh`, `scripts/erdos/find-stubs.ts`,
`scripts/erdos/process-gallery-candidate.ts`, and the Erdős enhancer role
(`.lean/roles/erdos-enhancer.md`). Dependabot bumps both pins monthly
(`gitsubmodule` group in `.github/dependabot.yml`).
