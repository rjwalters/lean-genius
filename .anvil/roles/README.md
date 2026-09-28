# anvil/roles/

Generic role definitions shared across skills. A skill composes one or more roles into its lifecycle commands.

## Planned roles

| Role | Stage | Reads | Writes |
|---|---|---|---|
| `drafter` | Draft | brief, prior version (if any) | `{thread}.{N}/` |
| `reviewer` | Review (general) | `{thread}.{N}/` | `{thread}.{N}.review/` |
| `auditor` | Review (fact-check) | `{thread}.{N}/` | `{thread}.{N}.audit/` |
| `critic` | Review (substantive critique) | `{thread}.{N}/` | `{thread}.{N}.critic/` |
| `reviser` | Revise | `{thread}.{N}/` + all `{thread}.{N}.<critic>/` siblings | `{thread}.{N+1}/` |
| `figurer` | Asset generation | text content | figures in current version dir |

Roles are markdown prompts, not code. None exist yet.
