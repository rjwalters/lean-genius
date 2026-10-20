# functions/

Cloudflare Pages Functions backing the site's API. Each file under `api/` is a
file-based route (`functions/api/auth/login.ts` serves `/api/auth/login`).

| Route group | Files |
|-------------|-------|
| `api/auth/` | `login`, `logout`, `me`, `register`, `google/login`, `google/callback` |
| `api/comments/` | `index` (list), `create`, `[id]` (get/update/delete), `[id]/vote`, `counts` |
| `api/submissions/` | `create` — proof submissions, emailed via Resend |
| `api/users/me/` | `comments`, `username` |

`lib/` holds the shared pieces: `auth.ts` (session validation, bearer tokens),
`email.ts` (Resend client), `schemas.ts` (zod request schemas).

Data access goes through Drizzle: `shared/db/client.ts` (`createDb(env.DB)`) and the
tables in `shared/db/schema.ts`. The `DB` binding is the D1 database declared in
`wrangler.toml` (`lean-genius-db`, migrations in `drizzle/`). `wrangler.toml` also
sets `EMAIL_FROM` and `SUBMISSION_EMAIL`; `RESEND_API_KEY` is a Wrangler secret.

Deploy: `pnpm deploy` (build + `wrangler pages deploy dist`), or the deployer agent's
`scripts/deploy/sync-and-deploy.sh`. `scripts/deploy/check-account.sh` enforces the
target Cloudflare account.
