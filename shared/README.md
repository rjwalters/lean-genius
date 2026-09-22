# shared/

Code shared between the frontend build tooling and the Cloudflare Pages Functions.
Currently one module:

- `db/schema.ts` — Drizzle ORM (sqlite-core) schema for the website's D1 database:
  `users`, `session_tokens`, `comments`, `comment_votes`, plus relations.
- `db/client.ts` — `createDb(d1: D1Database)` returning a Drizzle client bound to that schema.

Consumers: every handler in `functions/api/` and `functions/lib/auth.ts` import from
here, and `drizzle.config.ts` points `drizzle-kit` at `schema.ts` to generate the SQL
migrations in `drizzle/`.

This is **not** the research database. The research pipeline's SQLite
(`research/db/knowledge.db`, `research/db/schema.sql`) is gitignored runtime state
handled by `pnpm db:rebuild` / `pnpm db:export` — see `CONTRIBUTING.md`.
