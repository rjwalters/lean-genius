# OQ slug redirects

`redirects.json` is the tracked source of truth mapping **old (retired) slug →
new slug** for entries that have been re-slugged under the bounded OQ naming
scheme (issue #39825, epic #39821). It exists so that when a deep ancestry slug
such as

    abel-ruffini-oq-04-oq-02-oq-02-oq-08-oq-01-oq-01-oq-01-oq-01-oq-01-oq-01-oq-01

is replaced by a bounded slug such as `abel-ruffini-oq007`, the old gallery URL
`/proof/<old>` keeps working with a `301` to `/proof/<new>` instead of 404-ing.

## Format

```jsonc
{
  "$comment": "...",        // any key starting with "$" is metadata, ignored
  "redirects": {
    "<old-slug>": "<new-slug>",
    "abel-ruffini-oq-04-...-oq-01": "abel-ruffini-oq007"
  }
}
```

- Keys and values are gallery slugs (kebab-case directory names under
  `src/data/proofs/`).
- The map is **not transitive** at serve time: if a slug is redirected more
  than once over its lifetime, collapse the chain to point directly at the
  final slug (the migration script does this).
- `$`-prefixed top-level keys (e.g. `$comment`, `$schema`) are metadata and are
  ignored by the build emitter and the migration script.

## How it reaches production

`scripts/gallery/build-redirects.ts` runs during `pnpm build` and emits a
Cloudflare Pages [`_redirects`](https://developers.cloudflare.com/pages/configuration/redirects/)
file to `public/_redirects` with one line per entry:

    /proof/<old-slug>  /proof/<new-slug>  301

Vite copies `public/` into `dist/`, which is the Pages build output
(`pages_build_output_dir = "dist"` in `wrangler.toml`). Cloudflare applies these
rules before its SPA fallback, so only retired slugs redirect; every other path
still resolves to the single-page app. The same map is also copied to
`public/data/proofs/redirects.json` for optional client-side use (e.g. resolving
an old slug reached via in-app navigation).

## Populating it

The foundation PR (#39825) ships this mechanism with an **empty** map. The mass
re-slugging that fills it in is deferred to **#39828**, which runs

    pnpm tsx scripts/gallery/migrate-oq-slugs.ts --apply

to compute the old→new mapping (and the `parentSlug`/`rootSlug` values) and
write both the renamed directories and these redirect entries.
