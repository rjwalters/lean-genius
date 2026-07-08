/**
 * Research Data Index
 *
 * Exports:
 * - getResearchListings: Fetch lightweight gallery listings (cached once per session)
 * - getResearchProblemAsync: Fetch full problem data by slug from the static asset tree
 *
 * Phase 3 of the build-perf durable fix (issue #20994, follow-up to phase 1
 * issue #20992 and phase 2 issue #20993). Previously this module used a
 * dynamic-template `import(`./problems/${slug}.json`)` glob to discover ~2074
 * per-problem JSON files, each of which Vite/Rollup pulled into the module
 * graph. That O(N) blowup mirrored the per-proof shim explosion that phase 2
 * cured. Phase 3 collapsed all of that to:
 *   - this file (a thin fetch-by-slug loader)
 *   - research-listings.json (single in-graph module — small at the time)
 *   - research-data-manifest.json (single small module mapping slug -> sha8
 *     hash for cache-busting; the manifest IS bundled with content hashing so
 *     any problem change busts the importing chunk)
 *
 * Listings eviction (issue #35117): research-listings.json grew to 2.1MB of
 * JSON inlined into an eagerly-loaded JS chunk. It is now emitted to
 * `public/data/research/research-listings.json` at build time (descriptions
 * truncated to card-length excerpts) and fetched once per session via
 * `getResearchListings()`. Its content hash rides in the data manifest under
 * the reserved `__listings__` key.
 *
 * All per-problem JSONs live under public/data/research/<slug>.json
 * (gitignored, build-generated) and are fetched at runtime. The committed
 * source-of-truth JSONs in `src/data/research/problems/` remain the canonical
 * inputs to `scripts/research/build.ts`; this file no longer touches them.
 */

import type { ResearchListing, ResearchProblem } from '@/types/research'

import dataManifest from './research-data-manifest.json'

const DATA_MANIFEST: Record<string, string> = dataManifest as Record<string, string>

/**
 * Reserved data-manifest key carrying the content hash of the emitted public
 * research-listings file (see scripts/research/build.ts). Not a problem slug.
 */
const LISTINGS_MANIFEST_KEY = '__listings__'

/**
 * Reserved data-manifest key carrying the content hash of the emitted public
 * research search-index file (see scripts/research/build.ts). Not a slug.
 */
const SEARCH_INDEX_MANIFEST_KEY = '__searchindex__'

/**
 * Precomputed research search index (issue #35117). Maps problem slug -> the
 * FULL, untruncated description (lowercased) so client-side search can match
 * text beyond the 140-char listings excerpt without reinflating the eager
 * listings payload. Fetched lazily only when the user searches.
 */
export type ResearchSearchIndex = Record<string, string>

let listingsPromise: Promise<ResearchListing[]> | null = null
let searchIndexPromise: Promise<ResearchSearchIndex> | null = null

/**
 * Fetch the lightweight research listings for the gallery page.
 *
 * The promise is cached module-level so the listings file is fetched at most
 * once per session regardless of how many consumers call this. A failed fetch
 * clears the cache so a later call can retry. Tags are normalized to always
 * exist (defensive — build.ts should provide them).
 */
export function getResearchListings(): Promise<ResearchListing[]> {
  if (!listingsPromise) {
    const v = DATA_MANIFEST[LISTINGS_MANIFEST_KEY] ?? ''
    listingsPromise = fetch(`/data/research/research-listings.json?v=${v}`)
      .then((resp) => {
        if (!resp.ok) throw new Error(`Failed to load research listings (HTTP ${resp.status})`)
        return resp.json() as Promise<ResearchListing[]>
      })
      .then((listings) => listings.map((l) => ({ ...l, tags: l.tags ?? [] })))
      .catch((e) => {
        listingsPromise = null
        throw e
      })
  }
  return listingsPromise
}

/**
 * Fetch the precomputed research search index (issue #35117).
 *
 * The listings payload from `getResearchListings()` carries only a 140-char
 * description excerpt, which narrowed full-text search recall (47.4% of
 * research descriptions exceed that excerpt). This index restores full-text
 * description search by mapping slug -> full lowercased description, built at
 * build time from the untruncated problem descriptions.
 *
 * The promise is cached module-level so the index is fetched at most once per
 * session. A failed fetch clears the cache so a later call can retry. Callers
 * should only invoke this when a search is actually active, so the eager first
 * paint never downloads the index (see useLazyFetchedData).
 */
export function getResearchSearchIndex(): Promise<ResearchSearchIndex> {
  if (!searchIndexPromise) {
    const v = DATA_MANIFEST[SEARCH_INDEX_MANIFEST_KEY] ?? ''
    searchIndexPromise = fetch(`/data/research/research-search-index.json?v=${v}`)
      .then((resp) => {
        if (!resp.ok) throw new Error(`Failed to load research search index (HTTP ${resp.status})`)
        return resp.json() as Promise<ResearchSearchIndex>
      })
      .catch((e) => {
        searchIndexPromise = null
        throw e
      })
  }
  return searchIndexPromise
}

/**
 * Asynchronously load research problem data for a given slug.
 *
 * Public signature preserved: `(slug) => Promise<ResearchProblem | undefined>`.
 * The only real consumer is `src/pages/ResearchProblemPage.tsx`; no change
 * needed there.
 *
 * The loader uses the in-graph data-manifest to know (a) which slugs exist and
 * (b) the sha8 cache-buster hash for each file. A missing slug or failed fetch
 * returns undefined rather than throwing, matching the previous contract.
 */
export async function getResearchProblemAsync(slug: string): Promise<ResearchProblem | undefined> {
  if (slug === LISTINGS_MANIFEST_KEY) return undefined
  const v = DATA_MANIFEST[slug]
  if (!v) return undefined

  try {
    const resp = await fetch(`/data/research/${slug}.json?v=${v}`)
    if (!resp.ok) return undefined
    return (await resp.json()) as ResearchProblem
  } catch (e) {
    console.error(`Failed to load research problem: ${slug}`, e)
    return undefined
  }
}
