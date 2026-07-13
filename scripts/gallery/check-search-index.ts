#!/usr/bin/env npx tsx
/**
 * Search-index smoke check (issue #35117).
 *
 * The gallery listings payload truncates descriptions to a 140-char card
 * excerpt, which narrowed client-side search recall. The build emits a separate
 * precomputed search index (public/data/proofs/search-index.json and
 * public/data/research/research-search-index.json) carrying the FULL,
 * untruncated descriptions so search over description tails still works.
 *
 * This check runs after the annotation + research builds and fails the build if
 * the search index ever regresses back to the truncated excerpt (e.g. someone
 * accidentally points it at the listings field). Concretely it verifies, for
 * each index:
 *   1. The index file exists and parses.
 *   2. It has a non-trivial number of entries.
 *   3. At least one entry is longer than the listing excerpt cap — proving the
 *      index carries full text, not the truncated excerpt.
 *   4. No index value ends with the truncation ellipsis '…' — the excerpt
 *      marker must never appear in the full-text index.
 *
 * Usage: tsx scripts/gallery/check-search-index.ts
 */

import * as fs from 'fs'
import * as path from 'path'
import { fileURLToPath } from 'url'

const __dirname = path.dirname(fileURLToPath(import.meta.url))
const REPO_ROOT = path.join(__dirname, '../..')

// Must match the excerpt cap in scripts/annotations/build.ts and
// scripts/research/build.ts. Kept in sync manually — the check is deliberately
// tolerant (it only needs SOME entry to exceed this) so a future cap tweak
// won't spuriously fail.
const LISTING_EXCERPT_MAX = 140

interface IndexSpec {
  label: string
  indexPath: string
  minEntries: number
}

const SPECS: IndexSpec[] = [
  {
    label: 'proofs',
    indexPath: path.join(REPO_ROOT, 'public/data/proofs/search-index.json'),
    minEntries: 1,
  },
  {
    label: 'research',
    indexPath: path.join(REPO_ROOT, 'public/data/research/research-search-index.json'),
    minEntries: 1,
  },
]

let failed = false

for (const spec of SPECS) {
  if (!fs.existsSync(spec.indexPath)) {
    console.error(`FAIL [${spec.label}]: search index not found at ${spec.indexPath} — run the gallery build first`)
    failed = true
    continue
  }

  let index: Record<string, string>
  try {
    index = JSON.parse(fs.readFileSync(spec.indexPath, 'utf-8'))
  } catch (e) {
    console.error(`FAIL [${spec.label}]: search index is not valid JSON: ${e instanceof Error ? e.message : e}`)
    failed = true
    continue
  }

  const entries = Object.entries(index)
  if (entries.length < spec.minEntries) {
    console.error(`FAIL [${spec.label}]: search index has ${entries.length} entries (< ${spec.minEntries})`)
    failed = true
    continue
  }

  // Every value must be a string.
  const nonString = entries.find(([, v]) => typeof v !== 'string')
  if (nonString) {
    console.error(`FAIL [${spec.label}]: search index value for "${nonString[0]}" is not a string`)
    failed = true
    continue
  }

  // Full-text proof: at least one entry must exceed the excerpt cap. If the
  // index were built from the truncated listing field instead of the full
  // description, no value could exceed the cap.
  const longest = entries.reduce((max, [, v]) => Math.max(max, v.length), 0)
  if (longest <= LISTING_EXCERPT_MAX) {
    console.error(
      `FAIL [${spec.label}]: longest search-index entry is ${longest} chars (<= ${LISTING_EXCERPT_MAX}). ` +
        `The index appears to carry truncated excerpts, not full descriptions — ` +
        `verify it is built from the untruncated meta/problem description (issue #35117).`
    )
    failed = true
    continue
  }

  // Detect the truncation-excerpt signature: the excerpt() builder cuts to at
  // most LISTING_EXCERPT_MAX chars and appends '…', so a truncated excerpt ends
  // with '…' AND has length <= cap + 1. A full description that legitimately
  // ends in an author-written '…' (e.g. "3, 5, 7, 11, 13, 17, …") is far longer
  // than the cap and must NOT trip this — only the truncated-excerpt signature
  // should. Every index entry carries a description longer than the cap by
  // construction, so a short entry ending in '…' means the index was wrongly
  // pointed at the truncated listing field.
  const truncated = entries.find(([, v]) => v.endsWith('…') && v.length <= LISTING_EXCERPT_MAX + 1)
  if (truncated) {
    console.error(
      `FAIL [${spec.label}]: search-index entry "${truncated[0]}" looks like a truncated ` +
        `excerpt (ends with '…', length ${truncated[1].length} <= ${LISTING_EXCERPT_MAX + 1}). ` +
        `The full-text index must be built from untruncated descriptions (issue #35117).`
    )
    failed = true
    continue
  }

  console.log(
    `ok [${spec.label}]: ${entries.length} entries, longest ${longest} chars ` +
      `(> ${LISTING_EXCERPT_MAX} excerpt cap — full descriptions confirmed)`
  )
}

if (failed) {
  process.exit(1)
}

console.log('Search index checks passed.\n')
