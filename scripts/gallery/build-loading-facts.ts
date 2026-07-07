#!/usr/bin/env npx tsx
/**
 * Build loading-screen math facts (issue #35117, Track B)
 *
 * Samples ~100 short, self-contained, single-sentence facts from the
 * gallery's existing `overview.keyInsights` arrays (src/data/proofs/x/meta.json)
 * into a tiny static src/data/loading-facts.json that is safe to bundle
 * eagerly. Each fact carries `{ fact, slug, title }` so the loading screen
 * can attribute it and deep-link to the proof page. A handful of curated
 * classic quotes (slug: null) are seeded in as fallback flavor.
 *
 * Selection is deterministic (sha1-based) so repeated builds over the same
 * gallery produce a byte-identical file and don't churn git status.
 *
 * Usage: tsx scripts/gallery/build-loading-facts.ts
 */

import * as fs from 'fs'
import * as path from 'path'
import { createHash } from 'node:crypto'
import { fileURLToPath } from 'url'

const __filename = fileURLToPath(import.meta.url)
const __dirname = path.dirname(__filename)

const PROOFS_DATA_DIR = path.join(__dirname, '../../src/data/proofs')
const OUTPUT_FILE = path.join(__dirname, '../../src/data/loading-facts.json')

/** Total facts to emit (insights + quotes). Keeps the file to a few KB. */
const TARGET_COUNT = 100

interface LoadingFact {
  fact: string
  /** Proof-page slug for deep-linking; null for classic quotes. */
  slug: string | null
  /** Proof title, or the quote's author when slug is null. */
  title: string
}

/** Curated classic quotes — always included, attributed via `title`. */
const CLASSIC_QUOTES: LoadingFact[] = [
  {
    fact: 'A mathematician is a machine for turning coffee into theorems.',
    slug: null,
    title: 'Alfréd Rényi (popularized by Paul Erdős)',
  },
  { fact: 'My brain is open.', slug: null, title: 'Paul Erdős' },
  {
    fact: 'Wir müssen wissen — wir werden wissen. (We must know — we will know.)',
    slug: null,
    title: 'David Hilbert',
  },
  {
    fact: 'Mathematics is the queen of the sciences.',
    slug: null,
    title: 'Carl Friedrich Gauss',
  },
  {
    fact: 'God made the integers; all else is the work of man.',
    slug: null,
    title: 'Leopold Kronecker',
  },
  {
    fact: "In mathematics you don't understand things. You just get used to them.",
    slug: null,
    title: 'John von Neumann',
  },
  {
    fact: 'The essence of mathematics lies in its freedom.',
    slug: null,
    title: 'Georg Cantor',
  },
  {
    fact: 'Mathematics is the art of giving the same name to different things.',
    slug: null,
    title: 'Henri Poincaré',
  },
  {
    fact: 'Beauty is the first test: there is no permanent place in the world for ugly mathematics.',
    slug: null,
    title: 'G. H. Hardy',
  },
]

/**
 * Reject insights that are LaTeX/Lean/markdown-heavy or not self-contained:
 * math delimiters, code spans, dotted Lean identifiers, tactic talk, and
 * references to "the parent" entry (meaningless out of context).
 */
const REJECT = new RegExp(
  [
    '[$\\\\`_{}^~|<>=]', // LaTeX / code / markup characters
    '\\*\\*', // leftover bold markers
    '\\b[A-Za-z][A-Za-z0-9]*\\.[A-Za-z]', // dotted identifiers (Nat.choose, …)
    '\\bsimp\\b',
    '\\bLean\\b',
    '\\bMathlib\\b',
    '\\bsorr(y|ies)\\b',
    '\\btactic',
    '\\baxiom',
    '\\bparent\\b', // "the parent entry/identity" — not self-contained
  ].join('|'),
  'i'
)

const MIN_LEN = 60
const MAX_LEN = 170

function sha1(s: string): string {
  return createHash('sha1').update(s).digest('hex')
}

/** Normalize a keyInsight: unwrap a leading `**Label:**` into `Label: …`. */
function normalize(raw: string): string {
  let s = raw.trim()
  const labeled = s.match(/^\*\*([^*]+?)\*\*[:.]?\s*(.*)$/s)
  if (labeled) {
    const label = labeled[1].replace(/:$/, '').trim()
    const rest = labeled[2].trim()
    s = rest ? `${label}: ${rest}` : label
  }
  s = s.replace(/\*\*/g, '').replace(/\s+/g, ' ').trim()
  if (s && !/[.!?]$/.test(s)) s += '.'
  return s
}

/** Accept only short, single-sentence, markup-free insights. */
function isGoodFact(s: string): boolean {
  if (s.length < MIN_LEN || s.length > MAX_LEN) return false
  if (REJECT.test(s)) return false
  const body = s.slice(0, -1)
  if (/[.!?]\s/.test(body)) return false // multiple sentences
  return true
}

function main(): void {
  const dirs = fs
    .readdirSync(PROOFS_DATA_DIR, { withFileTypes: true })
    .filter((d) => d.isDirectory())
    .map((d) => d.name)
    .sort()

  // Best candidate per slug (lowest hash) so no proof dominates the deck.
  const bySlug = new Map<string, { hash: string; fact: LoadingFact }>()

  for (const dir of dirs) {
    const metaPath = path.join(PROOFS_DATA_DIR, dir, 'meta.json')
    if (!fs.existsSync(metaPath)) continue
    let meta: {
      slug?: string
      title?: string
      overview?: { keyInsights?: unknown[] }
    }
    try {
      meta = JSON.parse(fs.readFileSync(metaPath, 'utf-8'))
    } catch {
      continue // malformed meta.json — not this script's problem
    }
    const insights = meta.overview?.keyInsights
    if (!Array.isArray(insights)) continue
    const slug = meta.slug || dir
    const title = meta.title || slug
    for (const raw of insights) {
      if (typeof raw !== 'string') continue
      const fact = normalize(raw)
      if (!isGoodFact(fact)) continue
      const hash = sha1(`${slug}|${fact}`)
      const prev = bySlug.get(slug)
      if (!prev || hash < prev.hash) {
        bySlug.set(slug, { hash, fact: { fact, slug, title } })
      }
    }
  }

  const sampled = [...bySlug.values()]
    .sort((a, b) => (a.hash < b.hash ? -1 : 1))
    .slice(0, Math.max(0, TARGET_COUNT - CLASSIC_QUOTES.length))
    .map((c) => c.fact)

  // Interleave quotes among facts deterministically via a second hash sort.
  const all = [...CLASSIC_QUOTES, ...sampled].sort((a, b) =>
    sha1(a.fact) < sha1(b.fact) ? -1 : 1
  )

  fs.writeFileSync(OUTPUT_FILE, JSON.stringify(all, null, 2) + '\n')

  const bytes = fs.statSync(OUTPUT_FILE).size
  console.log(
    `loading-facts: wrote ${all.length} facts (${sampled.length} insights from ${bySlug.size} eligible proofs + ${CLASSIC_QUOTES.length} quotes) to ${path.relative(process.cwd(), OUTPUT_FILE)} (${(bytes / 1024).toFixed(1)} KB)`
  )
}

main()
