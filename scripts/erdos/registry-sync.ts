/**
 * Registry sync tool: Update research registry with external Erdős data
 *
 * Operations:
 * - Enrich existing entries with external metadata (tags, OEIS, Lean paths)
 * - Add high-value problems we're missing (gallery candidates, easy targets)
 * - Update status for resolved problems
 */

import { readFileSync, writeFileSync, existsSync } from 'fs'
import { join, dirname } from 'path'
import { enrichProblems, type EnrichedProblem } from './external-sync'

const ROOT_DIR = join(dirname(import.meta.url.replace('file://', '')), '../..')
const REGISTRY_PATH = join(ROOT_DIR, 'research/registry.json')

interface RegistryEntry {
  slug: string
  phase: string
  path: string
  started: string
  status: string
  completed?: string
  lastUpdate?: string
  // New fields from external sync
  externalMeta?: {
    erdosNumber: number
    externalStatus: string
    tags: string[]
    oeis: string[]
    prize?: string
    leanFilePath?: string
    leanHasProof: boolean
    erdosUrl: string
    syncedAt: string
  }
}

interface Registry {
  version: string
  problems: RegistryEntry[]
  config: object
}

/**
 * Extract Erdős number from slug
 */
function extractErdosNumber(slug: string): number | null {
  const match = slug.match(/^erdos-(\d+)(?:-|$)/)
  return match ? parseInt(match[1]) : null
}

/**
 * Generate slug for a new problem
 */
function generateSlug(problem: EnrichedProblem): string {
  const baseSlug = `erdos-${problem.number}`

  // Add a descriptive suffix based on tags
  const tagSuffix = problem.tags[0]
    ?.toLowerCase()
    .replace(/[^a-z0-9]+/g, '-')
    .slice(0, 20)

  return tagSuffix ? `${baseSlug}-${tagSuffix}` : baseSlug
}

/**
 * Load registry
 */
function loadRegistry(): Registry {
  return JSON.parse(readFileSync(REGISTRY_PATH, 'utf-8'))
}

/**
 * Save registry
 */
function saveRegistry(registry: Registry): void {
  writeFileSync(REGISTRY_PATH, JSON.stringify(registry, null, 2) + '\n')
}

export interface SyncOptions {
  dryRun?: boolean
  enrichOnly?: boolean // Only update existing entries, don't add new ones
  addGalleryCandidates?: boolean // Add resolved + Lean problems
  addEasyTargets?: boolean // Add undergraduate-level problems
  addResearchCandidates?: boolean // Add open + Lean problems
  maxNewEntries?: number // Limit new additions
  verbose?: boolean
}

export interface SyncResult {
  enriched: number
  added: number
  skipped: number
  errors: string[]
}

/**
 * Sync registry with external data
 */
export function syncRegistry(options: SyncOptions = {}): SyncResult {
  const {
    dryRun = false,
    enrichOnly = false,
    addGalleryCandidates = true,
    addEasyTargets = true,
    addResearchCandidates = false,
    maxNewEntries = 50,
    verbose = false,
  } = options

  console.log('=== Registry Sync ===\n')

  const registry = loadRegistry()
  const enrichedProblems = enrichProblems()

  // Build lookup map
  const externalByNumber = new Map<number, EnrichedProblem>()
  for (const p of enrichedProblems) {
    externalByNumber.set(p.number, p)
  }

  const result: SyncResult = {
    enriched: 0,
    added: 0,
    skipped: 0,
    errors: [],
  }

  // Track which Erdős numbers we have
  const existingNumbers = new Set<number>()

  // Step 1: Enrich existing entries
  console.log('Enriching existing registry entries...')
  for (const entry of registry.problems) {
    const num = extractErdosNumber(entry.slug)
    if (num === null) continue

    existingNumbers.add(num)
    const external = externalByNumber.get(num)
    if (!external) continue

    // Add external metadata
    entry.externalMeta = {
      erdosNumber: num,
      externalStatus: external.status,
      tags: external.tags,
      oeis: external.oeis,
      prize: external.prize,
      leanFilePath: external.leanFilePath,
      leanHasProof: external.leanHasProof,
      erdosUrl: `https://www.erdosproblems.com/${num}`,
      syncedAt: new Date().toISOString(),
    }

    result.enriched++
    if (verbose) {
      console.log(`  Enriched: ${entry.slug}`)
    }
  }
  console.log(`  Enriched ${result.enriched} entries`)

  if (enrichOnly) {
    if (!dryRun) {
      saveRegistry(registry)
      console.log('\nRegistry saved (enrich only mode)')
    }
    return result
  }

  // Step 2: Identify new problems to add
  console.log('\nIdentifying new problems to add...')
  const toAdd: EnrichedProblem[] = []

  for (const p of enrichedProblems) {
    if (existingNumbers.has(p.number)) continue
    if (!p.hasLeanFormalization) continue

    // Determine if we should add this problem
    let shouldAdd = false
    let reason = ''

    if (addGalleryCandidates && p.isGalleryCandidate) {
      shouldAdd = true
      reason = 'gallery candidate'
    } else if (addEasyTargets && p.isProofTarget &&
               p.leanCategories.some(c => c.includes('undergraduate'))) {
      shouldAdd = true
      reason = 'easy target (undergraduate)'
    } else if (addResearchCandidates && p.isResearchCandidate) {
      shouldAdd = true
      reason = 'research candidate'
    }

    if (shouldAdd) {
      toAdd.push(p)
      if (verbose) {
        console.log(`  Will add #${p.number}: ${reason}`)
      }
    }
  }

  // Sort by priority (gallery candidates first, then by number)
  toAdd.sort((a, b) => {
    const aGallery = a.isGalleryCandidate ? 0 : 1
    const bGallery = b.isGalleryCandidate ? 0 : 1
    if (aGallery !== bGallery) return aGallery - bGallery
    return a.number - b.number
  })

  // Limit additions
  const toAddLimited = toAdd.slice(0, maxNewEntries)
  console.log(`  Found ${toAdd.length} candidates, adding ${toAddLimited.length}`)

  // Step 3: Add new entries
  for (const p of toAddLimited) {
    const slug = generateSlug(p)

    // Determine initial phase based on problem characteristics
    let phase = 'NEW'
    let path = 'full'

    if (p.isGalleryCandidate) {
      // Resolved problems - might be faster to formalize
      phase = 'NEW'
      path = 'fast'
    } else if (p.leanCategories.some(c => c.includes('undergraduate'))) {
      phase = 'NEW'
      path = 'fast'
    }

    const newEntry: RegistryEntry = {
      slug,
      phase,
      path,
      started: new Date().toISOString(),
      status: 'active',
      externalMeta: {
        erdosNumber: p.number,
        externalStatus: p.status,
        tags: p.tags,
        oeis: p.oeis,
        prize: p.prize,
        leanFilePath: p.leanFilePath,
        leanHasProof: p.leanHasProof,
        erdosUrl: `https://www.erdosproblems.com/${p.number}`,
        syncedAt: new Date().toISOString(),
      },
    }

    registry.problems.push(newEntry)
    result.added++

    if (verbose) {
      console.log(`  Added: ${slug} (${p.status})`)
    }
  }

  result.skipped = toAdd.length - toAddLimited.length

  // Save
  if (!dryRun) {
    saveRegistry(registry)
    console.log('\nRegistry saved')
  } else {
    console.log('\n[DRY RUN] Would save registry')
  }

  // Summary
  console.log('\n=== Summary ===')
  console.log(`Enriched: ${result.enriched}`)
  console.log(`Added: ${result.added}`)
  console.log(`Skipped (limit): ${result.skipped}`)
  if (result.errors.length > 0) {
    console.log(`Errors: ${result.errors.length}`)
    for (const err of result.errors) {
      console.log(`  - ${err}`)
    }
  }

  return result
}

// CLI entry point
if (import.meta.url === `file://${process.argv[1]}`) {
  const args = process.argv.slice(2)

  const options: SyncOptions = {
    dryRun: args.includes('--dry-run'),
    enrichOnly: args.includes('--enrich-only'),
    addGalleryCandidates: !args.includes('--no-gallery'),
    addEasyTargets: !args.includes('--no-easy'),
    addResearchCandidates: args.includes('--add-research'),
    verbose: args.includes('--verbose') || args.includes('-v'),
  }

  // Parse --max-new N
  const maxIdx = args.indexOf('--max-new')
  if (maxIdx !== -1 && args[maxIdx + 1]) {
    options.maxNewEntries = parseInt(args[maxIdx + 1])
  }

  if (args.includes('--help')) {
    console.log(`
Usage: npx tsx scripts/erdos/registry-sync.ts [options]

Options:
  --dry-run       Preview changes without saving
  --enrich-only   Only update existing entries, don't add new problems
  --no-gallery    Don't add gallery candidates
  --no-easy       Don't add easy undergraduate targets
  --add-research  Also add open research candidates
  --max-new N     Maximum new entries to add (default: 50)
  --verbose, -v   Show detailed output
  --help          Show this help
`)
    process.exit(0)
  }

  syncRegistry(options)
}
