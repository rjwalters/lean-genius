/**
 * Cross-reference tool: Compare external Erdős data with our research registry
 *
 * Identifies:
 * - Problems we're tracking that have external Lean formalizations
 * - Problems we're missing that could be easy wins
 * - Status mismatches between sources
 */

import { readFileSync, existsSync, readdirSync, writeFileSync, mkdirSync } from 'fs'
import { join, dirname } from 'path'
import { enrichProblems, type EnrichedProblem } from './external-sync'

const ROOT_DIR = join(dirname(import.meta.url.replace('file://', '')), '../..')
const REGISTRY_PATH = join(ROOT_DIR, 'research/registry.json')
const PROOFS_DIR = join(ROOT_DIR, 'proofs/Proofs')
const GALLERY_DIR = join(ROOT_DIR, 'src/data/proofs')

interface RegistryEntry {
  slug: string
  phase: string
  path: string
  started: string
  status: string
  completed?: string
  lastUpdate?: string
}

interface Registry {
  version: string
  problems: RegistryEntry[]
  config: object
}

interface CrossRefResult {
  erdosNumber: number
  slug?: string
  inRegistry: boolean
  registryStatus?: string
  registryPhase?: string
  hasProofFile: boolean
  proofFilePath?: string
  hasGalleryEntry: boolean
  galleryPath?: string
  externalStatus: string
  hasLeanFormalization: boolean
  leanFilePath?: string
  leanHasProof: boolean
  statusMatch: boolean
  recommendation: 'keep' | 'update' | 'add' | 'skip'
  recommendationReason: string
}

/**
 * Load our research registry
 */
function loadRegistry(): Registry {
  if (!existsSync(REGISTRY_PATH)) {
    throw new Error(`Registry not found at ${REGISTRY_PATH}`)
  }
  return JSON.parse(readFileSync(REGISTRY_PATH, 'utf-8'))
}

/**
 * Extract Erdős problem number from a slug
 */
function extractErdosNumber(slug: string): number | null {
  // Match patterns like "erdos-123", "erdos-123-description"
  const match = slug.match(/^erdos-(\d+)(?:-|$)/)
  return match ? parseInt(match[1]) : null
}

/**
 * Check if a proof file exists for a problem number
 */
function findProofFile(num: number): string | null {
  try {
    const files = readdirSync(PROOFS_DIR)
    // Look for Erdos{N}*.lean files
    const match = files.find((f: string) =>
      f.startsWith(`Erdos${num}`) && f.endsWith('.lean')
    )
    return match ? join(PROOFS_DIR, match) : null
  } catch {
    return null
  }
}

/**
 * Check if a gallery entry exists for a problem number
 */
function findGalleryEntry(num: number): string | null {
  try {
    const dirs = readdirSync(GALLERY_DIR)
    // Look for erdos-{N}* directories
    const match = dirs.find((d: string) =>
      d.startsWith(`erdos-${num}`) || d === `erdos-${num}`
    )
    return match ? join(GALLERY_DIR, match) : null
  } catch {
    return null
  }
}

/**
 * Cross-reference all data sources
 */
export function crossReference(): CrossRefResult[] {
  console.log('Loading data sources...')

  const registry = loadRegistry()
  const enrichedProblems = enrichProblems()

  // Build map of our registry entries by Erdős number
  const registryByNumber = new Map<number, RegistryEntry>()
  for (const entry of registry.problems) {
    const num = extractErdosNumber(entry.slug)
    if (num !== null) {
      registryByNumber.set(num, entry)
    }
  }

  console.log(`Registry has ${registryByNumber.size} Erdős problems`)
  console.log(`External data has ${enrichedProblems.length} problems`)

  const results: CrossRefResult[] = []

  // Process all external problems
  for (const ext of enrichedProblems) {
    const num = ext.number
    const regEntry = registryByNumber.get(num)
    const proofFile = findProofFile(num)
    const galleryEntry = findGalleryEntry(num)

    // Determine status match
    const externalResolved = ['proved', 'disproved', 'solved'].includes(ext.status)
    const registryResolved = regEntry?.status === 'graduated'
    const statusMatch = (externalResolved === registryResolved) || !regEntry

    // Determine recommendation
    let recommendation: CrossRefResult['recommendation'] = 'skip'
    let recommendationReason = ''

    if (regEntry) {
      if (ext.hasLeanFormalization && !proofFile) {
        recommendation = 'update'
        recommendationReason = 'Has external Lean formalization, consider importing'
      } else if (!statusMatch) {
        recommendation = 'update'
        recommendationReason = `Status mismatch: registry=${regEntry.status}, external=${ext.status}`
      } else {
        recommendation = 'keep'
        recommendationReason = 'Already tracked, status matches'
      }
    } else {
      // Not in our registry
      if (ext.isGalleryCandidate) {
        recommendation = 'add'
        recommendationReason = 'Gallery candidate: resolved + has Lean formalization'
      } else if (ext.isProofTarget && ext.leanCategories.some(c => c.includes('undergraduate'))) {
        recommendation = 'add'
        recommendationReason = 'Easy proof target: has Lean statement, marked undergraduate'
      } else if (ext.hasLeanFormalization && ext.status === 'open') {
        recommendation = 'add'
        recommendationReason = 'Research candidate: open problem with Lean formalization'
      } else {
        recommendation = 'skip'
        recommendationReason = ext.hasLeanFormalization
          ? 'Has Lean but no clear advantage'
          : 'No Lean formalization available'
      }
    }

    results.push({
      erdosNumber: num,
      slug: regEntry?.slug,
      inRegistry: !!regEntry,
      registryStatus: regEntry?.status,
      registryPhase: regEntry?.phase,
      hasProofFile: !!proofFile,
      proofFilePath: proofFile?.replace(ROOT_DIR + '/', '') || undefined,
      hasGalleryEntry: !!galleryEntry,
      galleryPath: galleryEntry?.replace(ROOT_DIR + '/', '') || undefined,
      externalStatus: ext.status,
      hasLeanFormalization: ext.hasLeanFormalization,
      leanFilePath: ext.leanFilePath,
      leanHasProof: ext.leanHasProof,
      statusMatch,
      recommendation,
      recommendationReason,
    })
  }

  return results
}

/**
 * Generate summary report
 */
export function generateReport(results: CrossRefResult[]): string {
  const lines: string[] = []

  lines.push('# Erdős Problems Cross-Reference Report\n')

  // Summary stats
  const inRegistry = results.filter(r => r.inRegistry).length
  const hasLean = results.filter(r => r.hasLeanFormalization).length
  const inBoth = results.filter(r => r.inRegistry && r.hasLeanFormalization).length
  const toAdd = results.filter(r => r.recommendation === 'add')
  const toUpdate = results.filter(r => r.recommendation === 'update')

  lines.push('## Summary\n')
  lines.push(`- Total external problems: ${results.length}`)
  lines.push(`- In our registry: ${inRegistry}`)
  lines.push(`- With Lean formalization: ${hasLean}`)
  lines.push(`- In both (overlap): ${inBoth}`)
  lines.push(`- Recommended to add: ${toAdd.length}`)
  lines.push(`- Recommended to update: ${toUpdate.length}`)
  lines.push('')

  // Gallery opportunities
  const galleryCandidates = toAdd.filter(r =>
    r.recommendationReason.includes('Gallery candidate')
  )
  if (galleryCandidates.length > 0) {
    lines.push('## Gallery Candidates (Proved + Lean)\n')
    lines.push('These resolved problems have Lean formalizations ready for annotated gallery proofs:\n')
    for (const c of galleryCandidates.slice(0, 30)) {
      lines.push(`- **#${c.erdosNumber}** [${c.externalStatus}] - ${c.leanFilePath}`)
    }
    if (galleryCandidates.length > 30) {
      lines.push(`- ... and ${galleryCandidates.length - 30} more`)
    }
    lines.push('')
  }

  // Easy proof targets
  const easyTargets = toAdd.filter(r =>
    r.recommendationReason.includes('undergraduate')
  )
  if (easyTargets.length > 0) {
    lines.push('## Easy Proof Targets (Undergraduate Level)\n')
    lines.push('These have Lean statements marked as undergraduate difficulty:\n')
    for (const t of easyTargets.slice(0, 20)) {
      lines.push(`- **#${t.erdosNumber}** [${t.externalStatus}] - ${t.leanFilePath}`)
    }
    if (easyTargets.length > 20) {
      lines.push(`- ... and ${easyTargets.length - 20} more`)
    }
    lines.push('')
  }

  // Research candidates
  const researchCandidates = toAdd.filter(r =>
    r.recommendationReason.includes('Research candidate')
  )
  if (researchCandidates.length > 0) {
    lines.push('## Research Candidates (Open + Lean)\n')
    lines.push('Open problems with Lean formalizations - good proof targets:\n')
    for (const r of researchCandidates.slice(0, 30)) {
      lines.push(`- **#${r.erdosNumber}** - ${r.leanFilePath}`)
    }
    if (researchCandidates.length > 30) {
      lines.push(`- ... and ${researchCandidates.length - 30} more`)
    }
    lines.push('')
  }

  // Updates needed
  if (toUpdate.length > 0) {
    lines.push('## Registry Updates Needed\n')
    for (const u of toUpdate) {
      lines.push(`- **#${u.erdosNumber}** (${u.slug}): ${u.recommendationReason}`)
    }
    lines.push('')
  }

  // Coverage analysis
  lines.push('## Coverage Analysis\n')
  const coverage = (inBoth / hasLean * 100).toFixed(1)
  lines.push(`We're tracking ${inBoth}/${hasLean} (${coverage}%) of problems with Lean formalizations.\n`)

  // Status distribution of what we're missing
  const missing = results.filter(r => !r.inRegistry && r.hasLeanFormalization)
  const missingByStatus: Record<string, number> = {}
  for (const m of missing) {
    missingByStatus[m.externalStatus] = (missingByStatus[m.externalStatus] || 0) + 1
  }
  lines.push('Missing problems by status:')
  for (const [status, count] of Object.entries(missingByStatus).sort((a, b) => b[1] - a[1])) {
    lines.push(`- ${status}: ${count}`)
  }

  return lines.join('\n')
}

// CLI entry point
if (import.meta.url === `file://${process.argv[1]}`) {
  const args = process.argv.slice(2)
  const outputJson = args.includes('--json')
  const outputReport = args.includes('--report')

  try {
    const results = crossReference()

    if (outputJson) {
      console.log(JSON.stringify(results, null, 2))
    } else if (outputReport) {
      console.log(generateReport(results))
    } else {
      // Default: show summary
      const report = generateReport(results)
      console.log(report)

      // Also save to file
      const outputDir = join(ROOT_DIR, 'scripts/erdos/data')
      mkdirSync(outputDir, { recursive: true })
      writeFileSync(join(outputDir, 'cross-reference.json'), JSON.stringify(results, null, 2))
      writeFileSync(join(outputDir, 'cross-reference-report.md'), report)
      console.log('\nSaved to scripts/erdos/data/cross-reference.json and cross-reference-report.md')
    }
  } catch (err) {
    console.error('Cross-reference failed:', err)
    process.exit(1)
  }
}
