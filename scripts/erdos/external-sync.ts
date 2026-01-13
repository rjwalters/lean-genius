/**
 * Integration tooling for external Erdős problem repositories
 *
 * Syncs data from:
 * - teorth/erdosproblems: Authoritative metadata (status, tags, prize, OEIS)
 * - google-deepmind/formal-conjectures: Lean formalizations
 *
 * Outputs:
 * - Enriched problem data with cross-references
 * - Gallery candidates (proved + formalized)
 * - Research candidates (open + formalized = good proof targets)
 */

import { readFileSync, writeFileSync, existsSync, readdirSync } from 'fs'
import { join, dirname } from 'path'
import { parse as parseYaml } from 'yaml'

const ROOT_DIR = join(dirname(import.meta.url.replace('file://', '')), '../..')
const ERDOS_PROBLEMS_DIR = join(ROOT_DIR, 'external/erdosproblems')
const FORMAL_CONJECTURES_DIR = join(ROOT_DIR, 'external/formal-conjectures')
const OUTPUT_DIR = join(ROOT_DIR, 'scripts/erdos/data')

/**
 * Problem metadata from teorth/erdosproblems
 */
export interface ExternalProblemMeta {
  number: string
  prize?: string
  status: {
    state: 'open' | 'proved' | 'disproved' | 'solved' | 'falsifiable' | 'verifiable' | 'decidable' | 'not provable' | 'not disprovable' | 'independent'
    last_update?: string
  }
  oeis?: string[]
  formalized: {
    state: 'yes' | 'no'
    last_update?: string
  }
  tags?: string[]
  comments?: string
}

/**
 * Lean formalization info
 */
export interface LeanFormalization {
  problemNumber: number
  filePath: string
  hasProof: boolean // true if no `sorry` in file
  theorems: string[]
  categories: string[] // e.g., 'research open', 'research solved', 'undergraduate'
}

/**
 * Combined problem data from all sources
 */
export interface EnrichedProblem {
  number: number
  // From erdosproblems YAML
  status: ExternalProblemMeta['status']['state']
  statusLastUpdate?: string
  prize?: string
  tags: string[]
  oeis: string[]
  comments?: string
  // From formal-conjectures
  hasLeanFormalization: boolean
  leanFilePath?: string
  leanHasProof: boolean
  leanTheorems: string[]
  leanCategories: string[]
  // Computed
  isGalleryCandidate: boolean // proved/solved + formalized
  isResearchCandidate: boolean // open + formalized (good target)
  isProofTarget: boolean // formalized + no proof (has sorry)
}

/**
 * Parse the problems.yaml file from erdosproblems repo
 */
export function parseProblemsYaml(): ExternalProblemMeta[] {
  const yamlPath = join(ERDOS_PROBLEMS_DIR, 'data/problems.yaml')
  if (!existsSync(yamlPath)) {
    throw new Error(`problems.yaml not found at ${yamlPath}. Run: git submodule update --init`)
  }
  const content = readFileSync(yamlPath, 'utf-8')
  return parseYaml(content) as ExternalProblemMeta[]
}

/**
 * Scan formal-conjectures for Erdős problem Lean files
 */
export function scanLeanFormalizations(): Map<number, LeanFormalization> {
  const erdosDir = join(FORMAL_CONJECTURES_DIR, 'FormalConjectures/ErdosProblems')
  if (!existsSync(erdosDir)) {
    throw new Error(`ErdosProblems dir not found at ${erdosDir}. Run: git submodule update --init`)
  }

  const formalizations = new Map<number, LeanFormalization>()

  const files = readdirSync(erdosDir).filter(f => f.endsWith('.lean'))
  for (const file of files) {
    const match = file.match(/^(\d+)\.lean$/)
    if (!match) continue

    const problemNumber = parseInt(match[1])
    const filePath = join(erdosDir, file)
    const content = readFileSync(filePath, 'utf-8')

    // Check for sorry (indicates incomplete proof)
    const hasSorry = /\bsorry\b/.test(content)

    // Extract theorem names
    const theoremMatches = content.matchAll(/theorem\s+([\w.]+)/g)
    const theorems = Array.from(theoremMatches).map(m => m[1])

    // Extract categories from @[category ...] attributes
    const categoryMatches = content.matchAll(/@\[category\s+([^\]]+)\]/g)
    const categories = Array.from(categoryMatches).map(m => m[1].trim())

    formalizations.set(problemNumber, {
      problemNumber,
      filePath: filePath.replace(ROOT_DIR + '/', ''),
      hasProof: !hasSorry,
      theorems,
      categories,
    })
  }

  return formalizations
}

/**
 * Enrich problems by combining all data sources
 */
export function enrichProblems(): EnrichedProblem[] {
  console.log('Parsing problems.yaml...')
  const yamlProblems = parseProblemsYaml()
  console.log(`  Found ${yamlProblems.length} problems`)

  console.log('Scanning Lean formalizations...')
  const leanFormalizations = scanLeanFormalizations()
  console.log(`  Found ${leanFormalizations.size} Lean files`)

  const enriched: EnrichedProblem[] = []

  for (const prob of yamlProblems) {
    const num = parseInt(prob.number)
    const lean = leanFormalizations.get(num)

    const status = prob.status.state
    const hasLean = prob.formalized.state === 'yes'
    const isResolved = ['proved', 'disproved', 'solved'].includes(status)
    const isOpen = status === 'open'

    enriched.push({
      number: num,
      status,
      statusLastUpdate: prob.status.last_update,
      prize: prob.prize !== 'no' ? prob.prize : undefined,
      tags: prob.tags || [],
      oeis: (prob.oeis || []).filter(o => o !== 'N/A' && !['possible', 'submitted', 'in progress'].includes(o)),
      comments: prob.comments,
      hasLeanFormalization: hasLean,
      leanFilePath: lean?.filePath,
      leanHasProof: lean?.hasProof ?? false,
      leanTheorems: lean?.theorems ?? [],
      leanCategories: lean?.categories ?? [],
      // Gallery candidates: resolved problems with Lean formalizations
      isGalleryCandidate: isResolved && hasLean,
      // Research candidates: open problems with Lean formalizations (good targets)
      isResearchCandidate: isOpen && hasLean,
      // Proof targets: has Lean file but proofs are incomplete (sorry)
      isProofTarget: hasLean && lean !== undefined && !lean.hasProof,
    })
  }

  return enriched
}

/**
 * Generate summary statistics
 */
export interface SyncStats {
  totalProblems: number
  proved: number
  disproved: number
  solved: number
  open: number
  other: number
  withPrize: number
  withLeanFormalization: number
  leanWithProof: number
  leanWithSorry: number
  galleryCandidates: number
  researchCandidates: number
  proofTargets: number
  tagDistribution: Record<string, number>
}

export function computeStats(problems: EnrichedProblem[]): SyncStats {
  const stats: SyncStats = {
    totalProblems: problems.length,
    proved: 0,
    disproved: 0,
    solved: 0,
    open: 0,
    other: 0,
    withPrize: 0,
    withLeanFormalization: 0,
    leanWithProof: 0,
    leanWithSorry: 0,
    galleryCandidates: 0,
    researchCandidates: 0,
    proofTargets: 0,
    tagDistribution: {},
  }

  for (const p of problems) {
    // Status counts
    switch (p.status) {
      case 'proved': stats.proved++; break
      case 'disproved': stats.disproved++; break
      case 'solved': stats.solved++; break
      case 'open': stats.open++; break
      default: stats.other++
    }

    if (p.prize) stats.withPrize++
    if (p.hasLeanFormalization) stats.withLeanFormalization++
    if (p.leanHasProof) stats.leanWithProof++
    if (p.hasLeanFormalization && !p.leanHasProof) stats.leanWithSorry++
    if (p.isGalleryCandidate) stats.galleryCandidates++
    if (p.isResearchCandidate) stats.researchCandidates++
    if (p.isProofTarget) stats.proofTargets++

    // Tag distribution
    for (const tag of p.tags) {
      stats.tagDistribution[tag] = (stats.tagDistribution[tag] || 0) + 1
    }
  }

  return stats
}

/**
 * Export gallery candidates for proof annotation
 */
export interface GalleryCandidate {
  number: number
  status: string
  prize?: string
  tags: string[]
  leanFile: string
  theorems: string[]
  oeis: string[]
  erdosUrl: string
}

export function getGalleryCandidates(problems: EnrichedProblem[]): GalleryCandidate[] {
  return problems
    .filter(p => p.isGalleryCandidate && p.leanFilePath)
    .map(p => ({
      number: p.number,
      status: p.status,
      prize: p.prize,
      tags: p.tags,
      leanFile: p.leanFilePath!,
      theorems: p.leanTheorems,
      oeis: p.oeis,
      erdosUrl: `https://www.erdosproblems.com/${p.number}`,
    }))
    .sort((a, b) => a.number - b.number)
}

/**
 * Export proof targets (formalized but not proved)
 */
export interface ProofTarget {
  number: number
  status: string
  prize?: string
  tags: string[]
  leanFile: string
  theorems: string[]
  categories: string[]
  difficulty: 'undergraduate' | 'research' | 'unknown'
  erdosUrl: string
}

export function getProofTargets(problems: EnrichedProblem[]): ProofTarget[] {
  return problems
    .filter(p => p.isProofTarget && p.leanFilePath)
    .map(p => {
      // Determine difficulty from Lean categories
      let difficulty: ProofTarget['difficulty'] = 'unknown'
      if (p.leanCategories.some(c => c.includes('undergraduate'))) {
        difficulty = 'undergraduate'
      } else if (p.leanCategories.some(c => c.includes('research'))) {
        difficulty = 'research'
      }

      return {
        number: p.number,
        status: p.status,
        prize: p.prize,
        tags: p.tags,
        leanFile: p.leanFilePath!,
        theorems: p.leanTheorems,
        categories: p.leanCategories,
        difficulty,
        erdosUrl: `https://www.erdosproblems.com/${p.number}`,
      }
    })
    .sort((a, b) => {
      // Sort by difficulty (undergraduate first), then by number
      const diffOrder = { undergraduate: 0, research: 1, unknown: 2 }
      const diffDelta = diffOrder[a.difficulty] - diffOrder[b.difficulty]
      return diffDelta !== 0 ? diffDelta : a.number - b.number
    })
}

/**
 * Main sync function
 */
export async function sync(options: { dryRun?: boolean; verbose?: boolean } = {}): Promise<{
  stats: SyncStats
  galleryCandidates: GalleryCandidate[]
  proofTargets: ProofTarget[]
}> {
  const { dryRun = false, verbose = false } = options

  console.log('=== External Erdős Data Sync ===\n')

  // Enrich all problems
  const problems = enrichProblems()

  // Compute statistics
  const stats = computeStats(problems)

  console.log('\n=== Statistics ===')
  console.log(`Total problems: ${stats.totalProblems}`)
  console.log(`Status breakdown:`)
  console.log(`  - Proved: ${stats.proved}`)
  console.log(`  - Disproved: ${stats.disproved}`)
  console.log(`  - Solved: ${stats.solved}`)
  console.log(`  - Open: ${stats.open}`)
  console.log(`  - Other: ${stats.other}`)
  console.log(`With prize: ${stats.withPrize}`)
  console.log(`With Lean formalization: ${stats.withLeanFormalization}`)
  console.log(`  - With complete proof: ${stats.leanWithProof}`)
  console.log(`  - With sorry (incomplete): ${stats.leanWithSorry}`)
  console.log(`Gallery candidates (resolved + Lean): ${stats.galleryCandidates}`)
  console.log(`Research candidates (open + Lean): ${stats.researchCandidates}`)
  console.log(`Proof targets (Lean + sorry): ${stats.proofTargets}`)

  // Get candidates
  const galleryCandidates = getGalleryCandidates(problems)
  const proofTargets = getProofTargets(problems)

  if (verbose) {
    console.log('\n=== Top Tags ===')
    const sortedTags = Object.entries(stats.tagDistribution)
      .sort(([, a], [, b]) => b - a)
      .slice(0, 15)
    for (const [tag, count] of sortedTags) {
      console.log(`  ${tag}: ${count}`)
    }

    console.log('\n=== Gallery Candidates (first 20) ===')
    for (const c of galleryCandidates.slice(0, 20)) {
      console.log(`  #${c.number} [${c.status}] ${c.tags.slice(0, 3).join(', ')}`)
    }

    console.log('\n=== Proof Targets by Difficulty ===')
    const undergrad = proofTargets.filter(p => p.difficulty === 'undergraduate')
    const research = proofTargets.filter(p => p.difficulty === 'research')
    console.log(`  Undergraduate: ${undergrad.length}`)
    for (const t of undergrad.slice(0, 10)) {
      console.log(`    #${t.number} - ${t.theorems[0] || 'unnamed'}`)
    }
    console.log(`  Research: ${research.length}`)
  }

  // Write output files
  if (!dryRun) {
    const { mkdirSync } = await import('fs')
    mkdirSync(OUTPUT_DIR, { recursive: true })

    // Write enriched data
    writeFileSync(
      join(OUTPUT_DIR, 'enriched-problems.json'),
      JSON.stringify(problems, null, 2)
    )
    console.log(`\nWrote ${problems.length} enriched problems to data/enriched-problems.json`)

    // Write gallery candidates
    writeFileSync(
      join(OUTPUT_DIR, 'gallery-candidates.json'),
      JSON.stringify(galleryCandidates, null, 2)
    )
    console.log(`Wrote ${galleryCandidates.length} gallery candidates to data/gallery-candidates.json`)

    // Write proof targets
    writeFileSync(
      join(OUTPUT_DIR, 'proof-targets.json'),
      JSON.stringify(proofTargets, null, 2)
    )
    console.log(`Wrote ${proofTargets.length} proof targets to data/proof-targets.json`)

    // Write stats
    writeFileSync(
      join(OUTPUT_DIR, 'sync-stats.json'),
      JSON.stringify(stats, null, 2)
    )
    console.log(`Wrote statistics to data/sync-stats.json`)
  } else {
    console.log('\n[DRY RUN] Would write files to scripts/erdos/data/')
  }

  return { stats, galleryCandidates, proofTargets }
}

// CLI entry point
if (import.meta.url === `file://${process.argv[1]}`) {
  const args = process.argv.slice(2)
  const dryRun = args.includes('--dry-run')
  const verbose = args.includes('--verbose') || args.includes('-v')

  sync({ dryRun, verbose }).catch(err => {
    console.error('Sync failed:', err)
    process.exit(1)
  })
}
