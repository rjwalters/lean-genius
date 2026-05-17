#!/usr/bin/env npx tsx
/**
 * Research Data Enrichment Script
 *
 * Enriches committed research problem JSON files with:
 * 1. leanFiles - metadata about associated Lean 4 formalization files
 * 2. relatedProofs - links to gallery proofs (auto-detected)
 *
 * This script is designed to run AFTER research:build in the build pipeline.
 * It modifies JSON on disk during build only (deploy does `git checkout -- .`).
 *
 * Run: npx tsx scripts/research/enrich-research.ts
 */

import * as fs from 'fs'
import * as path from 'path'
import { fileURLToPath } from 'url'

const __filename = fileURLToPath(import.meta.url)
const __dirname = path.dirname(__filename)

const PROJECT_ROOT = path.join(__dirname, '../..')
const PROOFS_DIR = path.join(PROJECT_ROOT, 'proofs/Proofs')
const PROBLEMS_DIR = path.join(PROJECT_ROOT, 'src/data/research/problems')
const GALLERY_DIR = path.join(PROJECT_ROOT, 'src/data/proofs')
const GITHUB_BASE = 'https://github.com/rjwalters/lean-genius/blob/main/proofs'

// --- Types ---

interface LeanFileInfo {
  path: string
  filename: string
  lineCount: number
  theoremCount: number
  axiomCount: number
  defCount: number
  sorryCount: number
  isAristotle: boolean
  githubUrl: string
}

interface GalleryMeta {
  slug: string
  meta?: {
    millenniumProblem?: string
    proofRepoPath?: string
  }
}

// --- Slug-to-PascalCase Conversion ---

/**
 * Common suffixes to strip from research slugs before PascalCase conversion.
 * These suffixes don't typically appear in Lean file names.
 */
const STRIP_SUFFIXES = ['-existence', '-uniqueness', '-completeness']

/**
 * Special cases where slug-to-PascalCase conversion is non-trivial.
 * Maps research slug to array of PascalCase prefixes to search for.
 */
const SPECIAL_CASES: Record<string, string[]> = {
  'p-vs-np': ['PvsNP', 'PNP'],
  'pnp-barriers': ['PNPBarriers'],
}

/**
 * Convert a kebab-case slug to PascalCase.
 * "riemann-hypothesis" -> "RiemannHypothesis"
 * "erdos-ko-rado" -> "ErdosKoRado"
 */
function slugToPascalCase(slug: string): string {
  return slug
    .split('-')
    .map(part => part.charAt(0).toUpperCase() + part.slice(1))
    .join('')
}

/**
 * Generate all PascalCase prefixes for a research slug.
 * Handles -oq-NN suffixes and common suffixes like -existence.
 */
function getPascalCasePrefixes(slug: string): string[] {
  // Check special cases first
  if (SPECIAL_CASES[slug]) {
    return SPECIAL_CASES[slug]
  }

  const prefixes: string[] = []

  // Full slug as PascalCase
  prefixes.push(slugToPascalCase(slug))

  // Strip -oq-NN suffixes (can be chained: -oq-01-oq-02)
  const baseSlug = slug.replace(/(-oq-\d+)+$/, '')
  if (baseSlug !== slug) {
    prefixes.push(slugToPascalCase(baseSlug))
  }

  // Strip common suffixes
  for (const suffix of STRIP_SUFFIXES) {
    if (slug.endsWith(suffix)) {
      const stripped = slug.slice(0, -suffix.length)
      prefixes.push(slugToPascalCase(stripped))
      // Also strip -oq-NN from the suffix-stripped version
      const strippedBase = stripped.replace(/(-oq-\d+)+$/, '')
      if (strippedBase !== stripped) {
        prefixes.push(slugToPascalCase(strippedBase))
      }
    }
  }

  // Deduplicate
  return [...new Set(prefixes)]
}

// --- Part 1: Lean File Scanning ---

/**
 * Scan all .lean files and build a map of filename -> file path.
 */
function scanLeanFiles(): Map<string, string> {
  const fileMap = new Map<string, string>()

  if (!fs.existsSync(PROOFS_DIR)) {
    console.warn('  Warning: proofs/Proofs directory not found')
    return fileMap
  }

  const files = fs.readdirSync(PROOFS_DIR)
    .filter(f => f.endsWith('.lean') && !f.endsWith('.lean.bak'))

  for (const filename of files) {
    fileMap.set(filename, path.join(PROOFS_DIR, filename))
  }

  return fileMap
}

/**
 * Extract metadata from a Lean file.
 */
function extractLeanMetadata(filePath: string): LeanFileInfo {
  const content = fs.readFileSync(filePath, 'utf-8')
  const lines = content.split('\n')
  const filename = path.basename(filePath)
  const relativePath = `Proofs/${filename}`

  let theoremCount = 0
  let axiomCount = 0
  let defCount = 0
  let sorryCount = 0

  for (const line of lines) {
    if (/^(theorem|lemma) /.test(line)) {
      theoremCount++
    }
    if (/^axiom /.test(line)) {
      axiomCount++
    }
    if (/^(def|noncomputable def|opaque def) /.test(line)) {
      defCount++
    }
    // Count `sorry` as word boundary match
    const sorryMatches = line.match(/\bsorry\b/g)
    if (sorryMatches) {
      sorryCount += sorryMatches.length
    }
  }

  return {
    path: relativePath,
    filename,
    lineCount: lines.length,
    theoremCount,
    axiomCount,
    defCount,
    sorryCount,
    isAristotle: filename.includes('Aristotle'),
    githubUrl: `${GITHUB_BASE}/${relativePath}`,
  }
}

/**
 * Find Lean files matching a research problem slug.
 */
function findLeanFilesForSlug(
  slug: string,
  leanFiles: Map<string, string>
): LeanFileInfo[] {
  const prefixes = getPascalCasePrefixes(slug)
  const matched: LeanFileInfo[] = []
  const seen = new Set<string>()

  for (const [filename, filePath] of leanFiles) {
    const baseName = filename.replace('.lean', '')
    for (const prefix of prefixes) {
      if (baseName.startsWith(prefix) && !seen.has(filename)) {
        seen.add(filename)
        matched.push(extractLeanMetadata(filePath))
      }
    }
  }

  // Sort by filename for deterministic output
  matched.sort((a, b) => a.filename.localeCompare(b.filename))

  return matched
}

// --- Part 2: Related Proofs Auto-Detection ---

/**
 * Load gallery proof metadata from all meta.json files.
 */
function loadGalleryProofs(): GalleryMeta[] {
  const proofs: GalleryMeta[] = []

  if (!fs.existsSync(GALLERY_DIR)) {
    console.warn('  Warning: src/data/proofs directory not found')
    return proofs
  }

  const dirs = fs.readdirSync(GALLERY_DIR).filter(d => {
    const dirPath = path.join(GALLERY_DIR, d)
    return fs.statSync(dirPath).isDirectory()
  })

  for (const dir of dirs) {
    const metaPath = path.join(GALLERY_DIR, dir, 'meta.json')
    if (!fs.existsSync(metaPath)) continue

    try {
      const content = fs.readFileSync(metaPath, 'utf-8')
      const meta = JSON.parse(content)
      proofs.push({
        slug: meta.slug || meta.id || dir,
        meta: meta.meta || {},
      })
    } catch {
      // Skip malformed meta.json
    }
  }

  return proofs
}

/**
 * Build a map from millenniumProblem values to research slugs.
 * millenniumProblem values are short codes like "p-vs-np", "riemann", "hodge".
 */
const MILLENNIUM_SLUG_MAP: Record<string, string> = {
  'p-vs-np': 'p-vs-np',
  'riemann': 'riemann-hypothesis',
  'navier-stokes': 'navier-stokes-existence',
  'hodge': 'hodge-conjecture',
  'poincare': 'poincare-conjecture',
  'bsd': 'birch-swinnerton-dyer',
  'yang-mills': 'yang-mills-mass-gap',
}

/**
 * Find related gallery proofs for a research problem.
 */
function findRelatedProofs(
  slug: string,
  leanFiles: LeanFileInfo[],
  galleryProofs: GalleryMeta[]
): string[] {
  const related = new Set<string>()

  const leanPaths = new Set(leanFiles.map(f => f.path))

  for (const proof of galleryProofs) {
    // Match 1: millenniumProblem field maps to research slug
    if (proof.meta?.millenniumProblem) {
      const mappedSlug = MILLENNIUM_SLUG_MAP[proof.meta.millenniumProblem]
      if (mappedSlug === slug) {
        related.add(proof.slug)
        continue
      }
    }

    // Match 2: Slug match (gallery slug matches or is contained in research slug, or vice versa)
    if (proof.slug === slug || slug.startsWith(proof.slug) || proof.slug.startsWith(slug)) {
      related.add(proof.slug)
      continue
    }

    // Match 3: proofRepoPath matches one of the research problem's leanFiles paths
    if (proof.meta?.proofRepoPath && leanPaths.has(proof.meta.proofRepoPath)) {
      related.add(proof.slug)
      continue
    }
  }

  return [...related].sort()
}

// --- Part 3: Write Enriched Data ---

interface ResearchProblemJson {
  slug: string
  leanFiles?: LeanFileInfo[]
  relatedProofs?: string[]
  [key: string]: unknown
}

/**
 * Enrich a single research problem JSON file.
 * Returns true if the file was modified.
 */
function enrichProblem(
  jsonPath: string,
  leanFiles: LeanFileInfo[],
  relatedProofs: string[],
  dryRun = false
): boolean {
  if (leanFiles.length === 0 && relatedProofs.length === 0) {
    return false
  }

  const content = fs.readFileSync(jsonPath, 'utf-8').trim()
  if (!content) {
    // Skip empty files
    return false
  }

  let problem: ResearchProblemJson
  try {
    problem = JSON.parse(content)
  } catch {
    console.warn(`  Warning: Skipping malformed JSON: ${path.basename(jsonPath)}`)
    return false
  }

  let modified = false

  // Add/update leanFiles
  if (leanFiles.length > 0) {
    problem.leanFiles = leanFiles
    modified = true
  }

  // Merge relatedProofs (combine with existing, deduplicate)
  if (relatedProofs.length > 0) {
    const existing = Array.isArray(problem.relatedProofs) ? problem.relatedProofs : []
    const merged = [...new Set([...existing, ...relatedProofs])].sort()
    if (JSON.stringify(merged) !== JSON.stringify(existing)) {
      problem.relatedProofs = merged
      modified = true
    }
  }

  if (modified && !dryRun) {
    fs.writeFileSync(jsonPath, JSON.stringify(problem, null, 2) + '\n')
  }

  return modified
}

// --- Main ---

function printUsage(): void {
  console.log(`Usage: npx tsx scripts/research/enrich-research.ts [options]

Enrich built research problem JSON with Lean file metadata and related proofs.

Options:
  --dry-run       Report enrichments without writing JSON files
  --help, -h      Show this help message`)
}

function main(options: { dryRun?: boolean } = {}): void {
  const { dryRun = false } = options

  console.log(
    dryRun
      ? 'Enriching research data with Lean file metadata (dry run)...\n'
      : 'Enriching research data with Lean file metadata...\n'
  )

  // Step 1: Scan Lean files
  const leanFileMap = scanLeanFiles()
  console.log(`  Found ${leanFileMap.size} Lean files in proofs/Proofs/`)

  // Step 2: Load gallery proofs
  const galleryProofs = loadGalleryProofs()
  console.log(`  Found ${galleryProofs.length} gallery proof entries`)

  // Step 3: Process each research problem JSON
  if (!fs.existsSync(PROBLEMS_DIR)) {
    console.error('Error: src/data/research/problems/ not found')
    process.exit(1)
  }

  const jsonFiles = fs.readdirSync(PROBLEMS_DIR)
    .filter(f => f.endsWith('.json'))

  let enrichedCount = 0
  let totalLeanFiles = 0
  let totalRelatedProofs = 0

  for (const jsonFile of jsonFiles) {
    const slug = jsonFile.replace('.json', '')
    const jsonPath = path.join(PROBLEMS_DIR, jsonFile)

    // Find matching Lean files
    const matchedLeanFiles = findLeanFilesForSlug(slug, leanFileMap)

    // Find related gallery proofs
    const relatedProofs = findRelatedProofs(slug, matchedLeanFiles, galleryProofs)

    // Enrich the JSON file
    const wasEnriched = enrichProblem(jsonPath, matchedLeanFiles, relatedProofs, dryRun)

    if (wasEnriched) {
      enrichedCount++
      totalLeanFiles += matchedLeanFiles.length
      totalRelatedProofs += relatedProofs.length
      if (matchedLeanFiles.length > 0 || relatedProofs.length > 0) {
        console.log(
          `  Enriched ${slug}: ${matchedLeanFiles.length} lean files, ${relatedProofs.length} related proofs`
        )
      }
    }
  }

  console.log(`\nEnrichment summary:`)
  console.log(`  Problems enriched: ${enrichedCount}/${jsonFiles.length}`)
  console.log(`  Total Lean files linked: ${totalLeanFiles}`)
  console.log(`  Total related proofs linked: ${totalRelatedProofs}`)
  if (dryRun) {
    console.log('  No files written')
  }
}

if (process.argv[1] && import.meta.url === `file://${process.argv[1]}`) {
  const args = process.argv.slice(2)

  if (args.includes('--help') || args.includes('-h')) {
    printUsage()
    process.exit(0)
  }

  main({ dryRun: args.includes('--dry-run') })
}
