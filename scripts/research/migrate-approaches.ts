#!/usr/bin/env npx tsx
/**
 * Migrate approaches data from problem JSON files into knowledge.md,
 * then remove the approaches field from each JSON.
 *
 * This is a one-time migration script. The Approaches tab is being removed
 * from the frontend because only 18 of 521 problems use it, and researchers
 * document their work in knowledge.md sessions instead.
 *
 * Run: npx tsx scripts/research/migrate-approaches.ts [--dry-run]
 */

import * as fs from 'fs'
import * as path from 'path'
import { fileURLToPath } from 'url'

const __filename = fileURLToPath(import.meta.url)
const __dirname = path.dirname(__filename)

const PROBLEMS_JSON_DIR = path.join(__dirname, '../../src/data/research/problems')
const RESEARCH_PROBLEMS_DIR = path.join(__dirname, '../../research/problems')

// The 18 problems that have approaches data
const SLUGS = [
  'cube-root-3-irrational',
  'dissection-of-cubes-oq-03',
  'euler-totient-oq-04',
  'angle-trisection-oq-04',
  'cube-root-2-irrational',
  'friendship-theorem-oq-01',
  'divisibility-truncation-general-oq-01',
  'sqrt2-plus-sqrt3-irrational',
  'area-of-circle-oq-03-oq-01',
  'weak-goldbach',
  'hurwitz-three-square-impossibility',
  'elementary-quadratic-reciprocity-oq-02',
  'combinations-formula-oq-03',
  'binomial-theorem-oq-04-oq-01',
  'cayley-hamilton-minpoly-oq-04',
  'ballot-problem-oq-01-oq-02',
  'pythagorean-triples-oq-01',
  'gcd-algorithm-oq-01-oq-03',
]

interface Approach {
  id?: string
  name: string
  status: string
  description?: string
  hypothesis?: string
  strategy?: string
  outcome?: string
  risks?: string[]
  attempts?: { file: string; succeeded: boolean }[] | number
  postMortem?: {
    whatWorked: string[]
    whatFailed: string[]
    lessonsLearned: string[]
  }
  successRecap?: {
    keyTheorem: string
    techniquesUsed: string[]
    linesOfProof?: number
    timeToSuccess?: string
  }
}

interface ProblemJson {
  approaches?: Approach[]
  [key: string]: unknown
}

interface MigrateOptions {
  dryRun?: boolean
}

function printUsage(): void {
  console.log(`Usage: npx tsx scripts/research/migrate-approaches.ts [options]

Migrate approaches data from research problem JSON files into knowledge.md.

Options:
  --dry-run   Report the migration actions without writing files
  -h, --help  Show this help message`)
}

function formatApproachesMarkdown(approaches: Approach[]): string {
  const lines: string[] = ['', '## Approaches Explored', '']

  for (const approach of approaches) {
    lines.push(`### ${approach.name}`)
    lines.push(`**Status**: ${approach.status}`)

    if (approach.description) {
      lines.push(approach.description)
    }

    if (approach.outcome) {
      lines.push(`**Outcome**: ${approach.outcome}`)
    }

    if (approach.strategy) {
      lines.push(`**Strategy**: ${approach.strategy}`)
    }

    if (approach.hypothesis) {
      lines.push(`**Hypothesis**: ${approach.hypothesis}`)
    }

    lines.push('')
  }

  return lines.join('\n')
}

function isPlaceholderApproach(approach: Approach): boolean {
  // Skip placeholder approaches that have no meaningful content
  const name = approach.name || ''
  if (name === 'approach-01' || name === 'Hypothesis: [Approach Name]') {
    // Check if there's any real content beyond the placeholder name
    if (!approach.description && !approach.outcome && !approach.strategy) {
      return true
    }
  }
  return false
}

function migrate(options: MigrateOptions = {}): void {
  const { dryRun = false } = options

  console.log(`Migrating approaches data to knowledge.md${dryRun ? ' (dry run)' : ''}...\n`)

  let migratedCount = 0
  let skippedCount = 0

  for (const slug of SLUGS) {
    const jsonPath = path.join(PROBLEMS_JSON_DIR, `${slug}.json`)

    if (!fs.existsSync(jsonPath)) {
      console.log(`  SKIP: ${slug} - JSON file not found`)
      skippedCount++
      continue
    }

    const jsonData: ProblemJson = JSON.parse(fs.readFileSync(jsonPath, 'utf-8'))
    const approaches: Approach[] = jsonData.approaches || []

    if (approaches.length === 0) {
      console.log(`  SKIP: ${slug} - no approaches`)
      skippedCount++
      continue
    }

    // Filter out placeholder approaches with no real content
    const meaningfulApproaches = approaches.filter(a => !isPlaceholderApproach(a))

    if (meaningfulApproaches.length === 0) {
      if (dryRun) {
        console.log(`  SKIP (placeholder): ${slug} - only placeholder approaches, would remove from JSON`)
      } else {
        console.log(`  SKIP (placeholder): ${slug} - only placeholder approaches, removing from JSON`)
        // Still remove approaches from JSON
        delete jsonData.approaches
        fs.writeFileSync(jsonPath, JSON.stringify(jsonData, null, 2) + '\n')
      }
      skippedCount++
      continue
    }

    // Format the markdown section
    const approachesMarkdown = formatApproachesMarkdown(meaningfulApproaches)

    // Find or create knowledge.md
    const knowledgeMdPath = path.join(RESEARCH_PROBLEMS_DIR, slug, 'knowledge.md')
    const problemDir = path.join(RESEARCH_PROBLEMS_DIR, slug)

    // Ensure the problem directory exists
    if (!fs.existsSync(problemDir)) {
      if (dryRun) {
        console.log(`  WOULD CREATE DIRECTORY: ${problemDir}`)
      } else {
        fs.mkdirSync(problemDir, { recursive: true })
        console.log(`  Created directory: ${problemDir}`)
      }
    }

    if (fs.existsSync(knowledgeMdPath)) {
      // Append to existing knowledge.md
      const existing = fs.readFileSync(knowledgeMdPath, 'utf-8')
      // Only append if not already migrated
      if (!existing.includes('## Approaches Explored')) {
        if (dryRun) {
          console.log(`  WOULD APPEND: ${slug} (${meaningfulApproaches.length} approach(es))`)
        } else {
          fs.writeFileSync(knowledgeMdPath, existing.trimEnd() + '\n' + approachesMarkdown)
          console.log(`  APPENDED: ${slug} (${meaningfulApproaches.length} approach(es))`)
        }
      } else {
        console.log(`  ALREADY MIGRATED: ${slug}`)
      }
    } else {
      // Create new knowledge.md with approaches section
      const header = `# Knowledge Base: ${slug}\n`
      if (dryRun) {
        console.log(`  WOULD CREATE: ${slug} knowledge.md (${meaningfulApproaches.length} approach(es))`)
      } else {
        fs.writeFileSync(knowledgeMdPath, header + approachesMarkdown)
        console.log(`  CREATED: ${slug} knowledge.md (${meaningfulApproaches.length} approach(es))`)
      }
    }

    // Remove approaches from JSON
    if (dryRun) {
      console.log(`  WOULD REMOVE approaches from JSON: ${slug}`)
    } else {
      delete jsonData.approaches
      fs.writeFileSync(jsonPath, JSON.stringify(jsonData, null, 2) + '\n')
    }

    migratedCount++
  }

  console.log(`\nDone: ${migratedCount} migrated, ${skippedCount} skipped`)

  if (dryRun) {
    console.log('No files written')
  }
}

function isMainModule(): boolean {
  return process.argv[1] ? path.resolve(process.argv[1]) === __filename : false
}

if (isMainModule()) {
  const args = process.argv.slice(2)

  if (args.includes('--help') || args.includes('-h')) {
    printUsage()
    process.exit(0)
  }

  const unknownArgs = args.filter(arg => arg !== '--dry-run')
  if (unknownArgs.length > 0) {
    console.error(`Unknown option(s): ${unknownArgs.join(', ')}`)
    printUsage()
    process.exit(1)
  }

  migrate({ dryRun: args.includes('--dry-run') })
}
