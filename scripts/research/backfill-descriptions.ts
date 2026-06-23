#!/usr/bin/env npx tsx
/**
 * Backfill Research Descriptions
 *
 * Fixes "AVAILABLE.", "IN-PROGRESS.", "COMPLETED." placeholder descriptions
 * in research problem entries by pulling real descriptions from:
 *
 * 1. Gallery proof meta.json (for graduated problems with linked proofs)
 * 2. knowledge.md "## Problem" section (for problems with research knowledge)
 * 3. Title + tags synthesis (fallback for remaining entries)
 *
 * Updates:
 * - src/data/research/problems/{slug}.json  (problemStatement.plain)
 * - research/problems/{slug}/problem.md     (### Plain Language section)
 *
 * Run: npx tsx scripts/research/backfill-descriptions.ts
 * Idempotent: safe to run multiple times (skips entries with real descriptions)
 */

import * as fs from 'fs'
import * as path from 'path'
import { fileURLToPath } from 'url'

const __filename = fileURLToPath(import.meta.url)
const __dirname = path.dirname(__filename)

const ROOT = path.join(__dirname, '../..')
const RESEARCH_PROBLEMS_DIR = path.join(ROOT, 'research/problems')
const JSON_PROBLEMS_DIR = path.join(ROOT, 'src/data/research/problems')
const PROOFS_DIR = path.join(ROOT, 'src/data/proofs')

// Status prefixes that indicate placeholder descriptions
const STATUS_PREFIXES = [
  'AVAILABLE',
  'IN-PROGRESS',
  'IN PROGRESS',
  'COMPLETED',
  'SKIPPED',
  'SURVEYED',
]

// Template placeholder patterns
const TEMPLATE_PLACEHOLDERS = [
  '[Explain what we\'re trying to prove in accessible terms]',
  '(formal statement to be added)',
]

/**
 * Check if a description is a placeholder that should be replaced
 */
function isPlaceholder(desc: string): boolean {
  const trimmed = desc.trim().replace(/\.$/, '').trim()
  if (!trimmed) return true
  const upper = trimmed.toUpperCase()
  for (const prefix of STATUS_PREFIXES) {
    if (upper === prefix || upper.startsWith(prefix + '.') || upper.startsWith(prefix + ' ')) {
      // Only treat as placeholder if the description is essentially JUST the status
      // Allow "AVAILABLE. Some real text here" to NOT be a placeholder
      const afterPrefix = trimmed.slice(prefix.length).replace(/^[.\s]+/, '').trim()
      if (afterPrefix.length < 10) return true
    }
  }
  for (const tmpl of TEMPLATE_PLACEHOLDERS) {
    if (trimmed === tmpl || trimmed.startsWith(tmpl)) return true
  }
  return false
}

/**
 * Get description from gallery proof meta.json
 */
function getGalleryDescription(slug: string): string | null {
  const metaPath = path.join(PROOFS_DIR, slug, 'meta.json')
  if (!fs.existsSync(metaPath)) return null
  try {
    const meta = JSON.parse(fs.readFileSync(metaPath, 'utf-8'))
    const desc = meta.description?.trim()
    if (desc && desc.length > 10 && !isPlaceholder(desc)) {
      return desc
    }
  } catch { /* ignore */ }
  return null
}

/**
 * Get description from knowledge.md "## Problem" section
 */
function getKnowledgeDescription(slug: string): string | null {
  const knowledgePath = path.join(RESEARCH_PROBLEMS_DIR, slug, 'knowledge.md')
  if (!fs.existsSync(knowledgePath)) return null
  try {
    const content = fs.readFileSync(knowledgePath, 'utf-8')
    // Look for ## Problem section
    const match = content.match(/##\s*Problem\s*\n([\s\S]*?)(?=\n##|\Z)/m)
    if (match) {
      const text = match[1].trim()
      if (text.length > 20) {
        // Get first meaningful paragraph, strip markdown bold/links
        const paragraphs = text.split(/\n\n+/)
        for (const para of paragraphs) {
          const cleaned = para
            .replace(/\*\*([^*]+)\*\*/g, '$1')
            .replace(/\[([^\]]+)\]\([^)]+\)/g, '$1')
            .replace(/\n/g, ' ')
            .trim()
          if (cleaned.length > 20 && !cleaned.startsWith('#')) {
            // Truncate to 2 sentences max
            const sentences = cleaned.match(/[^.!?]+[.!?]+/g)
            if (sentences && sentences.length > 2) {
              return sentences.slice(0, 2).join('').trim()
            }
            return cleaned.length > 300 ? cleaned.slice(0, 297) + '...' : cleaned
          }
        }
      }
    }
  } catch { /* ignore */ }
  return null
}

/**
 * Tag category descriptions for generating fallback descriptions
 */
const TAG_AREA_MAP: Record<string, string> = {
  'number-theory': 'number theory',
  'combinatorics': 'combinatorics',
  'algebra': 'algebra',
  'analysis': 'mathematical analysis',
  'geometry': 'geometry',
  'topology': 'topology',
  'graph-theory': 'graph theory',
  'probability': 'probability theory',
  'measure-theory': 'measure theory',
  'set-theory': 'set theory',
  'logic': 'mathematical logic',
  'category-theory': 'category theory',
  'field-theory': 'field theory',
  'group-theory': 'group theory',
  'ring-theory': 'ring theory',
  'galois-theory': 'Galois theory',
  'linear-algebra': 'linear algebra',
  'functional-analysis': 'functional analysis',
  'real-analysis': 'real analysis',
  'complex-analysis': 'complex analysis',
  'differential-equations': 'differential equations',
  'prime-numbers': 'prime number theory',
  'diophantine': 'Diophantine equations',
  'modular-arithmetic': 'modular arithmetic',
  'lattice-paths': 'lattice path combinatorics',
  'extremal-combinatorics': 'extremal combinatorics',
  'ramsey-theory': 'Ramsey theory',
  'additive-combinatorics': 'additive combinatorics',
  'partition-theory': 'partition theory',
  'sieve-theory': 'sieve methods',
  'carmichael-numbers': 'Carmichael numbers',
  'pseudoprimes': 'pseudoprimes',
  'polynomial': 'polynomial theory',
  'matrix-theory': 'matrix theory',
  'representation-theory': 'representation theory',
  'algebraic-geometry': 'algebraic geometry',
  'dynamical-systems': 'dynamical systems',
  'ergodic-theory': 'ergodic theory',
  'information-theory': 'information theory',
}

/**
 * Tag type descriptions for generating fallback descriptions
 */
const TAG_TYPE_MAP: Record<string, string> = {
  'extension': 'extending an existing formalization',
  'generalization': 'generalizing a known result',
  'completion': 'completing a partial formalization',
  'mathlib-contribution': 'contributing to the Mathlib library',
  'classic': 'a classical mathematical result',
  'open-problem': 'an open mathematical problem',
  'seeker-selected': '',  // Not useful for description
  '1-sorry': '',
  '0-sorry': '',
}

/**
 * Generate a description from title and tags
 */
function generateFromTitleAndTags(title: string, tags: string[]): string {
  // Find mathematical area from tags
  const areas: string[] = []
  const types: string[] = []

  for (const tag of tags) {
    if (TAG_AREA_MAP[tag]) areas.push(TAG_AREA_MAP[tag])
    if (TAG_TYPE_MAP[tag] && TAG_TYPE_MAP[tag].length > 0) types.push(TAG_TYPE_MAP[tag])
  }

  // Clean up the title - remove common prefix patterns
  let cleanTitle = title
    .replace(/^Problem:\s*/i, '')
    .replace(/^Erdős\s*(?:Problem\s*)?#?\d+\s*[-:]\s*/i, '')
    .trim()

  // If title is already a good description (contains a verb or mathematical statement), use it directly
  if (cleanTitle.length > 30 && /\b(prove|show|determine|find|construct|establish|formalize|verify|extend|generalize|compute|count|classify|characterize)\b/i.test(cleanTitle)) {
    // Already a good descriptive title
    if (!cleanTitle.endsWith('.')) cleanTitle += '.'
    return cleanTitle
  }

  // Build a description
  const parts: string[] = []

  if (types.length > 0) {
    // "Formalization extending/generalizing [title] in [area]"
    const typePhrase = types[0]
    if (areas.length > 0) {
      parts.push(`Formalization ${typePhrase} in ${areas[0]}: ${cleanTitle}.`)
    } else {
      parts.push(`Formalization ${typePhrase}: ${cleanTitle}.`)
    }
  } else if (areas.length > 0) {
    parts.push(`Formal investigation in ${areas[0]}: ${cleanTitle}.`)
  } else {
    parts.push(`Formal mathematical investigation: ${cleanTitle}.`)
  }

  return parts.join(' ')
}

/**
 * Update problem.md file's Plain Language section
 */
function updateProblemMd(slug: string, description: string, dryRun = false): boolean {
  const problemMdPath = path.join(RESEARCH_PROBLEMS_DIR, slug, 'problem.md')
  if (!fs.existsSync(problemMdPath)) return false

  let content = fs.readFileSync(problemMdPath, 'utf-8')

  // Match the Plain Language section and replace its first line
  const match = content.match(/(###\s*Plain Language\s*\n)([\s\S]*?)(\n###|\n##|$)/)
  if (!match) return false

  const currentPlain = match[2].trim().split('\n')[0]
  if (!isPlaceholder(currentPlain)) return false  // Already has a real description

  if (dryRun) return true

  // Replace the plain language content
  const newSection = `${match[1]}${description}\n${match[3]}`
  content = content.replace(match[0], newSection)

  fs.writeFileSync(problemMdPath, content)
  return true
}

/**
 * Update JSON problem file's problemStatement.plain
 */
function updateProblemJson(slug: string, description: string, dryRun = false): boolean {
  const jsonPath = path.join(JSON_PROBLEMS_DIR, `${slug}.json`)
  if (!fs.existsSync(jsonPath)) return false

  try {
    const data = JSON.parse(fs.readFileSync(jsonPath, 'utf-8'))
    const currentPlain = data.problemStatement?.plain?.trim() || ''

    if (!isPlaceholder(currentPlain)) return false  // Already has a real description

    if (!data.problemStatement) {
      data.problemStatement = { formal: '', plain: '', whyMatters: [] }
    }

    if (dryRun) return true

    data.problemStatement.plain = description

    fs.writeFileSync(jsonPath, JSON.stringify(data, null, 2) + '\n')
    return true
  } catch {
    return false
  }
}

/**
 * Main backfill function
 */
function printUsage(): void {
  console.log(`Usage: npx tsx scripts/research/backfill-descriptions.ts [options]

Backfill placeholder research descriptions from gallery metadata, knowledge.md,
or title and tag synthesis.

Options:
  --dry-run       Report description backfills without writing files
  --help, -h      Show this help message`)
}

function backfill(options: { dryRun?: boolean } = {}): void {
  const { dryRun = false } = options

  console.log(
    dryRun
      ? 'Backfilling research problem descriptions (dry run)...\n'
      : 'Backfilling research problem descriptions...\n'
  )

  if (!fs.existsSync(JSON_PROBLEMS_DIR)) {
    console.error('Error: JSON problems directory not found:', JSON_PROBLEMS_DIR)
    process.exit(1)
  }

  const jsonFiles = fs.readdirSync(JSON_PROBLEMS_DIR).filter(f => f.endsWith('.json'))
  console.log(`  Found ${jsonFiles.length} JSON problem files\n`)

  let fromGallery = 0
  let fromKnowledge = 0
  let fromTitle = 0
  let alreadyGood = 0
  let jsonUpdated = 0
  let mdUpdated = 0
  let errors = 0

  for (const file of jsonFiles.sort()) {
    const slug = file.replace('.json', '')
    let data: any

    try {
      data = JSON.parse(fs.readFileSync(path.join(JSON_PROBLEMS_DIR, file), 'utf-8'))
    } catch {
      errors++
      continue
    }

    const currentPlain = data.problemStatement?.plain?.trim() || ''

    // Skip entries that already have real descriptions
    if (!isPlaceholder(currentPlain)) {
      alreadyGood++
      continue
    }

    const title = data.title || slug
    const tags = data.tags || []

    // Try sources in priority order
    let description: string | null = null
    let source = ''

    // Source 1: Gallery proof meta.json
    description = getGalleryDescription(slug)
    if (description) {
      source = 'gallery'
      fromGallery++
    }

    // Source 2: knowledge.md Problem section
    if (!description) {
      description = getKnowledgeDescription(slug)
      if (description) {
        source = 'knowledge'
        fromKnowledge++
      }
    }

    // Source 3: Generate from title + tags
    if (!description) {
      description = generateFromTitleAndTags(title, tags)
      source = 'title+tags'
      fromTitle++
    }

    // Apply the description
    if (description) {
      const jsonOk = updateProblemJson(slug, description, dryRun)
      const mdOk = updateProblemMd(slug, description, dryRun)

      if (jsonOk) jsonUpdated++
      if (mdOk) mdUpdated++

      if (jsonOk || mdOk) {
        console.log(`  [${source}] ${slug}: ${description.slice(0, 80)}${description.length > 80 ? '...' : ''}`)
      }
    }
  }

  console.log(`\nBackfill Summary:`)
  console.log(`  Already good:        ${alreadyGood}`)
  console.log(`  From gallery:        ${fromGallery}`)
  console.log(`  From knowledge.md:   ${fromKnowledge}`)
  console.log(`  From title+tags:     ${fromTitle}`)
  console.log(`  JSON files updated:  ${jsonUpdated}`)
  console.log(`  problem.md updated:  ${mdUpdated}`)
  console.log(`  Errors:              ${errors}`)
  if (dryRun) {
    console.log(`  No files written`)
  }
  console.log(`\nDone! Run 'pnpm research:build' to regenerate research-listings.json`)
}

if (process.argv[1] && import.meta.url === `file://${process.argv[1]}`) {
  const args = process.argv.slice(2)

  if (args.includes('--help') || args.includes('-h')) {
    printUsage()
    process.exit(0)
  }

  backfill({ dryRun: args.includes('--dry-run') })
}
