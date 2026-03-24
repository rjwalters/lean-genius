#!/usr/bin/env npx tsx
/**
 * Backfill Research Problem Descriptions
 *
 * Fixes research problems that have "AVAILABLE." or other status prefixes
 * as their plain language description. Generates proper descriptions from:
 *   1. The knowledge.markdown "## Problem" section (best source)
 *   2. The problem title (fallback - humanized/expanded)
 *
 * Also updates the corresponding research/problems/{slug}/problem.md files.
 *
 * Usage:
 *   npx tsx scripts/research/backfill-descriptions.ts              # Dry run (default)
 *   npx tsx scripts/research/backfill-descriptions.ts --apply       # Actually write changes
 *   npx tsx scripts/research/backfill-descriptions.ts --verbose     # Show all details
 */

import * as fs from 'fs'
import * as path from 'path'
import { fileURLToPath } from 'url'

const __filename = fileURLToPath(import.meta.url)
const __dirname = path.dirname(__filename)

const PROBLEMS_JSON_DIR = path.join(__dirname, '../../src/data/research/problems')
const PROBLEMS_MD_DIR = path.join(__dirname, '../../research/problems')

// Known status prefixes that should not be used as descriptions
const STATUS_PREFIXES = ['AVAILABLE', 'IN-PROGRESS', 'COMPLETED', 'BLOCKED', 'SKIPPED', 'SURVEYED']

// Parse CLI args
const args = process.argv.slice(2)
const dryRun = !args.includes('--apply')
const verbose = args.includes('--verbose')

interface ProblemJson {
  slug: string
  title: string
  problemStatement: {
    formal: string
    plain: string
    whyMatters: string[]
  }
  knowledge: {
    markdown?: string
    [key: string]: unknown
  }
  tags: string[]
  [key: string]: unknown
}

/**
 * Check if a plain description is a status placeholder.
 */
function isStatusPlaceholder(plain: string): boolean {
  const trimmed = plain.trim()
  return STATUS_PREFIXES.some(prefix =>
    trimmed === prefix ||
    trimmed === `${prefix}.` ||
    trimmed.startsWith(`${prefix}:`) ||
    trimmed.startsWith(`${prefix} `)
  )
}

/**
 * Extract a description from the knowledge.markdown "## Problem" section.
 * Many knowledge files have a structure like:
 *   ## Problem
 *   <description paragraph>
 *   ## ...
 *
 * Or sometimes:
 *   ## Problem Summary
 *   <description paragraph>
 */
function extractFromKnowledge(markdown: string): string | null {
  if (!markdown) return null

  // Try "## Problem Summary" first (more specific)
  // Note: no 'm' flag so that '$' matches end-of-string, not end-of-line
  const summaryMatch = markdown.match(/##\s*Problem Summary\s*\n+([\s\S]*?)(?=\n##|\n\*\*Status\*\*)/)
  if (summaryMatch) {
    const text = cleanExtractedText(summaryMatch[1])
    if (text) return text
  }

  // Try "## Problem" section (but not "## Problem Summary" which was already tried)
  const problemMatch = markdown.match(/##\s*Problem\s*\n+([\s\S]*?)(?=\n##)/)
  if (problemMatch) {
    const text = cleanExtractedText(problemMatch[1])
    if (text) return text
  }

  // Try "## Overview" section
  const overviewMatch = markdown.match(/##\s*Overview\s*\n+([\s\S]*?)(?=\n##)/)
  if (overviewMatch) {
    const text = cleanExtractedText(overviewMatch[1])
    if (text) return text
  }

  return null
}

/**
 * Clean extracted text: get the first meaningful sentence,
 * removing markdown formatting and status lines.
 */
function cleanExtractedText(raw: string): string | null {
  // Split into lines and find the first non-empty, non-heading, non-status line
  const lines = raw.split('\n')
  const paragraphLines: string[] = []

  for (const line of lines) {
    const trimmed = line.trim()
    // Skip empty lines, headings, status lines, and horizontal rules
    if (!trimmed) {
      if (paragraphLines.length > 0) break // End of first paragraph
      continue
    }
    if (trimmed.startsWith('#')) break
    if (trimmed.startsWith('---')) break
    if (trimmed.startsWith('**Status**:')) continue
    if (trimmed.startsWith('**Milestone')) continue
    if (STATUS_PREFIXES.some(p => trimmed.startsWith(p))) continue

    paragraphLines.push(trimmed)
  }

  if (paragraphLines.length === 0) return null

  // Join the paragraph and extract the first sentence or two
  let text = paragraphLines.join(' ')

  // Remove markdown bold/italic formatting
  text = text.replace(/\*\*([^*]+)\*\*/g, '$1')
  text = text.replace(/\*([^*]+)\*/g, '$1')
  // Remove markdown links [text](url) -> text
  text = text.replace(/\[([^\]]+)\]\([^)]+\)/g, '$1')

  // Get first sentence (up to first period followed by space or end-of-string)
  const sentenceMatch = text.match(/^(.+?\.)(?:\s|$)/)
  if (sentenceMatch && sentenceMatch[1].length >= 20) {
    return sentenceMatch[1]
  }

  // If first sentence is too short or no period found, take first ~150 chars
  if (text.length > 150) {
    // Cut at a word boundary
    const cut = text.slice(0, 150).replace(/\s+\S*$/, '')
    return cut
  }

  return text || null
}

/**
 * Generate a description from the problem title.
 * Converts slug-like titles to human-readable descriptions.
 */
function descriptionFromTitle(title: string): string {
  // Title is already human-readable in most cases
  // Just ensure it reads as a description
  const cleaned = title.trim()

  // If title ends with '...' it was truncated - use as-is
  if (cleaned.endsWith('...')) {
    return cleaned
  }

  // If title is already a question or statement, use as-is
  if (cleaned.endsWith('?') || cleaned.endsWith('.')) {
    return cleaned
  }

  // Otherwise return the title as the description
  return cleaned
}

/**
 * Update the problem.md file to replace the AVAILABLE placeholder.
 */
function updateProblemMd(slug: string, newDescription: string): boolean {
  const mdPath = path.join(PROBLEMS_MD_DIR, slug, 'problem.md')
  if (!fs.existsSync(mdPath)) return false

  let content = fs.readFileSync(mdPath, 'utf-8')

  // Find the "### Plain Language" section and replace its content
  const plainLangPattern = /(### Plain Language\s*\n)([^\n]*)/m
  const match = content.match(plainLangPattern)
  if (!match) return false

  const currentText = match[2].trim()
  // Only replace if the current text is a status placeholder
  if (!isStatusPlaceholder(currentText.replace(/\.$/, ''))) return false

  // newDescription already has proper terminal punctuation
  content = content.replace(plainLangPattern, `$1${newDescription}`)

  // Also fix the "Why This Matters" section if it has the same placeholder
  for (const prefix of STATUS_PREFIXES) {
    const whyPattern = new RegExp(
      `(\\*\\*Research value\\*\\*\\s*-\\s*)${prefix}[^\\n]*`,
      'g'
    )
    content = content.replace(whyPattern, `$1${newDescription}`)
  }

  if (!dryRun) {
    fs.writeFileSync(mdPath, content)
  }
  return true
}

/**
 * Main backfill function
 */
function main(): void {
  console.log(`Research Problem Description Backfill`)
  console.log(`Mode: ${dryRun ? 'DRY RUN (use --apply to write changes)' : 'APPLYING CHANGES'}`)
  console.log()

  // Find all problem JSON files
  const files = fs.readdirSync(PROBLEMS_JSON_DIR).filter(f => f.endsWith('.json'))
  console.log(`Found ${files.length} problem JSON files`)

  let placeholderCount = 0
  let fixedFromKnowledge = 0
  let fixedFromTitle = 0
  let mdUpdated = 0
  let skipped = 0

  for (const file of files) {
    const jsonPath = path.join(PROBLEMS_JSON_DIR, file)
    let problem: ProblemJson
    try {
      problem = JSON.parse(fs.readFileSync(jsonPath, 'utf-8'))
    } catch {
      console.warn(`  Warning: Failed to parse ${file}`)
      continue
    }

    const plain = problem.problemStatement?.plain || ''
    if (!isStatusPlaceholder(plain)) continue

    placeholderCount++
    const slug = problem.slug || file.replace('.json', '')

    // Try to extract from knowledge.markdown
    const knowledgeMarkdown = problem.knowledge?.markdown || ''
    let newDescription = extractFromKnowledge(knowledgeMarkdown)
    let source = 'knowledge'

    if (!newDescription) {
      // Fall back to title
      newDescription = descriptionFromTitle(problem.title)
      source = 'title'
    }

    if (!newDescription) {
      skipped++
      if (verbose) {
        console.log(`  SKIP ${slug}: no description source available`)
      }
      continue
    }

    // Normalize trailing punctuation: preserve ellipsis (...) and question marks
    let cleanDesc = newDescription.trim()
    // Collapse redundant periods (but preserve ellipsis)
    if (cleanDesc.endsWith('...')) {
      // Keep ellipsis as-is (it indicates truncated text)
    } else {
      cleanDesc = cleanDesc.replace(/\.{2,}$/, '.')
    }

    if (source === 'knowledge') {
      fixedFromKnowledge++
    } else {
      fixedFromTitle++
    }

    // Ensure description ends with terminal punctuation
    const finalDesc = /[.!?]$/.test(cleanDesc) ? cleanDesc : `${cleanDesc}.`

    if (verbose || dryRun) {
      console.log(`  ${dryRun ? 'WOULD FIX' : 'FIX'} ${slug}`)
      console.log(`    Old: "${plain}"`)
      console.log(`    New: "${finalDesc}" (from ${source})`)
    }

    // Update JSON
    problem.problemStatement.plain = finalDesc

    if (!dryRun) {
      fs.writeFileSync(jsonPath, JSON.stringify(problem, null, 2) + '\n')
    }

    // Update problem.md
    const mdWasUpdated = updateProblemMd(slug, finalDesc)
    if (mdWasUpdated) {
      mdUpdated++
    }
  }

  console.log()
  console.log(`Summary:`)
  console.log(`  Problems with status placeholder: ${placeholderCount}`)
  console.log(`  Fixed from knowledge.markdown:    ${fixedFromKnowledge}`)
  console.log(`  Fixed from title:                 ${fixedFromTitle}`)
  console.log(`  Problem.md files updated:         ${mdUpdated}`)
  console.log(`  Skipped (no source):              ${skipped}`)

  if (dryRun) {
    console.log()
    console.log(`This was a dry run. Use --apply to write changes.`)
  } else {
    console.log()
    console.log(`Changes applied successfully.`)
  }
}

main()
