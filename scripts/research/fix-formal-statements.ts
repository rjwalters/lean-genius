#!/usr/bin/env npx tsx
/**
 * Fix Formal Statements Cleanup Script
 *
 * Strips website navigation junk from Erdos problem.md files.
 * The junk comes from scraping erdosproblems.com and includes
 * navigation text (Forum, Favourites, Tags, etc.) prepended to
 * both the Formal Statement and Plain Language sections.
 *
 * Two junk patterns exist:
 * 1. Clean nav prefix: "Forum\nFavourites\nTags\n..." (nav on its own lines)
 * 2. Mixed prefix: "Let Forum\nFavourites\n..." (content fragment + nav)
 *
 * Run: npx tsx scripts/research/fix-formal-statements.ts
 */

import * as fs from 'fs'
import * as path from 'path'
import { fileURLToPath } from 'url'

const __filename = fileURLToPath(import.meta.url)
const __dirname = path.dirname(__filename)

const PROBLEMS_DIR = path.join(__dirname, '../../research/problems')

/**
 * Check if text contains the navigation junk pattern.
 * Looks for the "Forum" + "Favourites" + "Random Open" sequence.
 */
function hasNavJunk(text: string): boolean {
  return (text.includes('Forum') &&
          text.includes('Favourites') &&
          text.includes('Random Open'))
}

/**
 * Strip navigation junk from text.
 * Finds the "Random Open" line and returns everything after it.
 * Handles both "Forum\n..." and "Let Forum\n..." patterns.
 */
function stripNavPrefix(text: string): string {
  const lines = text.split('\n')

  // Find the "Random Open" line
  let randomOpenIdx = -1
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].trim() === 'Random Open') {
      randomOpenIdx = i
      break
    }
  }

  if (randomOpenIdx < 0) return text

  let i = randomOpenIdx + 1

  // Skip blank lines after nav junk
  while (i < lines.length && lines[i].trim() === '') i++

  // Return remaining content
  return lines.slice(i).join('\n')
}

/**
 * Strip trailing junk from formal statement content.
 * Removes:
 * - "References" sections (bibliography entries)
 * - "Back to the problem" links
 * - Trailing blank lines
 */
function stripTrailingJunk(text: string): string {
  const lines = text.split('\n')

  // Work backwards to find where trailing junk starts
  let end = lines.length

  // Remove trailing empty lines
  while (end > 0 && lines[end - 1].trim() === '') end--

  // Remove "Back to the problem" if present
  if (end > 0 && lines[end - 1].trim() === 'Back to the problem') {
    end--
    // Remove blank lines before "Back to the problem"
    while (end > 0 && lines[end - 1].trim() === '') end--
  }

  // Remove References section if present
  // Scan backwards to find "References" heading
  let refStart = -1
  for (let j = end - 1; j >= 0; j--) {
    const trimmed = lines[j].trim()
    if (trimmed === 'References') {
      refStart = j
      break
    }
  }

  if (refStart >= 0) {
    end = refStart
    // Remove blank lines before References
    while (end > 0 && lines[end - 1].trim() === '') end--
  }

  // Final trailing blank line cleanup
  while (end > 0 && lines[end - 1].trim() === '') end--

  return lines.slice(0, end).join('\n')
}

/**
 * Process a single problem.md file.
 * Cleans both formal statement and plain language sections.
 */
function processFile(filePath: string): 'cleaned' | 'already-clean' | 'placeholder' {
  const content = fs.readFileSync(filePath, 'utf-8')

  // Check if this is a placeholder
  const formalMatch = content.match(/### Formal Statement[\s\S]*?\$\$([\s\S]*?)\$\$/)
  if (formalMatch) {
    const formalText = formalMatch[1].trim()
    if (formalText === '(LaTeX not available)' || formalText === '\\text{(formal statement to be added)}') {
      return 'placeholder'
    }
  }

  let modified = content
  let didClean = false

  // --- Clean Formal Statement section ---
  const formalRegex = /(### Formal Statement\n\$\$\n)([\s\S]*?)(\$\$)/
  const formalSectionMatch = modified.match(formalRegex)
  let cleanedFormalContent = ''

  if (formalSectionMatch && hasNavJunk(formalSectionMatch[2])) {
    let cleaned = stripNavPrefix(formalSectionMatch[2])
    cleaned = stripTrailingJunk(cleaned)
    cleanedFormalContent = cleaned.trim()
    cleaned = cleaned.trimEnd() + '\n'
    // Use replacer function to avoid $ interpretation in replacement string
    modified = modified.replace(formalRegex, (_match, prefix, _body, suffix) => {
      return prefix + cleaned + suffix
    })
    didClean = true
  }

  // --- Clean Plain Language section ---
  const plainRegex = /(### Plain Language\n)([\s\S]*?)(\n### Formal Statement)/
  const plainSectionMatch = modified.match(plainRegex)

  if (plainSectionMatch && hasNavJunk(plainSectionMatch[2])) {
    let cleaned = stripNavPrefix(plainSectionMatch[2])
    cleaned = stripTrailingJunk(cleaned)
    cleaned = cleaned.trim()

    // If nothing left after stripping, use cleaned formal content
    if (!cleaned && cleanedFormalContent) {
      cleaned = cleanedFormalContent.split('\n\n')[0]
    }

    if (cleaned) {
      // Use replacer function to avoid $ interpretation in replacement string
      modified = modified.replace(plainRegex, (_match, prefix, _body, suffix) => {
        return prefix + cleaned + '\n\n' + suffix
      })
      didClean = true
    }
  }

  if (didClean) {
    fs.writeFileSync(filePath, modified)
    return 'cleaned'
  }

  return 'already-clean'
}

/**
 * Main
 */
function main(): void {
  console.log('Fixing formal statements in Erdos research problem files...\n')

  const dirs = fs.readdirSync(PROBLEMS_DIR)
    .filter(d => d.startsWith('erdos-'))
    .filter(d => fs.existsSync(path.join(PROBLEMS_DIR, d, 'problem.md')))
    .sort()

  let cleaned = 0
  let alreadyClean = 0
  let placeholder = 0
  let potentialRescrape = 0

  for (const dir of dirs) {
    const filePath = path.join(PROBLEMS_DIR, dir, 'problem.md')
    const result = processFile(filePath)

    switch (result) {
      case 'cleaned':
        cleaned++
        console.log(`  Cleaned: ${dir}`)
        break
      case 'already-clean':
        alreadyClean++
        break
      case 'placeholder': {
        placeholder++
        // Check if plain language has usable LaTeX
        const content = fs.readFileSync(filePath, 'utf-8')
        const plainMatch = content.match(/### Plain Language\n([\s\S]*?)(?=\n### Formal Statement)/)
        if (plainMatch) {
          const plain = plainMatch[1].trim()
          if (plain.includes('$') || plain.includes('\\[')) {
            potentialRescrape++
          }
        }
        break
      }
    }
  }

  console.log(`\n--- Summary ---`)
  console.log(`Files cleaned:     ${cleaned}`)
  console.log(`Already clean:     ${alreadyClean}`)
  console.log(`Placeholders:      ${placeholder}`)
  console.log(`  (with LaTeX in plain, could rescrape: ${potentialRescrape})`)
  console.log(`Total processed:   ${dirs.length}`)
}

main()
