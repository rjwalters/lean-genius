#!/usr/bin/env npx tsx
/**
 * Fill LaTeX Gaps - Targeted LaTeX fetching for missing files
 *
 * This script specifically fetches LaTeX for problems that have HTML cached
 * but are missing LaTeX files. It uses slow/glacial mode for polite scraping.
 *
 * Usage:
 *   npx tsx scripts/erdos/fill-latex-gaps.ts [options]
 *
 * Options:
 *   --slow        60s between requests
 *   --glacial     3 min between requests (default)
 *   --fast        5s between requests (not recommended)
 *   --limit N     Only process first N missing files
 *   --playwright  Use browser automation
 *   --status      Show status without processing
 *   --dry-run     Show what would be done
 */

import * as fs from 'fs'
import * as path from 'path'
import {
  getCachedLatex,
  cacheLatex,
  rateLimitedFetch,
  getSlowConfig,
  getVerySlowConfig,
  type CacheConfig,
} from './cache'
import {
  fetchLatexWithPlaywright,
  closeBrowser,
} from './playwright-fetch'

const BASE_URL = 'https://erdosproblems.com'
const CACHE_DIR = path.join(process.cwd(), '.erdos-cache')

interface Options {
  slow: boolean
  glacial: boolean
  fast: boolean
  limit?: number
  playwright: boolean
  status: boolean
  dryRun: boolean
}

function parseArgs(): Options {
  const args = process.argv.slice(2)
  const options: Options = {
    slow: false,
    glacial: true, // Default to glacial
    fast: false,
    limit: undefined,
    playwright: false,
    status: false,
    dryRun: false,
  }

  for (let i = 0; i < args.length; i++) {
    switch (args[i]) {
      case '--slow':
        options.slow = true
        options.glacial = false
        break
      case '--glacial':
        options.glacial = true
        options.slow = false
        break
      case '--fast':
        options.fast = true
        options.glacial = false
        options.slow = false
        break
      case '--limit':
        options.limit = parseInt(args[++i])
        break
      case '--playwright':
        options.playwright = true
        break
      case '--status':
        options.status = true
        break
      case '--dry-run':
        options.dryRun = true
        break
      case '--help':
      case '-h':
        printHelp()
        process.exit(0)
    }
  }

  return options
}

function printHelp(): void {
  console.log(`
Fill LaTeX Gaps - Targeted LaTeX fetching

Fetches LaTeX for problems that have HTML cached but are missing LaTeX.

Usage:
  npx tsx scripts/erdos/fill-latex-gaps.ts [options]

Options:
  --slow        60s between requests
  --glacial     3 min between requests (default, safest)
  --fast        5s between requests (not recommended)
  --limit N     Only process first N missing files
  --playwright  Use browser automation (recommended)
  --status      Show status without processing
  --dry-run     Show what would be done without fetching
  --help, -h    Show this help

Examples:
  # Check status
  npx tsx scripts/erdos/fill-latex-gaps.ts --status

  # Fill gaps with browser (recommended)
  npx tsx scripts/erdos/fill-latex-gaps.ts --playwright

  # Fill first 50 gaps
  npx tsx scripts/erdos/fill-latex-gaps.ts --limit 50 --playwright
`)
}

/**
 * Find all problem numbers that have HTML but no LaTeX
 */
function findMissingLatex(): number[] {
  if (!fs.existsSync(CACHE_DIR)) {
    console.error('Cache directory not found:', CACHE_DIR)
    return []
  }

  const files = fs.readdirSync(CACHE_DIR)
  const htmlNumbers = new Set<number>()
  const latexNumbers = new Set<number>()

  for (const file of files) {
    const htmlMatch = file.match(/^(\d+)\.html$/)
    if (htmlMatch) {
      htmlNumbers.add(parseInt(htmlMatch[1]))
    }
    const latexMatch = file.match(/^(\d+)\.latex$/)
    if (latexMatch) {
      latexNumbers.add(parseInt(latexMatch[1]))
    }
  }

  const missing: number[] = []
  for (const num of htmlNumbers) {
    if (!latexNumbers.has(num)) {
      missing.push(num)
    }
  }

  return missing.sort((a, b) => a - b)
}

/**
 * Fetch LaTeX for a single problem
 */
async function fetchLatex(
  problemNumber: number,
  config?: CacheConfig,
  usePlaywright = false
): Promise<boolean> {
  if (usePlaywright) {
    const latexContent = await fetchLatexWithPlaywright(problemNumber)
    if (latexContent) {
      cacheLatex(problemNumber, latexContent, config)
      return true
    }
    return false
  }

  try {
    const latexUrl = `${BASE_URL}/latex/${problemNumber}`
    const response = await rateLimitedFetch(latexUrl, config)

    if (response.ok) {
      const latexContent = await response.text()
      // Validate that it's actually LaTeX, not HTML
      if (!latexContent.startsWith('<!DOCTYPE') && !latexContent.startsWith('<html')) {
        cacheLatex(problemNumber, latexContent, config)
        return true
      }
    }
    return false
  } catch (error) {
    console.error(`  Error fetching LaTeX for #${problemNumber}:`, error)
    return false
  }
}

/**
 * Format time remaining estimate
 */
function formatTime(seconds: number): string {
  const hours = Math.floor(seconds / 3600)
  const minutes = Math.floor((seconds % 3600) / 60)
  if (hours > 0) {
    return `${hours}h ${minutes}m`
  }
  return `${minutes}m`
}

async function main(): Promise<void> {
  const options = parseArgs()

  console.log('=== Fill LaTeX Gaps ===\n')

  // Find missing LaTeX files
  const missing = findMissingLatex()

  if (missing.length === 0) {
    console.log('All problems have LaTeX cached!')
    return
  }

  // Categorize missing files
  const early = missing.filter(n => n <= 89)
  const scattered = missing.filter(n => n > 89 && n <= 1135)
  const beyond = missing.filter(n => n > 1135)

  console.log(`Missing LaTeX files: ${missing.length}`)
  console.log(`  Early problems (1-89): ${early.length}`)
  console.log(`  Scattered (90-1135): ${scattered.length}`)
  console.log(`  Beyond defined (1136+): ${beyond.length}`)
  console.log()

  if (options.status) {
    console.log('Missing problem numbers:')
    console.log(missing.join(', '))
    return
  }

  // Determine rate limiting
  let delayMs = 180000 // 3 min default (glacial)
  let modeName = 'GLACIAL'
  if (options.slow) {
    delayMs = 60000
    modeName = 'SLOW'
  } else if (options.fast) {
    delayMs = 5000
    modeName = 'FAST'
  }

  // Apply limit if specified
  let toProcess = missing
  if (options.limit) {
    toProcess = missing.slice(0, options.limit)
    console.log(`Processing first ${toProcess.length} of ${missing.length} missing files`)
  }

  // Time estimate
  const totalSeconds = (toProcess.length * delayMs) / 1000
  console.log(`Mode: ${modeName} (${delayMs / 1000}s between requests)`)
  console.log(`Estimated time: ${formatTime(totalSeconds)}`)
  console.log(`Using Playwright: ${options.playwright}`)
  console.log()

  if (options.dryRun) {
    console.log('** DRY RUN - Would process:')
    console.log(toProcess.join(', '))
    return
  }

  // Get config based on rate
  const config = options.glacial ? getVerySlowConfig() : options.slow ? getSlowConfig() : undefined

  // Process missing LaTeX files
  let success = 0
  let failed = 0
  const startTime = Date.now()

  console.log(`Starting LaTeX fetch for ${toProcess.length} problems...`)
  console.log('Progress will be shown every 10 problems.\n')

  try {
    for (let i = 0; i < toProcess.length; i++) {
      const num = toProcess[i]
      const result = await fetchLatex(num, config, options.playwright)

      if (result) {
        success++
        console.log(`  ✓ #${num} (${i + 1}/${toProcess.length})`)
      } else {
        failed++
        console.log(`  ✗ #${num} - no LaTeX available (${i + 1}/${toProcess.length})`)
      }

      // Progress summary every 10
      if ((i + 1) % 10 === 0 || i === toProcess.length - 1) {
        const elapsed = (Date.now() - startTime) / 1000
        const remaining = ((toProcess.length - i - 1) * delayMs) / 1000
        console.log(`\n  Progress: ${i + 1}/${toProcess.length} | Success: ${success} | Failed: ${failed}`)
        console.log(`  Elapsed: ${formatTime(elapsed)} | Remaining: ~${formatTime(remaining)}\n`)
      }
    }
  } finally {
    if (options.playwright) {
      await closeBrowser()
    }
  }

  // Final summary
  const totalElapsed = (Date.now() - startTime) / 1000
  console.log('\n=== Summary ===')
  console.log(`Processed: ${toProcess.length}`)
  console.log(`Success: ${success}`)
  console.log(`Failed: ${failed}`)
  console.log(`Total time: ${formatTime(totalElapsed)}`)

  // Updated count
  const newMissing = findMissingLatex()
  console.log(`\nRemaining missing: ${newMissing.length}`)
}

main().catch(console.error)
