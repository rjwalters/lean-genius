#!/usr/bin/env npx tsx
/**
 * Erdős Problems Collection Pipeline
 *
 * Scrapes erdosproblems.com and generates:
 * - Gallery stub templates for solved problems
 * - Research topic entries for open problems
 * - Aristotle job candidates for tractable problems
 *
 * Usage:
 *   npx tsx scripts/erdos/index.ts [options]
 *
 * Options:
 *   --dry-run         Preview without writing files
 *   --range 1-100     Process subset of problems (e.g., 1-100)
 *   --batch 10        Process next N uncached problems (default: 10)
 *   --continue        Continue from where we left off (alias for --batch 10)
 *   --refresh         Ignore cache, fetch fresh
 *   --gallery-only    Only generate gallery stubs
 *   --research-only   Only generate research entries
 *   --status          Show status without processing
 *   --verbose         Verbose output
 *   --help            Show help
 */

import type { CliOptions, PipelineStats, TransformedProblem } from './types'
import { getCacheStats, ensureCacheDir, getProgressSummary, getNextUncachedBatch } from './cache'
import { scrapeRange, scrapeProblems, getScrapeStats } from './scrape'
import { transformProblems, getTransformStats } from './transform'
import { filterDuplicates, printDedupeReport } from './dedupe'
import { generateGalleryEntries, getGalleryStats } from './generate-gallery'
import { generateResearchEntries, getResearchStats } from './generate-research'
import { generateAristotleCandidates, printAristotleReport } from './generate-aristotle'

/**
 * Parse command line arguments
 */
function parseArgs(): CliOptions {
  const args = process.argv.slice(2)
  const options: CliOptions = {
    dryRun: false,
    range: undefined,
    batch: undefined,
    refresh: false,
    galleryOnly: false,
    researchOnly: false,
    status: false,
    verbose: false,
  }

  for (let i = 0; i < args.length; i++) {
    const arg = args[i]

    switch (arg) {
      case '--dry-run':
        options.dryRun = true
        break
      case '--range':
        options.range = args[++i]
        break
      case '--batch':
        options.batch = parseInt(args[++i]) || 10
        break
      case '--continue':
        options.batch = 10
        break
      case '--refresh':
        options.refresh = true
        break
      case '--gallery-only':
        options.galleryOnly = true
        break
      case '--research-only':
        options.researchOnly = true
        break
      case '--status':
        options.status = true
        break
      case '--verbose':
      case '-v':
        options.verbose = true
        break
      case '--help':
      case '-h':
        printHelp()
        process.exit(0)
      default:
        console.error(`Unknown option: ${arg}`)
        printHelp()
        process.exit(1)
    }
  }

  return options
}

/**
 * Print help message
 */
function printHelp(): void {
  console.log(`
Erdős Problems Collection Pipeline

Scrapes erdosproblems.com and generates gallery/research entries.

Usage:
  npx tsx scripts/erdos/index.ts [options]

Options:
  --batch N         Process next N uncached problems (default: 10)
  --continue        Continue from where we left off (same as --batch 10)
  --range 1-100     Process specific range of problems
  --dry-run         Preview without writing files
  --refresh         Ignore cache, fetch fresh
  --gallery-only    Only generate gallery stubs (solved problems)
  --research-only   Only generate research entries (open problems)
  --status          Show progress and status
  --verbose, -v     Verbose output
  --help, -h        Show this help

Examples:
  # Process next 10 problems (incremental)
  npx tsx scripts/erdos/index.ts --continue

  # Process next 20 problems
  npx tsx scripts/erdos/index.ts --batch 20

  # Check progress
  npx tsx scripts/erdos/index.ts --status

  # Process specific range
  npx tsx scripts/erdos/index.ts --range 1-100
`)
}

/**
 * Parse range string like "1-100"
 */
function parseRange(range: string): { start: number; end: number } {
  const match = range.match(/^(\d+)-(\d+)$/)
  if (!match) {
    console.error(`Invalid range format: ${range}. Use format like "1-100"`)
    process.exit(1)
  }
  return {
    start: parseInt(match[1]),
    end: parseInt(match[2]),
  }
}

/**
 * Show status information
 */
function showStatus(): void {
  console.log('=== Erdős Problems Pipeline Status ===\n')

  // Progress summary
  const progress = getProgressSummary()
  const bar = '█'.repeat(Math.floor(progress.percentComplete / 5)) + '░'.repeat(20 - Math.floor(progress.percentComplete / 5))
  console.log('Progress:')
  console.log(`  [${bar}] ${progress.percentComplete}%`)
  console.log(`  Cached: ${progress.cached} / ${progress.total}`)
  console.log(`  Remaining: ${progress.remaining}`)

  if (progress.nextBatch.length > 0) {
    console.log(`\n  Next batch: #${progress.nextBatch[0]}-${progress.nextBatch[progress.nextBatch.length - 1]}`)
  }

  // Cache details
  const cacheStats = getCacheStats()
  if (cacheStats.newestEntry) {
    console.log(`  Last scraped: ${new Date(cacheStats.newestEntry).toLocaleString()}`)
  }

  // Deduplication status
  printDedupeReport()

  console.log('\nNext steps:')
  console.log('  npx tsx scripts/erdos/index.ts --continue     # Process next 10')
  console.log('  npx tsx scripts/erdos/index.ts --batch 20     # Process next 20')
  console.log('  npx tsx scripts/erdos/index.ts --dry-run      # Preview only')
}

/**
 * Run the pipeline
 */
async function runPipeline(options: CliOptions): Promise<PipelineStats> {
  const stats: PipelineStats = {
    totalScraped: 0,
    solvedCount: 0,
    openCount: 0,
    partiallySolvedCount: 0,
    galleryCreated: 0,
    gallerySkipped: 0,
    researchCreated: 0,
    researchSkipped: 0,
    aristotleCandidates: 0,
    errors: 0,
  }

  console.log('=== Erdős Problems Collection Pipeline ===\n')

  if (options.dryRun) {
    console.log('** DRY RUN MODE - No files will be written **\n')
  }

  // Ensure cache directory exists
  ensureCacheDir()

  // Determine which problems to scrape
  let scraped: Awaited<ReturnType<typeof scrapeProblems>>

  if (options.batch) {
    // Batch mode: get next N uncached problems
    const batchNumbers = getNextUncachedBatch(options.batch)
    if (batchNumbers.length === 0) {
      console.log('All problems have been cached!')
      const progress = getProgressSummary()
      console.log(`  Total cached: ${progress.cached}/${progress.total}\n`)
      return stats
    }
    console.log(`Step 1: Scraping batch of ${batchNumbers.length} uncached problems...`)
    scraped = await scrapeProblems(batchNumbers, undefined, !options.refresh)
  } else if (options.range) {
    // Range mode: scrape specific range
    const range = parseRange(options.range)
    console.log(`Step 1: Scraping problems ${range.start}-${range.end}...`)
    scraped = await scrapeRange(range.start, range.end, undefined, !options.refresh)
  } else {
    // Default: scrape all (1-1200)
    console.log('Step 1: Scraping all problems 1-1200...')
    scraped = await scrapeRange(1, 1200, undefined, !options.refresh)
  }
  stats.totalScraped = scraped.length

  const scrapeStats = getScrapeStats(scraped)
  stats.solvedCount = scrapeStats.solved
  stats.openCount = scrapeStats.open
  stats.partiallySolvedCount = scrapeStats.partiallySolved

  console.log(`  Scraped: ${scraped.length} problems`)
  console.log(`  Open: ${scrapeStats.open}, Solved: ${scrapeStats.solved}, Partial: ${scrapeStats.partiallySolved}`)
  console.log(`  Unique tags: ${scrapeStats.uniqueTags.length}`)

  if (options.verbose) {
    console.log(`  Tags: ${scrapeStats.uniqueTags.join(', ')}`)
  }

  // Step 2: Transform problems
  console.log('\nStep 2: Transforming problems...')
  const transformed = transformProblems(scraped)
  const transformStats = getTransformStats(transformed)

  console.log(`  Aristotle-suitable: ${transformStats.aristotleSuitableCount}`)
  console.log(`  Avg tractability: ${transformStats.avgTractability.toFixed(1)}`)
  console.log(`  Tier distribution: S=${transformStats.tierDistribution.S}, A=${transformStats.tierDistribution.A}, B=${transformStats.tierDistribution.B}, C=${transformStats.tierDistribution.C}, D=${transformStats.tierDistribution.D}`)

  // Step 3: Deduplicate
  console.log('\nStep 3: Checking for duplicates...')
  const { unique, duplicates } = filterDuplicates(transformed)

  console.log(`  Unique: ${unique.length}`)
  console.log(`  Duplicates: ${duplicates.length}`)

  if (duplicates.length > 0 && options.verbose) {
    console.log('  Duplicate entries:')
    for (const { problem, result } of duplicates) {
      console.log(`    #${problem.number}: ${result.matchReason}`)
    }
  }

  // Step 4: Generate gallery entries (unless research-only)
  if (!options.researchOnly) {
    console.log('\nStep 4: Generating gallery entries (solved problems)...')
    const solvedUnique = unique.filter(p => p.status === 'SOLVED' || p.status === 'PARTIALLY_SOLVED')
    const galleryResults = generateGalleryEntries(solvedUnique, options.dryRun)
    const galleryStats = getGalleryStats(galleryResults)

    stats.galleryCreated = galleryStats.created
    stats.gallerySkipped = galleryStats.skipped

    console.log(`  Created: ${galleryStats.created}`)
    console.log(`  Skipped: ${galleryStats.skipped}`)
  }

  // Step 5: Generate research entries (unless gallery-only)
  if (!options.galleryOnly) {
    console.log('\nStep 5: Generating research entries (open problems)...')
    const openUnique = unique.filter(p => p.status === 'OPEN')
    const researchResults = generateResearchEntries(openUnique, options.dryRun)
    const researchStats = getResearchStats(researchResults)

    stats.researchCreated = researchStats.created
    stats.researchSkipped = researchStats.skipped

    console.log(`  Created: ${researchStats.created}`)
    console.log(`  Skipped: ${researchStats.skipped}`)
  }

  // Step 6: Generate Aristotle candidates
  if (!options.researchOnly) {
    console.log('\nStep 6: Generating Aristotle candidates...')
    const candidates = generateAristotleCandidates(unique, options.dryRun)
    stats.aristotleCandidates = candidates.length

    if (options.verbose) {
      printAristotleReport(candidates)
    }
  }

  return stats
}

/**
 * Print final summary
 */
function printSummary(stats: PipelineStats, options: CliOptions): void {
  console.log('\n=== Pipeline Summary ===')
  console.log(`Total scraped: ${stats.totalScraped}`)
  console.log(`  Open: ${stats.openCount}`)
  console.log(`  Solved: ${stats.solvedCount}`)
  console.log(`  Partially solved: ${stats.partiallySolvedCount}`)

  if (!options.researchOnly) {
    console.log(`Gallery entries: ${stats.galleryCreated} created, ${stats.gallerySkipped} skipped`)
  }
  if (!options.galleryOnly) {
    console.log(`Research entries: ${stats.researchCreated} created, ${stats.researchSkipped} skipped`)
  }
  if (!options.researchOnly) {
    console.log(`Aristotle candidates: ${stats.aristotleCandidates}`)
  }

  if (options.dryRun) {
    console.log('\n** DRY RUN - No files were written **')
    console.log('Run without --dry-run to create files.')
  }
}

/**
 * Main entry point
 */
async function main(): Promise<void> {
  const options = parseArgs()

  if (options.status) {
    showStatus()
    return
  }

  try {
    const stats = await runPipeline(options)
    printSummary(stats, options)
  } catch (error) {
    console.error('Pipeline error:', error)
    process.exit(1)
  }
}

// Run
main().catch(console.error)
