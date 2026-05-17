/**
 * Update research problem files that have "Problem statement not found"
 *
 * Scrapes erdosproblems.com for each missing problem statement and updates
 * the research JSON files in-place.
 */

import * as fs from 'fs'
import * as path from 'path'

const RESEARCH_DIR = 'src/data/research/problems'

function printUsage() {
  console.log(`Usage: npx tsx scripts/erdos/update-missing-statements.ts [options]

Update Erdős research problem files whose statement is missing.

Options:
  --dry-run     List files that would be updated without scraping or writing
  --playwright  Use Playwright-backed scraping for update runs
  --help        Show this help message
  -h            Show this help message`)
}

interface ResearchProblem {
  slug: string
  title: string
  problemStatement: {
    formal: string
    plain: string
    whyMatters: string[]
  }
  knowledge?: {
    markdown?: string
    [key: string]: unknown
  }
  tags?: string[]
  [key: string]: unknown
}

async function main() {
  const args = process.argv.slice(2)
  if (args.includes('--help') || args.includes('-h')) {
    printUsage()
    return
  }

  const usePlaywright = args.includes('--playwright')
  const dryRun = args.includes('--dry-run')

  // Find all research files with missing statements
  const researchDir = path.resolve(process.cwd(), RESEARCH_DIR)
  const files = fs.readdirSync(researchDir).filter(f => f.startsWith('erdos-') && f.endsWith('.json'))

  const missing: Array<{ file: string; number: number }> = []

  for (const file of files) {
    const filePath = path.join(researchDir, file)
    const data: ResearchProblem = JSON.parse(fs.readFileSync(filePath, 'utf-8'))

    if (data.problemStatement?.plain === 'Problem statement not found' ||
        data.problemStatement?.plain === '' ||
        !data.problemStatement?.plain) {
      const numMatch = file.match(/erdos-(\d+)\.json/)
      if (numMatch) {
        missing.push({ file, number: parseInt(numMatch[1]) })
      }
    }
  }

  console.log(`Found ${missing.length} research files with missing statements`)

  if (missing.length === 0) {
    console.log('Nothing to update!')
    return
  }

  if (dryRun) {
    console.log('\nDry run - would update:')
    for (const m of missing) {
      console.log(`  ${m.file} (erdos #${m.number})`)
    }
    return
  }

  const { scrapeProblem } = await import('./scrape')

  let updated = 0
  let failed = 0
  let solved = 0

  for (let i = 0; i < missing.length; i++) {
    const { file, number } = missing[i]
    console.log(`\n[${i + 1}/${missing.length}] Scraping problem #${number}...`)

    const scraped = await scrapeProblem(number, undefined, true, usePlaywright)

    if (!scraped) {
      console.log(`  FAILED: Could not scrape problem #${number}`)
      failed++
      continue
    }

    const statement = scraped.statement.html
    if (statement === 'Problem statement not found' || statement.length < 20) {
      console.log(`  FAILED: Statement too short or not found for #${number}`)
      failed++
      continue
    }

    // Read the research file
    const filePath = path.join(researchDir, file)
    const data: ResearchProblem = JSON.parse(fs.readFileSync(filePath, 'utf-8'))

    // Update the problem statement
    data.problemStatement.plain = statement
    if (scraped.statement.latex) {
      data.problemStatement.formal = scraped.statement.latex
    }

    // Update the title if it's generic
    if (data.title === `Erdős #${number}`) {
      data.title = scraped.title !== `Problem #${number}`
        ? `Erdős #${number}: ${scraped.title}`
        : data.title
    }

    // Update tags if empty
    if ((!data.tags || data.tags.length <= 1) && scraped.tags.length > 0) {
      data.tags = ['erdos', ...scraped.tags]
    }

    // Update the knowledge markdown if it references "Problem statement not found"
    if (data.knowledge?.markdown && typeof data.knowledge.markdown === 'string') {
      data.knowledge.markdown = data.knowledge.markdown.replace(
        /## Problem Statement\n\nProblem statement not found/,
        `## Problem Statement\n\n${statement}`
      )
    }

    // Track if this is a solved problem
    if (scraped.status === 'SOLVED') {
      solved++
      console.log(`  NOTE: Problem #${number} is SOLVED - may need gallery entry`)
    }

    // Write updated file
    fs.writeFileSync(filePath, JSON.stringify(data, null, 2) + '\n')
    console.log(`  Updated: ${statement.slice(0, 80)}...`)
    updated++
  }

  console.log(`\n=== Summary ===`)
  console.log(`Updated: ${updated}`)
  console.log(`Failed:  ${failed}`)
  console.log(`Solved (may need gallery): ${solved}`)
}

main().catch(console.error)
