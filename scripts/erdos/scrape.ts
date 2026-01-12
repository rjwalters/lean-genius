/**
 * Scraper for erdosproblems.com
 *
 * Fetches problem pages and parses HTML to extract:
 * - Problem number and title
 * - Status (OPEN/SOLVED/PARTIALLY_SOLVED)
 * - Mathematical statement (HTML and LaTeX)
 * - Tags, related problems, references
 * - Prize amount if any
 */

import type { ScrapedProblem, ScrapedStatus } from './types'
import {
  getCachedHtml,
  getCachedLatex,
  cacheHtml,
  cacheLatex,
  rateLimitedFetch,
  type CacheConfig,
} from './cache'
import {
  fetchWithPlaywright,
  fetchLatexWithPlaywright,
  closeBrowser,
} from './playwright-fetch'

const BASE_URL = 'https://erdosproblems.com'

export interface ScrapeOptions {
  config?: CacheConfig
  useCache?: boolean
  usePlaywright?: boolean
}

/**
 * Extract problem number from URL or page content
 */
function extractNumber(html: string, url: string): number {
  // Try to get from URL first
  const urlMatch = url.match(/\/(\d+)$/)
  if (urlMatch) {
    return parseInt(urlMatch[1])
  }

  // Try to find in page content
  const headerMatch = html.match(/#(\d+)/i)
  if (headerMatch) {
    return parseInt(headerMatch[1])
  }

  throw new Error(`Could not extract problem number from ${url}`)
}

/**
 * Extract problem title from page content
 */
function extractTitle(html: string, problemNumber: number): string {
  // Look for title patterns like "Problem #N:" or just use a generic title
  // The actual title is often the problem statement itself (first sentence)
  const statementMatch = html.match(/(?:problem\s*statement|statement)[:\s]*([^.]+\.)/i)
  if (statementMatch) {
    return statementMatch[1].trim().slice(0, 100)
  }

  // Try to extract from the main content
  const mainMatch = html.match(/If\s+\$[^$]+\$[^.]+\./i)
  if (mainMatch) {
    return mainMatch[0].slice(0, 100).replace(/\$[^$]+\$/g, '...').trim()
  }

  return `Problem #${problemNumber}`
}

/**
 * Extract problem status (OPEN, SOLVED, PARTIALLY_SOLVED)
 *
 * The site uses specific status badges at the beginning:
 * - "OPEN This is open..."
 * - "PROVED This has been solved in the affirmative..."
 * - "DISPROVED This has been solved in the negative..."
 */
function extractStatus(html: string): ScrapedStatus {
  // Look for the status badge patterns at the start of content
  // These appear prominently on each problem page

  // PROVED or DISPROVED = SOLVED
  if (/\bPROVED\b/i.test(html) || /\bDISPROVED\b/i.test(html)) {
    return 'SOLVED'
  }

  // Check for "solved in the affirmative/negative" which indicates resolved
  if (/solved in the (affirmative|negative)/i.test(html)) {
    return 'SOLVED'
  }

  // Check for "this has been resolved"
  if (/this has been resolved/i.test(html)) {
    return 'SOLVED'
  }

  // PARTIALLY SOLVED
  if (/partially\s*(solved|resolved)/i.test(html)) {
    return 'PARTIALLY_SOLVED'
  }

  // OPEN is the default and most common status
  // The site shows "OPEN This is open, and cannot be resolved..."
  return 'OPEN'
}

/**
 * Extract prize amount if any
 */
function extractPrize(html: string): string | undefined {
  // Look for dollar amounts like $500, $5000, $10,000
  const prizeMatch = html.match(/\$[\d,]+/g)
  if (prizeMatch && prizeMatch.length > 0) {
    // Return the first (usually the prize) unless it looks like math notation
    for (const match of prizeMatch) {
      const amount = parseInt(match.replace(/[$,]/g, ''))
      if (amount >= 25 && amount <= 1000000) {
        return match
      }
    }
  }
  return undefined
}

/**
 * Extract tags from the page
 */
function extractTags(html: string): string[] {
  const tags: string[] = []

  // Look for tag links like [number theory](/tags/number theory)
  const tagLinkMatches = html.matchAll(/\[([^\]]+)\]\(\/tags\/[^)]+\)/g)
  for (const match of tagLinkMatches) {
    const tag = match[1].toLowerCase().trim()
    if (tag && !tags.includes(tag)) {
      tags.push(tag)
    }
  }

  // Also look for explicit tag mentions
  const tagPatterns = [
    /tags?:\s*([^.\n]+)/i,
    /categories?:\s*([^.\n]+)/i,
  ]
  for (const pattern of tagPatterns) {
    const match = html.match(pattern)
    if (match) {
      const tagList = match[1].split(/[,;]/).map(t => t.trim().toLowerCase())
      for (const tag of tagList) {
        if (tag && !tags.includes(tag)) {
          tags.push(tag)
        }
      }
    }
  }

  return tags
}

/**
 * Extract related problem numbers
 */
function extractRelatedProblems(html: string, currentNumber: number): number[] {
  const related: number[] = []

  // Look for problem references like [123] or #123 or /123
  const problemRefs = html.matchAll(/(?:\[(\d+)\]|#(\d+)(?!\d)|\/(\d+)(?!\d))/g)
  for (const match of problemRefs) {
    const num = parseInt(match[1] || match[2] || match[3])
    if (num && num !== currentNumber && num >= 1 && num <= 2000 && !related.includes(num)) {
      related.push(num)
    }
  }

  // Also look for explicit "related problems" or "see also" sections
  const relatedMatch = html.match(/(?:related|see also)[:\s]*([^.]+)/i)
  if (relatedMatch) {
    const nums = relatedMatch[1].match(/\d+/g)
    if (nums) {
      for (const n of nums) {
        const num = parseInt(n)
        if (num && num !== currentNumber && num >= 1 && num <= 2000 && !related.includes(num)) {
          related.push(num)
        }
      }
    }
  }

  return related.slice(0, 20) // Limit to 20 related problems
}

/**
 * Extract references/citations
 */
function extractReferences(html: string): Array<{ key: string; citation?: string }> {
  const refs: Array<{ key: string; citation?: string }> = []
  const seen = new Set<string>()

  // Look for citation keys like [Er56], [Er95], etc.
  const citationMatches = html.matchAll(/\[([A-Z][a-zA-Z]+\d+[a-z]?)\]/g)
  for (const match of citationMatches) {
    const key = match[1]
    if (!seen.has(key)) {
      seen.add(key)
      refs.push({ key })
    }
  }

  return refs.slice(0, 50) // Limit to 50 references
}

/**
 * Extract OEIS sequence numbers
 */
function extractOEIS(html: string): string[] {
  const oeis: string[] = []

  // Look for OEIS references like A123456 or oeis.org/A123456
  const oeisMatches = html.matchAll(/(?:oeis\.org\/)?([A-Z]\d{6})/gi)
  for (const match of oeisMatches) {
    const seq = match[1].toUpperCase()
    if (!oeis.includes(seq)) {
      oeis.push(seq)
    }
  }

  return oeis
}

/**
 * Extract the last edited date
 */
function extractLastEdited(html: string): string | undefined {
  const datePatterns = [
    /last\s+edited[:\s]*(\d{1,2}\s+\w+\s+\d{4})/i,
    /edited[:\s]*(\d{1,2}\s+\w+\s+\d{4})/i,
    /(\d{1,2}\s+\w+\s+\d{4})/i,
  ]

  for (const pattern of datePatterns) {
    const match = html.match(pattern)
    if (match) {
      return match[1]
    }
  }

  return undefined
}

/**
 * Extract the actual problem statement from HTML
 *
 * The problem text is in: <div id="content">...</div>
 * Additional context is in: <div class="problem-additional-text">...</div>
 */
function extractProblemStatement(html: string): string {
  // First try to extract from the content div
  const contentMatch = html.match(/<div[^>]*id="content"[^>]*>([\s\S]*?)<\/div>/i)
  let statement = ''

  if (contentMatch) {
    statement = contentMatch[1]
  }

  // Also try to get additional context from problem-additional-text
  const additionalMatch = html.match(/<div[^>]*class="problem-additional-text"[^>]*>([\s\S]*?)<\/div>/i)
  if (additionalMatch && additionalMatch[1].length < 2000) {
    // Add the additional context if it's not too long
    const additional = additionalMatch[1].trim()
    if (additional && !additional.includes('<h3>References</h3>')) {
      statement += '\n\n' + additional
    }
  }

  if (!statement) {
    // Fallback: try to extract any content between problem-box divs
    const boxMatch = html.match(/<div[^>]*class="problem-text"[^>]*>([\s\S]*?)<\/div>/i)
    if (boxMatch) {
      statement = boxMatch[1]
    }
  }

  // Clean up HTML entities and tags
  statement = statement
    .replace(/&#(\d+);/g, (_, code) => String.fromCharCode(parseInt(code)))
    .replace(/&gt;/g, '>')
    .replace(/&lt;/g, '<')
    .replace(/&amp;/g, '&')
    .replace(/&quot;/g, '"')
    .replace(/<br\s*\/?>/gi, '\n')
    .replace(/<a[^>]*>([^<]*)<\/a>/gi, '$1')
    .replace(/<[^>]+>/g, '')
    .replace(/\{UL\}|\{\/UL\}|\{LI\}|\{\/LI\}/gi, '')
    .replace(/\s+/g, ' ')
    .trim()

  return statement || 'Problem statement not found'
}

/**
 * Clean HTML content for the statement (legacy, returns full HTML)
 */
function cleanStatementHtml(html: string): string {
  // Remove script and style tags
  let cleaned = html.replace(/<script[^>]*>[\s\S]*?<\/script>/gi, '')
  cleaned = cleaned.replace(/<style[^>]*>[\s\S]*?<\/style>/gi, '')

  // Remove HTML comments
  cleaned = cleaned.replace(/<!--[\s\S]*?-->/g, '')

  // Remove excess whitespace
  cleaned = cleaned.replace(/\s+/g, ' ').trim()

  return cleaned
}

/**
 * Scrape a single problem
 */
export async function scrapeProblem(
  problemNumber: number,
  config?: CacheConfig,
  useCache = true,
  usePlaywright = false
): Promise<ScrapedProblem | null> {
  const url = `${BASE_URL}/${problemNumber}`

  // Check cache first
  let html = useCache ? getCachedHtml(problemNumber, config) : null
  let latex = useCache ? getCachedLatex(problemNumber, config) : null

  // Fetch if not cached
  if (!html) {
    if (usePlaywright) {
      // Use Playwright browser
      const result = await fetchWithPlaywright(problemNumber)
      if (!result) {
        return null
      }
      if (result.status === 404) {
        console.log(`  Problem #${problemNumber} not found (404)`)
        return null
      }
      html = result.html
      cacheHtml(problemNumber, html, result.status, config)
    } else {
      // Use fetch API
      try {
        const response = await rateLimitedFetch(url, config)

        if (response.status === 404) {
          console.log(`  Problem #${problemNumber} not found (404)`)
          return null
        }

        if (!response.ok) {
          console.log(`  Problem #${problemNumber} fetch failed: ${response.status}`)
          return null
        }

        html = await response.text()
        cacheHtml(problemNumber, html, response.status, config)
      } catch (error) {
        console.error(`  Error fetching problem #${problemNumber}:`, error)
        return null
      }
    }
  }

  // Fetch LaTeX if not cached
  if (!latex) {
    if (usePlaywright) {
      // Use Playwright browser
      const latexContent = await fetchLatexWithPlaywright(problemNumber)
      if (latexContent) {
        latex = latexContent
        cacheLatex(problemNumber, latex, config)
      }
    } else {
      // Use fetch API
      try {
        const latexUrl = `${BASE_URL}/latex/${problemNumber}`
        const response = await rateLimitedFetch(latexUrl, config)

        if (response.ok) {
          const latexContent = await response.text()
          // Validate that it's actually LaTeX, not HTML
          // The /latex endpoint sometimes returns HTML pages instead of LaTeX
          if (!latexContent.startsWith('<!DOCTYPE') && !latexContent.startsWith('<html')) {
            latex = latexContent
            cacheLatex(problemNumber, latex, config)
          }
        }
      } catch (error) {
        // LaTeX is optional, don't fail on this
        console.log(`  Could not fetch LaTeX for problem #${problemNumber}`)
      }
    }
  }

  // If cached latex is actually HTML, ignore it
  if (latex && (latex.startsWith('<!DOCTYPE') || latex.startsWith('<html'))) {
    latex = null
  }

  // Parse the HTML
  try {
    const number = extractNumber(html, url)
    const title = extractTitle(html, number)
    const status = extractStatus(html)
    const prize = extractPrize(html)
    const tags = extractTags(html)
    const relatedProblems = extractRelatedProblems(html, number)
    const references = extractReferences(html)
    const oeis = extractOEIS(html)
    const lastEdited = extractLastEdited(html)

    return {
      number,
      title,
      status,
      prize,
      statement: {
        latex: latex || '',
        html: extractProblemStatement(html),
      },
      tags,
      relatedProblems,
      references,
      lastEdited,
      oeis: oeis.length > 0 ? oeis : undefined,
      sourceUrl: url,
    }
  } catch (error) {
    console.error(`  Error parsing problem #${problemNumber}:`, error)
    return null
  }
}

/**
 * Scrape a list of specific problem numbers
 */
export async function scrapeProblems(
  numbers: number[],
  config?: CacheConfig,
  useCache = true,
  onProgress?: (current: number, total: number, problem: ScrapedProblem | null) => void,
  usePlaywright = false
): Promise<ScrapedProblem[]> {
  const problems: ScrapedProblem[] = []
  const total = numbers.length

  if (total === 0) {
    console.log('No problems to scrape.')
    return problems
  }

  console.log(`Scraping ${total} problems: #${numbers[0]}-${numbers[numbers.length - 1]}...`)

  try {
    for (let i = 0; i < numbers.length; i++) {
      const num = numbers[i]
      const problem = await scrapeProblem(num, config, useCache, usePlaywright)

      if (problem) {
        problems.push(problem)
      }

      if (onProgress) {
        onProgress(i + 1, total, problem)
      }

      // Progress indicator every 10 problems
      if ((i + 1) % 10 === 0) {
        const pct = Math.round(((i + 1) / total) * 100)
        console.log(`  Progress: ${i + 1}/${total} (${pct}%)`)
      }
    }
  } finally {
    // Close browser if using Playwright
    if (usePlaywright) {
      await closeBrowser()
    }
  }

  console.log(`Scraped ${problems.length} problems successfully`)
  return problems
}

/**
 * Scrape a range of problems
 */
export async function scrapeRange(
  start: number,
  end: number,
  config?: CacheConfig,
  useCache = true,
  onProgress?: (current: number, total: number, problem: ScrapedProblem | null) => void,
  usePlaywright = false
): Promise<ScrapedProblem[]> {
  const numbers: number[] = []
  for (let i = start; i <= end; i++) {
    numbers.push(i)
  }
  return scrapeProblems(numbers, config, useCache, onProgress, usePlaywright)
}

/**
 * Scrape all known problems (1-1200 to cover gaps)
 */
export async function scrapeAll(
  config?: CacheConfig,
  useCache = true,
  onProgress?: (current: number, total: number, problem: ScrapedProblem | null) => void,
  usePlaywright = false
): Promise<ScrapedProblem[]> {
  return scrapeRange(1, 1200, config, useCache, onProgress, usePlaywright)
}

/**
 * Get summary statistics from scraped problems
 */
export function getScrapeStats(problems: ScrapedProblem[]): {
  total: number
  open: number
  solved: number
  partiallySolved: number
  withPrize: number
  totalPrizeValue: number
  uniqueTags: string[]
} {
  const tagSet = new Set<string>()
  let totalPrize = 0

  for (const p of problems) {
    for (const tag of p.tags) {
      tagSet.add(tag)
    }
    if (p.prize) {
      const amount = parseInt(p.prize.replace(/[$,]/g, ''))
      if (!isNaN(amount)) {
        totalPrize += amount
      }
    }
  }

  return {
    total: problems.length,
    open: problems.filter(p => p.status === 'OPEN').length,
    solved: problems.filter(p => p.status === 'SOLVED').length,
    partiallySolved: problems.filter(p => p.status === 'PARTIALLY_SOLVED').length,
    withPrize: problems.filter(p => p.prize).length,
    totalPrizeValue: totalPrize,
    uniqueTags: Array.from(tagSet).sort(),
  }
}
