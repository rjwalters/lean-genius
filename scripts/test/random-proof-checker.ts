/**
 * random-proof-checker.ts
 *
 * Playwright script that visits leangenius.org, clicks the random proof dice
 * button N times, and verifies each proof page loads without errors.
 * Failures are reported as GitHub issues (deduplicated).
 *
 * Usage: npx tsx scripts/test/random-proof-checker.ts [--count N] [--url URL]
 */

import { execFileSync } from 'child_process'

// --- CLI args ---
const args = process.argv.slice(2)

if (args.includes('--help') || args.includes('-h')) {
  console.log(`Usage: npx tsx scripts/test/random-proof-checker.ts [options]

Visit leangenius.org, click random proofs, and report broken proof pages.

Options:
  --count N    Number of random proofs to test (default: 20)
  --url URL    Base URL to test (default: https://leangenius.org)
  --help, -h   Show this help message`)
  process.exit(0)
}

function getArg(name: string, fallback: string): string {
  const idx = args.indexOf(name)
  return idx !== -1 && args[idx + 1] ? args[idx + 1] : fallback
}
const COUNT = parseInt(getArg('--count', '20'), 10)
const BASE_URL = getArg('--url', 'https://leangenius.org')

interface TestResult {
  slug: string
  url: string
  ok: boolean
  error?: string
}

interface PageLike {
  url(): string
}

interface ConsoleMessageLike {
  type(): string
  text(): string
}

async function extractSlug(page: PageLike): Promise<string> {
  const url = page.url()
  const match = url.match(/\/proof\/([^/?#]+)/)
  return match ? match[1] : url
}

/** Check if a GitHub issue already exists for this slug */
function issueExists(slug: string): boolean {
  try {
    const out = execFileSync(
      'gh',
      [
        'issue',
        'list',
        '--state',
        'open',
        '--search',
        `[tester] ${slug}`,
        '--json',
        'number',
        '--limit',
        '1',
      ],
      { encoding: 'utf8', timeout: 15000 }
    )
    const issues = JSON.parse(out)
    return issues.length > 0
  } catch {
    return false // if gh fails, allow issue creation
  }
}

/** Open a GitHub issue for a broken proof page */
function fileIssue(result: TestResult, screenshotPath?: string): void {
  if (issueExists(result.slug)) {
    console.log(`  Issue already exists for ${result.slug}, skipping`)
    return
  }

  const body = [
    '## Tester Agent Report',
    '',
    `The random proof checker found an error on proof page **${result.slug}**.`,
    '',
    `**URL**: ${result.url}`,
    `**Error**: ${result.error}`,
    '',
    '### Reproduction',
    '1. Navigate to https://leangenius.org',
    '2. Click the random proof dice button until you reach this proof',
    `3. Or go directly to ${result.url}`,
    '',
    screenshotPath ? `Screenshot attached separately.` : '',
    '',
    '---',
    '*Filed automatically by the tester agent (`scripts/test/random-proof-checker.ts`)*',
  ].join('\n')

  try {
    execFileSync(
      'gh',
      [
        'issue',
        'create',
        '--title',
        `[tester] Proof page broken: ${result.slug}`,
        '--body',
        body,
        '--label',
        'bug',
      ],
      { encoding: 'utf8', timeout: 30000 }
    )
    console.log(`  Filed issue for ${result.slug}`)
  } catch (e) {
    console.error(`  Failed to file issue for ${result.slug}:`, e)
  }
}

async function run(): Promise<void> {
  console.log(`Testing ${COUNT} random proofs on ${BASE_URL}`)

  const { chromium } = await import('playwright')
  const browser = await chromium.launch({ headless: true })
  const context = await browser.newContext({
    viewport: { width: 1280, height: 720 },
  })
  const page = await context.newPage()

  // Collect console errors
  const consoleErrors: string[] = []
  page.on('console', (msg: ConsoleMessageLike) => {
    if (msg.type() === 'error') {
      consoleErrors.push(msg.text())
    }
  })

  // Track failed network requests
  const networkErrors: string[] = []
  page.on('requestfailed', (req: { url(): string; failure(): { errorText?: string } | null }) => {
    networkErrors.push(`${req.url()} - ${req.failure()?.errorText ?? 'unknown'}`)
  })

  const results: TestResult[] = []

  // Navigate to home page
  console.log(`Navigating to ${BASE_URL}...`)
  await page.goto(BASE_URL, { waitUntil: 'networkidle', timeout: 30000 })

  for (let i = 0; i < COUNT; i++) {
    consoleErrors.length = 0
    networkErrors.length = 0

    // Click the dice button (title="Random proof")
    const diceButton = page.locator('button[title="Random proof"]')
    if (!(await diceButton.isVisible({ timeout: 5000 }).catch(() => false))) {
      // If not on home page (e.g., on a proof page), go back first
      await page.goto(BASE_URL, { waitUntil: 'networkidle', timeout: 30000 })
    }

    await diceButton.click()

    // Wait for navigation to complete
    try {
      await page.waitForURL(/\/proof\//, { timeout: 10000 })
      await page.waitForLoadState('networkidle', { timeout: 15000 })
    } catch {
      const slug = await extractSlug(page)
      results.push({
        slug,
        url: page.url(),
        ok: false,
        error: 'Navigation timeout: page did not load within 15s',
      })
      console.log(`  [${i + 1}/${COUNT}] FAIL ${slug} - navigation timeout`)
      continue
    }

    const slug = await extractSlug(page)
    const url = page.url()

    // Check for error states in page content
    const errorText = await page
      .locator('text=/Error Loading Proof|Proof not found|Something went wrong/')
      .first()
      .textContent({ timeout: 2000 })
      .catch(() => null)

    if (errorText) {
      results.push({ slug, url, ok: false, error: `Page error: ${errorText}` })
      console.log(`  [${i + 1}/${COUNT}] FAIL ${slug} - ${errorText}`)
      continue
    }

    // Check for console errors (ignore benign ones)
    const significantErrors = consoleErrors.filter(
      (e) => !e.includes('favicon') && !e.includes('analytics')
    )

    if (significantErrors.length > 0) {
      results.push({
        slug,
        url,
        ok: false,
        error: `Console errors: ${significantErrors.join('; ')}`,
      })
      console.log(`  [${i + 1}/${COUNT}] FAIL ${slug} - console errors`)
      continue
    }

    // Check for network failures on the proof page (ignore external)
    const significantNetworkErrors = networkErrors.filter(
      (e) => e.includes('leangenius.org') || e.includes('localhost')
    )

    if (significantNetworkErrors.length > 0) {
      results.push({
        slug,
        url,
        ok: false,
        error: `Network errors: ${significantNetworkErrors.join('; ')}`,
      })
      console.log(`  [${i + 1}/${COUNT}] FAIL ${slug} - network errors`)
      continue
    }

    results.push({ slug, url, ok: true })
    console.log(`  [${i + 1}/${COUNT}] OK   ${slug}`)

    // Navigate back to home for next dice click
    await page.goto(BASE_URL, { waitUntil: 'networkidle', timeout: 30000 })
  }

  await browser.close()

  // Summary
  const passed = results.filter((r) => r.ok).length
  const failed = results.filter((r) => !r.ok).length

  console.log('')
  console.log(`Results: ${passed} passed, ${failed} failed out of ${results.length} tested`)

  // File issues for failures
  if (failed > 0) {
    console.log('')
    console.log('Filing issues for failures...')
    for (const result of results.filter((r) => !r.ok)) {
      fileIssue(result)
    }
  }

  // Exit with non-zero if any failures
  process.exit(failed > 0 ? 1 : 0)
}

run().catch((err) => {
  console.error('Fatal error:', err)
  process.exit(2)
})
