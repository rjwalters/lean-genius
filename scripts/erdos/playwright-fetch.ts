/**
 * Playwright-based fetcher for erdosproblems.com
 *
 * Uses a real browser to avoid rate limiting that targets automated HTTP requests.
 * Simulates human-like browsing behavior with random delays.
 */

import { chromium, type Browser, type BrowserContext, type Page } from 'playwright'

let browser: Browser | null = null
let context: BrowserContext | null = null
let page: Page | null = null

const BASE_URL = 'https://erdosproblems.com'

/**
 * Random delay between min and max milliseconds
 */
function randomDelay(min: number, max: number): Promise<void> {
  const delay = Math.floor(Math.random() * (max - min + 1)) + min
  return new Promise(resolve => setTimeout(resolve, delay))
}

/**
 * Initialize the browser if not already running
 */
async function ensureBrowser(): Promise<Page> {
  if (!browser) {
    console.log('  Launching browser...')
    browser = await chromium.launch({
      headless: true,
    })

    context = await browser.newContext({
      userAgent: 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
      viewport: { width: 1280, height: 720 },
      locale: 'en-US',
    })

    page = await context.newPage()

    // Navigate to homepage first to establish session
    await page.goto(BASE_URL, { waitUntil: 'domcontentloaded' })
    await randomDelay(1000, 2000)
  }

  return page!
}

/**
 * Close the browser
 */
export async function closeBrowser(): Promise<void> {
  if (browser) {
    await browser.close()
    browser = null
    context = null
    page = null
  }
}

/**
 * Fetch a problem page using Playwright
 */
export async function fetchWithPlaywright(
  problemNumber: number
): Promise<{ html: string; status: number } | null> {
  const browserPage = await ensureBrowser()
  const url = `${BASE_URL}/${problemNumber}`

  try {
    // Random delay before navigation (3-8 seconds)
    await randomDelay(3000, 8000)

    const response = await browserPage.goto(url, {
      waitUntil: 'domcontentloaded',
      timeout: 30000,
    })

    if (!response) {
      console.log(`  Problem #${problemNumber}: No response`)
      return null
    }

    const status = response.status()

    if (status === 404) {
      console.log(`  Problem #${problemNumber}: Not found (404)`)
      return { html: '', status: 404 }
    }

    if (status === 429) {
      console.log(`  Problem #${problemNumber}: Rate limited (429), waiting 60s...`)
      await randomDelay(60000, 90000)
      // Retry once
      const retryResponse = await browserPage.goto(url, {
        waitUntil: 'domcontentloaded',
        timeout: 30000,
      })
      if (!retryResponse || retryResponse.status() !== 200) {
        return null
      }
    }

    if (status !== 200) {
      console.log(`  Problem #${problemNumber}: HTTP ${status}`)
      return null
    }

    // Wait for content to load
    await browserPage.waitForSelector('#content', { timeout: 10000 }).catch(() => {})

    // Small delay to let any JS finish
    await randomDelay(500, 1500)

    const html = await browserPage.content()
    return { html, status: 200 }

  } catch (error) {
    console.log(`  Problem #${problemNumber}: Error - ${(error as Error).message}`)
    return null
  }
}

/**
 * Fetch LaTeX for a problem using Playwright
 */
export async function fetchLatexWithPlaywright(
  problemNumber: number
): Promise<string | null> {
  const browserPage = await ensureBrowser()
  const url = `${BASE_URL}/latex/${problemNumber}`

  try {
    // Random delay before navigation (2-5 seconds)
    await randomDelay(2000, 5000)

    const response = await browserPage.goto(url, {
      waitUntil: 'domcontentloaded',
      timeout: 30000,
    })

    if (!response || response.status() !== 200) {
      return null
    }

    // Wait a bit for content
    await randomDelay(500, 1000)

    // Get the page text content (LaTeX pages are plain text)
    const content = await browserPage.evaluate(() => document.body.innerText || document.body.textContent || '')

    // Validate it's actually LaTeX, not HTML
    if (content.startsWith('<!DOCTYPE') || content.startsWith('<html')) {
      return null
    }

    return content.trim() || null

  } catch {
    return null
  }
}
