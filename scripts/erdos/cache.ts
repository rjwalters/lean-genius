/**
 * Rate-limited caching layer for erdosproblems.com scraping
 */

import * as fs from 'fs'
import * as path from 'path'
import type { CacheEntry, CacheManifest } from './types'

const CACHE_DIR = '.erdos-cache'
const MANIFEST_FILE = 'manifest.json'
const DEFAULT_MAX_AGE_HOURS = 24
const DEFAULT_REQUEST_DELAY_MS = 5000  // 5 seconds between requests
const DEFAULT_MAX_RETRIES = 5
const BATCH_SIZE = 10

export interface CacheConfig {
  cacheDir: string
  maxAgeHours: number
  requestDelayMs: number
  maxRetries: number
  batchSize: number
}

const defaultConfig: CacheConfig = {
  cacheDir: CACHE_DIR,
  maxAgeHours: DEFAULT_MAX_AGE_HOURS,
  requestDelayMs: DEFAULT_REQUEST_DELAY_MS,
  maxRetries: DEFAULT_MAX_RETRIES,
  batchSize: BATCH_SIZE,
}

/**
 * Sleep for specified milliseconds
 */
function sleep(ms: number): Promise<void> {
  return new Promise(resolve => setTimeout(resolve, ms))
}

/**
 * Get the cache directory path
 */
function getCacheDir(config: CacheConfig = defaultConfig): string {
  return path.resolve(process.cwd(), config.cacheDir)
}

/**
 * Ensure cache directory exists
 */
export function ensureCacheDir(config: CacheConfig = defaultConfig): void {
  const cacheDir = getCacheDir(config)
  if (!fs.existsSync(cacheDir)) {
    fs.mkdirSync(cacheDir, { recursive: true })
  }
}

/**
 * Get the manifest path
 */
function getManifestPath(config: CacheConfig = defaultConfig): string {
  return path.join(getCacheDir(config), MANIFEST_FILE)
}

/**
 * Load the cache manifest
 */
export function loadManifest(config: CacheConfig = defaultConfig): CacheManifest {
  const manifestPath = getManifestPath(config)
  if (fs.existsSync(manifestPath)) {
    try {
      const content = fs.readFileSync(manifestPath, 'utf-8')
      return JSON.parse(content)
    } catch {
      // Corrupted manifest, start fresh
    }
  }
  return {
    version: '1.0.0',
    lastUpdate: new Date().toISOString(),
    entries: {},
  }
}

/**
 * Save the cache manifest
 */
export function saveManifest(manifest: CacheManifest, config: CacheConfig = defaultConfig): void {
  ensureCacheDir(config)
  const manifestPath = getManifestPath(config)
  manifest.lastUpdate = new Date().toISOString()
  fs.writeFileSync(manifestPath, JSON.stringify(manifest, null, 2))
}

/**
 * Get cached HTML for a problem
 */
export function getCachedHtml(problemNumber: number, config: CacheConfig = defaultConfig): string | null {
  const manifest = loadManifest(config)
  const entry = manifest.entries[problemNumber]

  if (!entry) return null

  // Check if cache is expired
  const fetchedAt = new Date(entry.fetchedAt)
  const maxAge = config.maxAgeHours * 60 * 60 * 1000
  if (Date.now() - fetchedAt.getTime() > maxAge) {
    return null
  }

  const cachePath = path.join(getCacheDir(config), `${problemNumber}.html`)
  if (fs.existsSync(cachePath)) {
    return fs.readFileSync(cachePath, 'utf-8')
  }

  return null
}

/**
 * Get cached LaTeX for a problem
 */
export function getCachedLatex(problemNumber: number, config: CacheConfig = defaultConfig): string | null {
  const manifest = loadManifest(config)
  const entry = manifest.entries[problemNumber]

  if (!entry || !entry.hasLatex) return null

  // Check if cache is expired
  const fetchedAt = new Date(entry.fetchedAt)
  const maxAge = config.maxAgeHours * 60 * 60 * 1000
  if (Date.now() - fetchedAt.getTime() > maxAge) {
    return null
  }

  const cachePath = path.join(getCacheDir(config), `${problemNumber}.latex`)
  if (fs.existsSync(cachePath)) {
    return fs.readFileSync(cachePath, 'utf-8')
  }

  return null
}

/**
 * Cache HTML for a problem
 */
export function cacheHtml(
  problemNumber: number,
  html: string,
  status: number,
  config: CacheConfig = defaultConfig
): void {
  ensureCacheDir(config)

  const cachePath = path.join(getCacheDir(config), `${problemNumber}.html`)
  fs.writeFileSync(cachePath, html)

  const manifest = loadManifest(config)
  const existing = manifest.entries[problemNumber] || { number: problemNumber, hasLatex: false }
  manifest.entries[problemNumber] = {
    ...existing,
    number: problemNumber,
    fetchedAt: new Date().toISOString(),
    status,
  }
  saveManifest(manifest, config)
}

/**
 * Cache LaTeX for a problem
 */
export function cacheLatex(
  problemNumber: number,
  latex: string,
  config: CacheConfig = defaultConfig
): void {
  ensureCacheDir(config)

  const cachePath = path.join(getCacheDir(config), `${problemNumber}.latex`)
  fs.writeFileSync(cachePath, latex)

  const manifest = loadManifest(config)
  if (manifest.entries[problemNumber]) {
    manifest.entries[problemNumber].hasLatex = true
    saveManifest(manifest, config)
  }
}

/**
 * Fetch with retry and exponential backoff
 */
export async function fetchWithRetry(
  url: string,
  config: CacheConfig = defaultConfig
): Promise<Response> {
  let lastError: Error | null = null

  for (let attempt = 0; attempt < config.maxRetries; attempt++) {
    try {
      const response = await fetch(url)

      // Handle rate limiting (429) with exponential backoff
      if (response.status === 429) {
        // Start at 10s and double each time: 10s, 20s, 40s, 80s, 160s
        const delay = 10000 * Math.pow(2, attempt)
        console.log(`  Rate limited (429), waiting ${delay / 1000}s before retry...`)
        await sleep(delay)
        continue
      }

      return response
    } catch (error) {
      lastError = error as Error
      const delay = config.requestDelayMs * Math.pow(2, attempt)
      console.log(`  Retry ${attempt + 1}/${config.maxRetries} after ${delay}ms...`)
      await sleep(delay)
    }
  }

  throw lastError || new Error(`Failed to fetch ${url} after ${config.maxRetries} attempts`)
}

/**
 * Rate-limited fetch that respects delay between requests
 */
let lastFetchTime = 0

export async function rateLimitedFetch(
  url: string,
  config: CacheConfig = defaultConfig
): Promise<Response> {
  const now = Date.now()
  const timeSinceLastFetch = now - lastFetchTime

  if (timeSinceLastFetch < config.requestDelayMs) {
    await sleep(config.requestDelayMs - timeSinceLastFetch)
  }

  lastFetchTime = Date.now()
  return fetchWithRetry(url, config)
}

/**
 * Process problems in batches with rate limiting
 */
export async function processBatch<T>(
  items: T[],
  processor: (item: T) => Promise<void>,
  config: CacheConfig = defaultConfig
): Promise<void> {
  for (let i = 0; i < items.length; i += config.batchSize) {
    const batch = items.slice(i, i + config.batchSize)

    // Process batch items with rate limiting between each
    for (const item of batch) {
      await processor(item)
    }

    // Small delay between batches
    if (i + config.batchSize < items.length) {
      await sleep(config.requestDelayMs)
    }
  }
}

/**
 * Get cache statistics
 */
export function getCacheStats(config: CacheConfig = defaultConfig): {
  totalCached: number
  withLatex: number
  oldestEntry: string | null
  newestEntry: string | null
} {
  const manifest = loadManifest(config)
  const entries = Object.values(manifest.entries)

  if (entries.length === 0) {
    return {
      totalCached: 0,
      withLatex: 0,
      oldestEntry: null,
      newestEntry: null,
    }
  }

  const sorted = entries.sort((a, b) =>
    new Date(a.fetchedAt).getTime() - new Date(b.fetchedAt).getTime()
  )

  return {
    totalCached: entries.length,
    withLatex: entries.filter(e => e.hasLatex).length,
    oldestEntry: sorted[0].fetchedAt,
    newestEntry: sorted[sorted.length - 1].fetchedAt,
  }
}

/**
 * Get list of cached problem numbers
 */
export function getCachedProblemNumbers(config: CacheConfig = defaultConfig): number[] {
  const manifest = loadManifest(config)
  return Object.keys(manifest.entries).map(n => parseInt(n)).sort((a, b) => a - b)
}

/**
 * Find the next batch of uncached problems
 * Returns array of problem numbers that haven't been cached yet
 */
export function getNextUncachedBatch(
  batchSize: number,
  maxProblem = 1200,
  config: CacheConfig = defaultConfig
): number[] {
  const cached = new Set(getCachedProblemNumbers(config))
  const batch: number[] = []

  for (let i = 1; i <= maxProblem && batch.length < batchSize; i++) {
    if (!cached.has(i)) {
      batch.push(i)
    }
  }

  return batch
}

/**
 * Get progress summary
 */
export function getProgressSummary(maxProblem = 1200, config: CacheConfig = defaultConfig): {
  cached: number
  remaining: number
  total: number
  percentComplete: number
  nextBatch: number[]
} {
  const cached = getCachedProblemNumbers(config)
  const nextBatch = getNextUncachedBatch(10, maxProblem, config)

  return {
    cached: cached.length,
    remaining: maxProblem - cached.length,
    total: maxProblem,
    percentComplete: Math.round((cached.length / maxProblem) * 100),
    nextBatch,
  }
}

/**
 * Clear expired cache entries
 */
export function clearExpiredCache(config: CacheConfig = defaultConfig): number {
  const manifest = loadManifest(config)
  const cacheDir = getCacheDir(config)
  const maxAge = config.maxAgeHours * 60 * 60 * 1000
  const now = Date.now()
  let cleared = 0

  for (const [numStr, entry] of Object.entries(manifest.entries)) {
    const fetchedAt = new Date(entry.fetchedAt)
    if (now - fetchedAt.getTime() > maxAge) {
      const num = parseInt(numStr)

      // Remove cached files
      const htmlPath = path.join(cacheDir, `${num}.html`)
      const latexPath = path.join(cacheDir, `${num}.latex`)

      if (fs.existsSync(htmlPath)) fs.unlinkSync(htmlPath)
      if (fs.existsSync(latexPath)) fs.unlinkSync(latexPath)

      delete manifest.entries[num]
      cleared++
    }
  }

  if (cleared > 0) {
    saveManifest(manifest, config)
  }

  return cleared
}
