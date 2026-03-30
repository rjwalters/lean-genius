#!/usr/bin/env npx tsx
/**
 * scan-engagement.ts - Hashtag timeline scanner for Herald engagement
 *
 * Scans Mastodon hashtag timelines for posts about Lean/formal math that
 * the Herald could engage with (reply, boost, favourite).
 *
 * Stateless between runs — tracks "already replied" IDs in the herald state file.
 *
 * Usage:
 *   npx tsx scripts/herald/scan-engagement.ts              Scan and print candidates
 *   npx tsx scripts/herald/scan-engagement.ts --dry-run    Preview without recording state
 *   npx tsx scripts/herald/scan-engagement.ts --json       Output candidates as JSON
 *
 * Environment:
 *   MATHSTODON_TOKEN - API access token (falls back to .env file in repo root)
 */

import * as fs from 'fs'
import * as path from 'path'
import { fileURLToPath } from 'url'
import { createMastodonClient } from './mastodon-client.js'

const __filename = fileURLToPath(import.meta.url)
const __dirname = path.dirname(__filename)

// --- Config ---

const HASHTAGS = ['LeanProver', 'FormalMath', 'Lean4', 'ProofAssistants']
const BODY_KEYWORDS = [/\blean\b/i, /\blean4\b/i, /\bLean 4\b/i]
const MAX_CANDIDATES_PER_SCAN = 10
const MAX_REPLIES_PER_CYCLE = 3
const OUR_ACCOUNT = 'rjwalters'

// --- State ---

interface EngagementState {
  replied_to: string[]
  last_scan?: string
}

function findRepoRoot(): string {
  let dir = __dirname
  while (dir !== '/') {
    if (fs.existsSync(path.join(dir, '.git'))) return dir
    if (fs.existsSync(path.join(dir, 'package.json'))) return dir
    dir = path.dirname(dir)
  }
  throw new Error('Could not find repo root')
}

function getEngagementStatePath(): string {
  return path.join(findRepoRoot(), '.loom', 'state', 'herald-engagement.json')
}

function readEngagementState(): EngagementState {
  const filePath = getEngagementStatePath()
  if (!fs.existsSync(filePath)) {
    return { replied_to: [] }
  }
  return JSON.parse(fs.readFileSync(filePath, 'utf-8'))
}

function writeEngagementState(state: EngagementState): void {
  const filePath = getEngagementStatePath()
  const dir = path.dirname(filePath)
  if (!fs.existsSync(dir)) {
    fs.mkdirSync(dir, { recursive: true })
  }
  fs.writeFileSync(filePath, JSON.stringify(state, null, 2) + '\n')
}

// --- Scanner ---

interface EngagementCandidate {
  id: string
  url: string
  account: string
  content: string
  createdAt: string
  matchedHashtags: string[]
  matchedKeywords: string[]
}

function stripHtml(html: string): string {
  return html.replace(/<[^>]*>/g, '').replace(/&amp;/g, '&').replace(/&lt;/g, '<').replace(/&gt;/g, '>')
}

function matchesKeywords(content: string): string[] {
  const plainText = stripHtml(content)
  const matched: string[] = []
  for (const kw of BODY_KEYWORDS) {
    if (kw.test(plainText)) {
      matched.push(kw.source)
    }
  }
  return matched
}

async function scanHashtags(
  dryRun: boolean
): Promise<EngagementCandidate[]> {
  const client = createMastodonClient({ dryRun, skipStateUpdate: true })
  const state = readEngagementState()
  const repliedSet = new Set(state.replied_to)
  const seenIds = new Set<string>()
  const candidates: EngagementCandidate[] = []

  for (const hashtag of HASHTAGS) {
    try {
      const posts = await client.fetchHashtagTimeline(hashtag, 20)

      for (const post of posts) {
        // Skip our own posts
        if (post.account === OUR_ACCOUNT) continue
        // Skip already-replied
        if (repliedSet.has(post.id)) continue
        // Skip already seen in this scan (cross-hashtag dedup)
        if (seenIds.has(post.id)) continue
        seenIds.add(post.id)

        // Check body keywords
        const matchedKw = matchesKeywords(post.content)
        if (matchedKw.length === 0) continue

        candidates.push({
          id: post.id,
          url: post.url,
          account: post.account,
          content: stripHtml(post.content).slice(0, 200),
          createdAt: post.createdAt,
          matchedHashtags: [hashtag],
          matchedKeywords: matchedKw,
        })

        if (candidates.length >= MAX_CANDIDATES_PER_SCAN) break
      }
    } catch (err) {
      console.error(`Warning: failed to scan #${hashtag}: ${err instanceof Error ? err.message : err}`)
    }

    if (candidates.length >= MAX_CANDIDATES_PER_SCAN) break
  }

  // Merge matched hashtags for posts found in multiple hashtag timelines
  // (already deduped by seenIds, so just return as-is)

  // Update scan timestamp
  if (!dryRun) {
    state.last_scan = new Date().toISOString()
    writeEngagementState(state)
  }

  return candidates
}

// --- CLI ---

async function main() {
  const args = process.argv.slice(2)
  let dryRun = false
  let jsonOutput = false

  for (const arg of args) {
    if (arg === '--dry-run') dryRun = true
    else if (arg === '--json') jsonOutput = true
    else if (arg === '--help' || arg === '-h') {
      printUsage()
      process.exit(0)
    } else {
      console.error(`Unknown option: ${arg}`)
      printUsage()
      process.exit(1)
    }
  }

  console.log(`Scanning hashtags: ${HASHTAGS.map(h => '#' + h).join(', ')}`)
  if (dryRun) console.log('[DRY RUN] State will not be updated')
  console.log()

  const candidates = await scanHashtags(dryRun)

  if (jsonOutput) {
    console.log(JSON.stringify({ candidates, count: candidates.length, max_replies: MAX_REPLIES_PER_CYCLE }, null, 2))
    return
  }

  if (candidates.length === 0) {
    console.log('No engagement candidates found.')
    return
  }

  console.log(`Found ${candidates.length} candidate(s) (max ${MAX_REPLIES_PER_CYCLE} replies per cycle):`)
  console.log()

  for (let i = 0; i < candidates.length; i++) {
    const c = candidates[i]
    const marker = i < MAX_REPLIES_PER_CYCLE ? '*' : ' '
    console.log(`${marker} [${c.id}] @${c.account} (${c.createdAt})`)
    console.log(`  ${c.content}`)
    console.log(`  Keywords: ${c.matchedKeywords.join(', ')} | Hashtags: ${c.matchedHashtags.map(h => '#' + h).join(', ')}`)
    console.log(`  URL: ${c.url}`)
    console.log()
  }

  console.log(`* = within per-cycle reply cap (${MAX_REPLIES_PER_CYCLE})`)
}

function printUsage() {
  console.log(`scan-engagement.ts - Hashtag timeline scanner for Herald engagement

Usage:
  npx tsx scripts/herald/scan-engagement.ts              Scan and print candidates
  npx tsx scripts/herald/scan-engagement.ts --dry-run    Preview without recording state
  npx tsx scripts/herald/scan-engagement.ts --json       Output candidates as JSON

Scanned hashtags: ${HASHTAGS.map(h => '#' + h).join(', ')}
Body keyword filter: posts must mention Lean, Lean4, or Lean 4
Max replies per cycle: ${MAX_REPLIES_PER_CYCLE}

State file: .loom/state/herald-engagement.json`)
}

// Run CLI if invoked directly
if (import.meta.url === `file://${process.argv[1]}` ||
    process.argv[1]?.endsWith('scan-engagement.ts')) {
  main().catch((err) => {
    console.error(`Error: ${err instanceof Error ? err.message : err}`)
    process.exit(1)
  })
}
