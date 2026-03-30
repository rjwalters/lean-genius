#!/usr/bin/env npx tsx
/**
 * mastodon-client.ts - TypeScript Mastodon client for Lean Genius Herald
 *
 * Dual-mode: importable as a library AND callable as a CLI.
 *
 * CLI Usage:
 *   npx tsx scripts/herald/mastodon-client.ts post "Hello world"
 *   npx tsx scripts/herald/mastodon-client.ts post --dry-run "Test post"
 *   npx tsx scripts/herald/mastodon-client.ts post --visibility unlisted "Quiet post"
 *   npx tsx scripts/herald/mastodon-client.ts reply <parent-id> "Reply text"
 *   npx tsx scripts/herald/mastodon-client.ts boost <status-id>
 *   npx tsx scripts/herald/mastodon-client.ts favourite <status-id>
 *   npx tsx scripts/herald/mastodon-client.ts status
 *
 * Environment:
 *   MATHSTODON_TOKEN - API access token (falls back to .env file in repo root)
 *
 * Library Usage:
 *   import { createMastodonClient } from './mastodon-client.js'
 *   const client = createMastodonClient()
 *   const status = await client.post('Hello world')
 */

import * as fs from 'fs'
import * as path from 'path'
import { fileURLToPath } from 'url'
import { createRestAPIClient } from 'masto'

const __filename = fileURLToPath(import.meta.url)
const __dirname = path.dirname(__filename)

const MASTODON_INSTANCE = 'https://mathstodon.xyz'
const STATE_FILE_NAME = 'herald-posts.json'

// --- Token Loading ---

function findRepoRoot(): string {
  let dir = __dirname
  while (dir !== '/') {
    if (fs.existsSync(path.join(dir, '.git'))) return dir
    if (fs.existsSync(path.join(dir, 'package.json'))) return dir
    dir = path.dirname(dir)
  }
  throw new Error('Could not find repo root')
}

function loadToken(): string {
  if (process.env.MATHSTODON_TOKEN) {
    return process.env.MATHSTODON_TOKEN
  }

  const envPath = path.join(findRepoRoot(), '.env')
  if (fs.existsSync(envPath)) {
    const content = fs.readFileSync(envPath, 'utf-8')
    for (const line of content.split('\n')) {
      const match = line.match(/^MATHSTODON_TOKEN=(['"]?)(.+)\1$/)
      if (match) return match[2]
    }
  }

  throw new Error(
    'MATHSTODON_TOKEN not set. Add it to .env or export it.'
  )
}

// --- State File ---

interface HeraldPost {
  subject?: string
  text: string
  url?: string
  posted_at: string
  arc?: string
  mastodon_id?: string
  type?: 'post' | 'reply' | 'boost' | 'favourite'
  in_reply_to?: string
}

interface HeraldState {
  posts: HeraldPost[]
  daily_counts: Record<string, number>
  engagement?: Record<string, string[]>
}

function getStateFilePath(): string {
  return path.join(findRepoRoot(), '.loom', 'state', STATE_FILE_NAME)
}

function readState(): HeraldState {
  const filePath = getStateFilePath()
  if (!fs.existsSync(filePath)) {
    return { posts: [], daily_counts: {} }
  }
  return JSON.parse(fs.readFileSync(filePath, 'utf-8'))
}

function writeState(state: HeraldState): void {
  const filePath = getStateFilePath()
  const dir = path.dirname(filePath)
  if (!fs.existsSync(dir)) {
    fs.mkdirSync(dir, { recursive: true })
  }
  fs.writeFileSync(filePath, JSON.stringify(state, null, 2) + '\n')
}

function todayUTC(): string {
  return new Date().toISOString().slice(0, 10)
}

function nowUTC(): string {
  return new Date().toISOString().replace(/\.\d{3}Z$/, 'Z')
}

// --- Client ---

export interface MastodonClientOptions {
  instance?: string
  token?: string
  dryRun?: boolean
  skipStateUpdate?: boolean
}

export interface PostResult {
  id: string
  url: string
  content: string
  createdAt: string
}

export function createMastodonClient(opts: MastodonClientOptions = {}) {
  const instance = opts.instance ?? MASTODON_INSTANCE
  const dryRun = opts.dryRun ?? false
  const skipState = opts.skipStateUpdate ?? false

  // Lazy-init the REST client (only when we actually need the API)
  let _client: ReturnType<typeof createRestAPIClient> | null = null
  function getClient() {
    if (!_client) {
      const token = opts.token ?? loadToken()
      _client = createRestAPIClient({ url: instance, accessToken: token })
    }
    return _client
  }

  return {
    /**
     * Post a new status.
     */
    async post(
      text: string,
      options: { visibility?: string; subject?: string; arc?: string } = {}
    ): Promise<PostResult | null> {
      const visibility = (options.visibility ?? 'public') as 'public' | 'unlisted' | 'private' | 'direct'

      if (dryRun) {
        console.log(`[DRY RUN] Would post (${text.length} chars):`)
        console.log(text)
        console.log(`\nVisibility: ${visibility}`)
        return null
      }

      const client = getClient()
      const status = await client.v1.statuses.create({
        status: text,
        visibility,
      })

      // Update state (skip when caller manages state externally, e.g. post-mathstodon.sh)
      if (!skipState) {
        const state = readState()
        const post: HeraldPost = {
          text,
          posted_at: nowUTC(),
          url: status.url ?? undefined,
          mastodon_id: status.id,
          type: 'post',
        }
        if (options.subject) post.subject = options.subject
        if (options.arc) post.arc = options.arc
        state.posts.push(post)
        state.daily_counts[todayUTC()] = (state.daily_counts[todayUTC()] ?? 0) + 1
        writeState(state)
      }

      return {
        id: status.id,
        url: status.url ?? '',
        content: status.content,
        createdAt: status.createdAt,
      }
    },

    /**
     * Reply to an existing status.
     */
    async reply(
      parentId: string,
      text: string,
      options: { visibility?: string } = {}
    ): Promise<PostResult | null> {
      const visibility = (options.visibility ?? 'public') as 'public' | 'unlisted' | 'private' | 'direct'

      if (dryRun) {
        console.log(`[DRY RUN] Would reply to ${parentId} (${text.length} chars):`)
        console.log(text)
        return null
      }

      const client = getClient()
      const status = await client.v1.statuses.create({
        status: text,
        visibility,
        inReplyToId: parentId,
      })

      if (!skipState) {
        const state = readState()
        state.posts.push({
          text,
          posted_at: nowUTC(),
          url: status.url ?? undefined,
          mastodon_id: status.id,
          type: 'reply',
          in_reply_to: parentId,
        })
        state.daily_counts[todayUTC()] = (state.daily_counts[todayUTC()] ?? 0) + 1
        writeState(state)
      }

      return {
        id: status.id,
        url: status.url ?? '',
        content: status.content,
        createdAt: status.createdAt,
      }
    },

    /**
     * Boost (reblog) a status.
     */
    async boost(statusId: string): Promise<PostResult | null> {
      if (dryRun) {
        console.log(`[DRY RUN] Would boost status ${statusId}`)
        return null
      }

      const client = getClient()
      const status = await client.v1.statuses.$select(statusId).reblog()

      return {
        id: status.id,
        url: status.url ?? '',
        content: status.content,
        createdAt: status.createdAt,
      }
    },

    /**
     * Favourite a status.
     */
    async favourite(statusId: string): Promise<PostResult | null> {
      if (dryRun) {
        console.log(`[DRY RUN] Would favourite status ${statusId}`)
        return null
      }

      const client = getClient()
      const status = await client.v1.statuses.$select(statusId).favourite()

      return {
        id: status.id,
        url: status.url ?? '',
        content: status.content,
        createdAt: status.createdAt,
      }
    },

    /**
     * Fetch hashtag timeline posts.
     */
    async fetchHashtagTimeline(
      hashtag: string,
      limit: number = 20
    ): Promise<Array<{ id: string; content: string; url: string; account: string; createdAt: string }>> {
      const client = getClient()
      const paginator = client.v1.timelines.tag.$select(hashtag).list({ limit })
      const results: Array<{ id: string; content: string; url: string; account: string; createdAt: string }> = []
      for await (const statuses of paginator) {
        for (const s of statuses) {
          results.push({
            id: s.id,
            content: s.content,
            url: s.url ?? '',
            account: s.account.acct,
            createdAt: s.createdAt,
          })
        }
        break // Only fetch the first page
      }
      return results
    },

    /**
     * Show status from state file.
     */
    showStatus(): void {
      const state = readState()
      const today = todayUTC()
      const todayCount = state.daily_counts[today] ?? 0
      const totalPosts = state.posts.length

      console.log('=== Mastodon Client Status ===')
      console.log()
      console.log(`State file: ${getStateFilePath()}`)
      console.log(`Total posts tracked: ${totalPosts}`)
      console.log(`Posts today (${today}): ${todayCount} / 8`)
      console.log()

      if (totalPosts > 0) {
        console.log('Last 5 posts:')
        const recent = state.posts.slice(-5)
        for (const p of recent) {
          const subj = p.subject ?? '(no subject)'
          const truncated = p.text.slice(0, 70)
          console.log(`  [${p.posted_at}] ${subj}: ${truncated}...`)
        }
      }
    },
  }
}

// --- CLI ---

async function main() {
  const args = process.argv.slice(2)
  if (args.length === 0) {
    printUsage()
    process.exit(1)
  }

  const command = args[0]

  // Parse flags
  let dryRun = false
  let noState = false
  let visibility = 'public'
  const positional: string[] = []

  for (let i = 1; i < args.length; i++) {
    if (args[i] === '--dry-run') {
      dryRun = true
    } else if (args[i] === '--no-state') {
      noState = true
    } else if (args[i] === '--visibility' && i + 1 < args.length) {
      visibility = args[++i]
    } else {
      positional.push(args[i])
    }
  }

  const client = createMastodonClient({ dryRun, skipStateUpdate: noState })

  switch (command) {
    case 'post': {
      const text = positional[0]
      if (!text) {
        console.error('Error: post text is required')
        process.exit(1)
      }
      if (text.length > 500) {
        console.error(`Error: post is ${text.length} chars (max 500)`)
        process.exit(1)
      }
      const result = await client.post(text, { visibility })
      if (result) {
        console.log(`Posted successfully (${text.length} chars)`)
        if (result.url) console.log(result.url)
        console.log(result.id)
      }
      break
    }

    case 'reply': {
      const parentId = positional[0]
      const text = positional[1]
      if (!parentId || !text) {
        console.error('Error: reply requires <parent-id> and <text>')
        process.exit(1)
      }
      if (text.length > 500) {
        console.error(`Error: reply is ${text.length} chars (max 500)`)
        process.exit(1)
      }
      const result = await client.reply(parentId, text, { visibility })
      if (result) {
        console.log(`Replied successfully (${text.length} chars)`)
        if (result.url) console.log(result.url)
        console.log(result.id)
      }
      break
    }

    case 'boost': {
      const statusId = positional[0]
      if (!statusId) {
        console.error('Error: boost requires <status-id>')
        process.exit(1)
      }
      const result = await client.boost(statusId)
      if (result) {
        console.log(`Boosted status ${statusId}`)
      }
      break
    }

    case 'favourite': {
      const statusId = positional[0]
      if (!statusId) {
        console.error('Error: favourite requires <status-id>')
        process.exit(1)
      }
      const result = await client.favourite(statusId)
      if (result) {
        console.log(`Favourited status ${statusId}`)
      }
      break
    }

    case 'status': {
      client.showStatus()
      break
    }

    default:
      console.error(`Unknown command: ${command}`)
      printUsage()
      process.exit(1)
  }
}

function printUsage() {
  console.log(`mastodon-client.ts - Mastodon API client for Lean Genius Herald

Usage:
  npx tsx scripts/herald/mastodon-client.ts post [--dry-run] [--visibility VIS] "text"
  npx tsx scripts/herald/mastodon-client.ts reply [--dry-run] <parent-id> "text"
  npx tsx scripts/herald/mastodon-client.ts boost <status-id>
  npx tsx scripts/herald/mastodon-client.ts favourite <status-id>
  npx tsx scripts/herald/mastodon-client.ts status

Commands:
  post        Post a new status
  reply       Reply to an existing status
  boost       Boost (reblog) a status
  favourite   Favourite a status
  status      Show state file status (post count, rate limits)

Options:
  --dry-run        Show what would happen without calling the API
  --no-state       Skip state file updates (for external orchestration)
  --visibility VIS Set visibility (public, unlisted, private, direct)

Environment:
  MATHSTODON_TOKEN   API access token (read from .env if not set)`)
}

// Run CLI if invoked directly
if (import.meta.url === `file://${process.argv[1]}` ||
    process.argv[1]?.endsWith('mastodon-client.ts')) {
  main().catch((err) => {
    console.error(`Error: ${err instanceof Error ? err.message : err}`)
    process.exit(1)
  })
}
