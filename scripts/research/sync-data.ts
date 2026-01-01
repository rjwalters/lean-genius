#!/usr/bin/env npx tsx
/**
 * Research Data Sync Script
 *
 * Synchronizes data between candidate-pool.json and registry.json to ensure
 * the website displays accurate, up-to-date research problem information.
 *
 * This script:
 * 1. Reads both candidate-pool.json and registry.json
 * 2. Adds missing problems from candidate-pool to registry
 * 3. Syncs status between the two files (bidirectional)
 * 4. Updates problem.md files with significance/tractability from pool
 *
 * Run: npx tsx scripts/research/sync-data.ts
 */

import * as fs from 'fs'
import * as path from 'path'
import { fileURLToPath } from 'url'

const __filename = fileURLToPath(import.meta.url)
const __dirname = path.dirname(__filename)

const RESEARCH_DIR = path.join(__dirname, '../../research')
const POOL_FILE = path.join(RESEARCH_DIR, 'candidate-pool.json')
const REGISTRY_FILE = path.join(RESEARCH_DIR, 'registry.json')
const PROBLEMS_DIR = path.join(RESEARCH_DIR, 'problems')

// Types
interface PoolCandidate {
  id: string
  name: string
  tier: string
  significance: number
  tractability: number
  status: 'available' | 'in-progress' | 'completed' | 'skipped' | 'surveyed'
  notes: string
  tags: string[]
}

interface CandidatePool {
  version: string
  last_updated: string
  candidates: PoolCandidate[]
}

interface RegistryEntry {
  slug: string
  phase: string
  path: string
  started: string
  status: 'active' | 'graduated' | 'abandoned' | 'blocked'
  lastUpdate?: string
  completed?: string
  template?: string
}

interface Registry {
  version: string
  problems: RegistryEntry[]
  config: object
}

// Status mapping: pool status -> registry status
const POOL_TO_REGISTRY_STATUS: Record<string, 'active' | 'graduated' | 'abandoned' | 'blocked'> = {
  'available': 'active',
  'in-progress': 'active',
  'completed': 'graduated',
  'skipped': 'blocked',
  'surveyed': 'active'  // surveyed = ongoing research
}

// Status mapping: registry status -> pool status
const REGISTRY_TO_POOL_STATUS: Record<string, 'available' | 'in-progress' | 'completed' | 'skipped' | 'surveyed'> = {
  'active': 'in-progress',
  'graduated': 'completed',
  'abandoned': 'skipped',
  'blocked': 'skipped'
}

// Phase to pool status mapping (more nuanced)
function registryToPoolStatus(entry: RegistryEntry): PoolCandidate['status'] {
  if (entry.status === 'graduated') return 'completed'
  if (entry.status === 'blocked' || entry.status === 'abandoned') return 'skipped'
  // For active, check phase
  if (entry.phase === 'NEW') return 'available'
  if (entry.phase === 'BREAKTHROUGH') return 'completed'
  return 'in-progress'
}

/**
 * Create a minimal problem.md file for a problem
 */
function createMinimalProblemMd(candidate: PoolCandidate): string {
  const tierMap: Record<string, string> = { 'A': 'A', 'B': 'B', 'C': 'C', 'S': 'S' }
  return `# Problem: ${candidate.name}

## Statement

### Plain Language
${candidate.notes.split('.')[0] || candidate.name}.

### Formal Statement
$$
\\text{(formal statement to be added)}
$$

## Classification

\`\`\`yaml
tier: ${tierMap[candidate.tier] || 'C'}
significance: ${candidate.significance}
tractability: ${candidate.tractability}
tags:
${candidate.tags.map(t => `  - ${t}`).join('\n')}
\`\`\`

**Significance**: ${candidate.significance}/10
**Tractability**: ${candidate.tractability}/10

## Why This Matters

1. **Research value** - ${candidate.notes.split('.')[0] || 'Important mathematical result'}

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| --- | --- |
`
}

/**
 * Create a minimal state.md file
 */
function createMinimalStateMd(phase: string): string {
  return `# Current State

**Phase**: ${phase}
**Since**: ${new Date().toISOString()}
**Iteration**: 1

## Current Focus

Initial exploration of the problem.

## Active Approach

None yet.

## Blockers

None.

## Next Action

Begin problem exploration.

## Attempt Counts

- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0
`
}

/**
 * Main sync function
 */
function sync(): void {
  console.log('🔄 Syncing research data...\n')

  // Read files
  if (!fs.existsSync(POOL_FILE)) {
    console.error('Error: candidate-pool.json not found')
    process.exit(1)
  }
  if (!fs.existsSync(REGISTRY_FILE)) {
    console.error('Error: registry.json not found')
    process.exit(1)
  }

  const pool: CandidatePool = JSON.parse(fs.readFileSync(POOL_FILE, 'utf-8'))
  const registry: Registry = JSON.parse(fs.readFileSync(REGISTRY_FILE, 'utf-8'))

  console.log(`   Pool: ${pool.candidates.length} candidates`)
  console.log(`   Registry: ${registry.problems.length} problems\n`)

  // Create lookup maps
  const registryBySlug = new Map(registry.problems.map(p => [p.slug, p]))
  const poolById = new Map(pool.candidates.map(c => [c.id, c]))

  let addedToRegistry = 0
  let updatedInRegistry = 0
  let updatedInPool = 0
  let createdProblemDirs = 0

  // 1. Sync from pool to registry (add missing, update status)
  for (const candidate of pool.candidates) {
    const registryEntry = registryBySlug.get(candidate.id)

    if (!registryEntry) {
      // Add to registry
      const newEntry: RegistryEntry = {
        slug: candidate.id,
        phase: candidate.status === 'completed' ? 'BREAKTHROUGH' : 'NEW',
        path: candidate.tractability >= 7 ? 'fast' : 'full',
        started: new Date().toISOString(),
        status: POOL_TO_REGISTRY_STATUS[candidate.status] || 'active',
        lastUpdate: new Date().toISOString()
      }
      if (candidate.status === 'completed') {
        newEntry.completed = new Date().toISOString()
      }
      registry.problems.push(newEntry)
      addedToRegistry++
      console.log(`   ➕ Added to registry: ${candidate.id}`)

      // Create problem directory if missing
      const problemDir = path.join(PROBLEMS_DIR, candidate.id)
      if (!fs.existsSync(problemDir)) {
        fs.mkdirSync(problemDir, { recursive: true })
        createdProblemDirs++

        // Create problem.md
        const problemMdPath = path.join(problemDir, 'problem.md')
        fs.writeFileSync(problemMdPath, createMinimalProblemMd(candidate))

        // Create state.md
        const stateMdPath = path.join(problemDir, 'state.md')
        fs.writeFileSync(stateMdPath, createMinimalStateMd(newEntry.phase))

        console.log(`   📁 Created problem directory: ${candidate.id}`)
      }
    } else {
      // Check for status mismatch and sync
      const expectedRegistryStatus = POOL_TO_REGISTRY_STATUS[candidate.status]
      if (registryEntry.status !== expectedRegistryStatus) {
        // Pool takes precedence for high-level status
        if (candidate.status === 'completed' && registryEntry.status !== 'graduated') {
          registryEntry.status = 'graduated'
          registryEntry.phase = 'BREAKTHROUGH'
          registryEntry.completed = registryEntry.completed || new Date().toISOString()
          registryEntry.lastUpdate = new Date().toISOString()
          updatedInRegistry++
          console.log(`   🔄 Updated registry status: ${candidate.id} → graduated`)
        } else if (candidate.status === 'skipped' && registryEntry.status !== 'blocked') {
          registryEntry.status = 'blocked'
          registryEntry.lastUpdate = new Date().toISOString()
          updatedInRegistry++
          console.log(`   🔄 Updated registry status: ${candidate.id} → blocked`)
        }
      }

      // Ensure problem.md has significance/tractability
      const problemMdPath = path.join(PROBLEMS_DIR, candidate.id, 'problem.md')
      if (fs.existsSync(problemMdPath)) {
        let content = fs.readFileSync(problemMdPath, 'utf-8')
        let updated = false

        // Add significance if missing
        if (!content.includes('**Significance**:') && candidate.significance) {
          const yamlMatch = content.match(/```yaml[\s\S]*?```/)
          if (yamlMatch) {
            const afterYaml = content.indexOf(yamlMatch[0]) + yamlMatch[0].length
            const sigLine = `\n\n**Significance**: ${candidate.significance}/10`
            const tracLine = `\n**Tractability**: ${candidate.tractability}/10`
            if (!content.slice(afterYaml, afterYaml + 200).includes('**Significance**')) {
              content = content.slice(0, afterYaml) + sigLine + tracLine + content.slice(afterYaml)
              updated = true
            }
          }
        }

        if (updated) {
          fs.writeFileSync(problemMdPath, content)
          console.log(`   📝 Updated problem.md: ${candidate.id}`)
        }
      }
    }
  }

  // 2. Sync from registry to pool (update status for problems in registry but status differs)
  for (const entry of registry.problems) {
    if (entry.template) continue // Skip template-derived

    const poolEntry = poolById.get(entry.slug)
    if (poolEntry) {
      const expectedPoolStatus = registryToPoolStatus(entry)
      if (poolEntry.status !== expectedPoolStatus) {
        // Registry takes precedence for detailed status
        if (entry.status === 'graduated' && poolEntry.status !== 'completed') {
          poolEntry.status = 'completed'
          updatedInPool++
          console.log(`   🔄 Updated pool status: ${entry.slug} → completed`)
        }
      }
    }
  }

  // 3. Sync from meta.json to registry (meta.json is source of truth for status)
  let updatedFromMeta = 0
  for (const entry of registry.problems) {
    if (entry.template) continue

    const metaPath = path.join(PROBLEMS_DIR, entry.slug, 'meta.json')
    if (!fs.existsSync(metaPath)) continue

    try {
      const meta = JSON.parse(fs.readFileSync(metaPath, 'utf-8'))
      const metaStatus = meta.status as RegistryEntry['status'] | undefined

      if (metaStatus && metaStatus !== entry.status) {
        // Meta.json takes precedence - it's the source of truth
        if (metaStatus === 'graduated' && entry.status !== 'graduated') {
          entry.status = 'graduated'
          entry.phase = 'BREAKTHROUGH'
          entry.completed = entry.completed || meta.completed || new Date().toISOString()
          entry.lastUpdate = new Date().toISOString()
          updatedFromMeta++
          console.log(`   🔄 Updated registry from meta.json: ${entry.slug} → graduated`)
        } else if (metaStatus === 'blocked' && entry.status !== 'blocked') {
          entry.status = 'blocked'
          entry.lastUpdate = new Date().toISOString()
          updatedFromMeta++
          console.log(`   🔄 Updated registry from meta.json: ${entry.slug} → blocked`)
        } else if (metaStatus === 'abandoned' && entry.status !== 'abandoned') {
          entry.status = 'abandoned'
          entry.lastUpdate = new Date().toISOString()
          updatedFromMeta++
          console.log(`   🔄 Updated registry from meta.json: ${entry.slug} → abandoned`)
        }
      }
    } catch (e) {
      console.warn(`   ⚠️  Could not read meta.json for ${entry.slug}`)
    }
  }

  // 4. Write updated files
  // Update pool timestamp
  pool.last_updated = new Date().toISOString()

  fs.writeFileSync(POOL_FILE, JSON.stringify(pool, null, 2) + '\n')
  fs.writeFileSync(REGISTRY_FILE, JSON.stringify(registry, null, 2) + '\n')

  // Summary
  console.log(`\n📊 Sync Summary:`)
  console.log(`   Added to registry:     ${addedToRegistry}`)
  console.log(`   Updated in registry:   ${updatedInRegistry}`)
  console.log(`   Updated from meta:     ${updatedFromMeta}`)
  console.log(`   Updated in pool:       ${updatedInPool}`)
  console.log(`   Created problem dirs:  ${createdProblemDirs}`)
  console.log(`\n✅ Sync complete!`)
}

// Run
sync()
