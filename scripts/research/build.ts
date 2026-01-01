#!/usr/bin/env npx tsx
/**
 * Research Data Build Script
 *
 * Processes research/ directory markdown files into JSON for the website:
 * 1. research-listings.json - lightweight gallery data
 * 2. Individual problem JSON files for detail pages
 *
 * Run: npx tsx scripts/research/build.ts
 */

import * as fs from 'fs'
import * as path from 'path'
import { fileURLToPath } from 'url'

const __filename = fileURLToPath(import.meta.url)
const __dirname = path.dirname(__filename)

const RESEARCH_DIR = path.join(__dirname, '../../research')
const PROBLEMS_DIR = path.join(RESEARCH_DIR, 'problems')
const OUTPUT_DIR = path.join(__dirname, '../../src/data/research')
const PROBLEMS_OUTPUT_DIR = path.join(OUTPUT_DIR, 'problems')

// Types matching src/types/research.ts
type ResearchPhase = 'NEW' | 'OBSERVE' | 'ORIENT' | 'DECIDE' | 'ACT' | 'VERIFY' | 'LEARN' | 'BREAKTHROUGH' | 'PIVOT'
type ValueTier = 'S' | 'A' | 'B' | 'C' | 'D'
type ResearchStatus = 'active' | 'graduated' | 'abandoned' | 'blocked'
type ResearchPath = 'fast' | 'full'

interface RegistryEntry {
  slug: string
  phase: ResearchPhase
  path: ResearchPath
  started: string
  status: ResearchStatus
  lastUpdate?: string
  completed?: string
  template?: string
  template_value?: string
  derived_from?: string
}

interface Registry {
  version: string
  problems: RegistryEntry[]
  config: object
}

interface ResearchListing {
  slug: string
  title: string
  description: string
  phase: ResearchPhase
  status: ResearchStatus
  tier: ValueTier
  path: ResearchPath
  tags: string[]
  started: string
  lastUpdate?: string
  completed?: string
  attemptCount: number
  approachCount: number
  linkedProof?: string
  significance?: number
  tractability?: number
}

interface ResearchProblem {
  slug: string
  title: string
  phase: ResearchPhase
  status: ResearchStatus
  tier: ValueTier
  path: ResearchPath
  problemStatement: {
    formal: string
    plain: string
    whyMatters: string[]
  }
  knownResults: {
    proven: string[]
    open: string[]
    goal: string
  }
  currentState: {
    phase: ResearchPhase
    since: string
    iteration: number
    focus: string
    activeApproach?: string
    blockers: string[]
    nextAction: string
    attemptCounts: {
      total: number
      currentApproach: number
      approachesTried: number
    }
  }
  knowledge: {
    progressSummary: string
    builtItems: { name: string; description: string; proven: boolean }[]
    insights: string[]
    mathlibGaps: string[]
    nextSteps: string[]
  }
  approaches: {
    id: string
    name: string
    status: 'active' | 'completed' | 'abandoned'
    hypothesis: string
    strategy: string
    risks: string[]
    attempts: { file: string; succeeded: boolean }[]
    postMortem?: {
      whatWorked: string[]
      whatFailed: string[]
      lessonsLearned: string[]
    }
  }[]
  tags: string[]
  relatedProofs: string[]
  references: {
    papers: string[]
    urls: string[]
    mathlib: string[]
  }
  started: string
  lastUpdate?: string
  completed?: string
  linkedProof?: string
  significance?: number
  tractability?: number
}

/**
 * Extract title from problem.md
 */
function extractTitle(content: string): string {
  const match = content.match(/^#\s+(?:Problem:\s*)?(.+)$/m)
  return match ? match[1].trim() : 'Unknown'
}

/**
 * Extract formal statement (LaTeX) from problem.md
 */
function extractFormalStatement(content: string): string {
  const match = content.match(/###\s*Formal Statement[\s\S]*?\$\$([\s\S]*?)\$\$/m)
  return match ? match[1].trim() : ''
}

/**
 * Extract plain language statement from problem.md
 */
function extractPlainStatement(content: string): string {
  const match = content.match(/###\s*Plain Language\s*\n([\s\S]*?)(?=\n###|\n##|$)/m)
  if (!match) return ''
  // Get first paragraph
  const lines = match[1].trim().split('\n')
  return lines[0] || ''
}

/**
 * Extract "Why This Matters" list from problem.md
 */
function extractWhyMatters(content: string): string[] {
  const match = content.match(/###\s*Why This Matters\s*\n([\s\S]*?)(?=\n##|$)/m)
  if (!match) return []
  const items: string[] = []
  const lines = match[1].split('\n')
  for (const line of lines) {
    const itemMatch = line.match(/^\d+\.\s*\*\*([^*]+)\*\*/)
    if (itemMatch) {
      items.push(itemMatch[1].trim())
    }
  }
  return items
}

/**
 * Extract tags from YAML metadata in problem.md
 */
function extractTags(content: string): string[] {
  const yamlMatch = content.match(/```yaml\n([\s\S]*?)\n```/)
  if (!yamlMatch) return []
  const tagsMatch = yamlMatch[1].match(/tags:\s*\n((?:\s*-\s*.+\n?)+)/)
  if (!tagsMatch) return []
  const tags: string[] = []
  const lines = tagsMatch[1].split('\n')
  for (const line of lines) {
    const tagMatch = line.match(/^\s*-\s*(.+)$/)
    if (tagMatch) {
      tags.push(tagMatch[1].trim())
    }
  }
  return tags
}

/**
 * Extract significance from problem.md
 */
function extractSignificance(content: string): number | undefined {
  const match = content.match(/\*\*Significance\*\*:\s*(\d+)\/10/)
  return match ? parseInt(match[1], 10) : undefined
}

/**
 * Extract tractability from problem.md
 */
function extractTractability(content: string): number | undefined {
  const match = content.match(/\*\*Tractability\*\*:\s*(\d+)\/10/)
  return match ? parseInt(match[1], 10) : undefined
}

/**
 * Extract related proofs from problem.md
 */
function extractRelatedProofs(content: string): string[] {
  const match = content.match(/##\s*Related Gallery Proofs[\s\S]*?\|[\s\S]*?\|([\s\S]*?)(?=\n##|$)/m)
  if (!match) return []
  const proofs: string[] = []
  const lines = match[1].split('\n')
  for (const line of lines) {
    const parts = line.split('|').filter(p => p.trim())
    if (parts.length > 0 && !parts[0].includes('---')) {
      const slug = parts[0].trim()
      if (slug && !slug.includes('Proof')) {
        proofs.push(slug)
      }
    }
  }
  return proofs
}

/**
 * Parse state.md to extract current state
 */
function parseState(content: string, registryEntry: RegistryEntry): ResearchProblem['currentState'] {
  const phaseMatch = content.match(/\*\*Phase\*\*:\s*(\w+)/)
  const sinceMatch = content.match(/\*\*Since\*\*:\s*(.+)/)
  const iterationMatch = content.match(/\*\*Iteration\*\*:\s*(\d+)/)
  const focusMatch = content.match(/##\s*Current Focus\s*\n([\s\S]*?)(?=\n##|$)/m)
  const activeMatch = content.match(/##\s*Active Approach\s*\n([\s\S]*?)(?=\n##|$)/m)
  const blockersMatch = content.match(/##\s*Blockers\s*\n([\s\S]*?)(?=\n##|$)/m)
  const nextMatch = content.match(/##\s*Next Action\s*\n([\s\S]*?)(?=\n##|$)/m)
  const totalMatch = content.match(/Total attempts:\s*(\d+)/)
  const currentMatch = content.match(/Current approach attempts:\s*(\d+)/)
  const triedMatch = content.match(/Approaches tried:\s*(\d+)/)

  const blockers: string[] = []
  if (blockersMatch) {
    const text = blockersMatch[1].trim()
    if (text.toLowerCase() !== 'none.' && text.toLowerCase() !== 'none') {
      blockers.push(text)
    }
  }

  return {
    phase: (phaseMatch?.[1] as ResearchPhase) || registryEntry.phase,
    since: sinceMatch?.[1] || registryEntry.started,
    iteration: parseInt(iterationMatch?.[1] || '1', 10),
    focus: focusMatch?.[1]?.trim() || '',
    activeApproach: activeMatch?.[1]?.trim() !== 'None yet.' ? activeMatch?.[1]?.trim() : undefined,
    blockers,
    nextAction: nextMatch?.[1]?.trim() || '',
    attemptCounts: {
      total: parseInt(totalMatch?.[1] || '0', 10),
      currentApproach: parseInt(currentMatch?.[1] || '0', 10),
      approachesTried: parseInt(triedMatch?.[1] || '0', 10)
    }
  }
}

/**
 * Parse knowledge.md to extract knowledge
 */
function parseKnowledge(content: string): ResearchProblem['knowledge'] {
  const progressMatch = content.match(/\*\*Milestone achieved\*\*:\s*(.+)/)
  const insightsMatch = content.match(/##\s*Technical Insights\s*\n([\s\S]*?)(?=\n##|$)/m)
  const gapsMatch = content.match(/###\s*What Mathlib Lacks\s*\n([\s\S]*?)(?=\n##|$)/m)
  const nextMatch = content.match(/##\s*Next Steps\s*\n([\s\S]*?)(?=\n##|$)/m)

  const insights: string[] = []
  if (insightsMatch) {
    const text = insightsMatch[1]
    // Extract subsection titles as insights
    const headers = text.match(/###\s+(.+)/g)
    if (headers) {
      for (const h of headers) {
        insights.push(h.replace(/^###\s+/, ''))
      }
    }
  }

  const mathlibGaps: string[] = []
  if (gapsMatch) {
    const lines = gapsMatch[1].split('\n')
    for (const line of lines) {
      const itemMatch = line.match(/^-\s+(.+)$/)
      if (itemMatch) {
        mathlibGaps.push(itemMatch[1].trim())
      }
    }
  }

  const nextSteps: string[] = []
  if (nextMatch) {
    const lines = nextMatch[1].split('\n')
    for (const line of lines) {
      const itemMatch = line.match(/^\d+\.\s+\*\*([^*]+)\*\*/)
      if (itemMatch) {
        nextSteps.push(itemMatch[1].trim())
      }
    }
  }

  return {
    progressSummary: progressMatch?.[1] || '',
    builtItems: [],
    insights,
    mathlibGaps,
    nextSteps
  }
}

/**
 * Parse approaches directory
 */
function parseApproaches(approachesDir: string): ResearchProblem['approaches'] {
  if (!fs.existsSync(approachesDir)) return []

  const approaches: ResearchProblem['approaches'] = []
  const dirs = fs.readdirSync(approachesDir).filter(d => {
    return fs.statSync(path.join(approachesDir, d)).isDirectory()
  })

  for (const dir of dirs) {
    const approachPath = path.join(approachesDir, dir)
    const approachMd = path.join(approachPath, 'approach.md')
    const hypothesisMd = path.join(approachPath, 'hypothesis.md')

    let content = ''
    if (fs.existsSync(approachMd)) {
      content = fs.readFileSync(approachMd, 'utf-8')
    } else if (fs.existsSync(hypothesisMd)) {
      content = fs.readFileSync(hypothesisMd, 'utf-8')
    }

    // Count attempts
    const attemptsDir = path.join(approachPath, 'attempts')
    const attempts: { file: string; succeeded: boolean }[] = []
    if (fs.existsSync(attemptsDir)) {
      const files = fs.readdirSync(attemptsDir).filter(f => f.endsWith('.lean'))
      for (const f of files) {
        attempts.push({ file: f, succeeded: false })
      }
    }

    const titleMatch = content.match(/^#\s+(?:Approach \d+:\s*)?(.+)$/m)
    const strategyMatch = content.match(/##\s*Strategy\s*\n([\s\S]*?)(?=\n##|$)/m)

    approaches.push({
      id: dir,
      name: titleMatch?.[1]?.trim() || dir,
      status: 'active',
      hypothesis: '',
      strategy: strategyMatch?.[1]?.trim() || '',
      risks: [],
      attempts
    })
  }

  return approaches
}

/**
 * Infer value tier from tractability and significance
 */
function inferTier(significance?: number, tractability?: number): ValueTier {
  if (significance === undefined) return 'C'
  if (significance >= 9) return 'S'
  if (significance >= 7) return 'A'
  if (significance >= 5) return 'B'
  if (significance >= 3) return 'C'
  return 'D'
}

/**
 * Process a single research problem
 */
function processProblem(slug: string, entry: RegistryEntry): ResearchProblem | null {
  const problemDir = path.join(PROBLEMS_DIR, slug)

  if (!fs.existsSync(problemDir)) {
    console.warn(`  Warning: Problem directory not found for ${slug}`)
    return null
  }

  // Read problem.md
  const problemMdPath = path.join(problemDir, 'problem.md')
  if (!fs.existsSync(problemMdPath)) {
    console.warn(`  Warning: problem.md not found for ${slug}`)
    return null
  }
  const problemMd = fs.readFileSync(problemMdPath, 'utf-8')

  // Read state.md
  const stateMdPath = path.join(problemDir, 'state.md')
  const stateMd = fs.existsSync(stateMdPath) ? fs.readFileSync(stateMdPath, 'utf-8') : ''

  // Read knowledge.md
  const knowledgeMdPath = path.join(problemDir, 'knowledge.md')
  const knowledgeMd = fs.existsSync(knowledgeMdPath) ? fs.readFileSync(knowledgeMdPath, 'utf-8') : ''

  // Extract data
  const title = extractTitle(problemMd)
  const significance = extractSignificance(problemMd)
  const tractability = extractTractability(problemMd)
  const tier = inferTier(significance, tractability)
  const tags = extractTags(problemMd)
  const relatedProofs = extractRelatedProofs(problemMd)

  const currentState = parseState(stateMd, entry)
  const knowledge = parseKnowledge(knowledgeMd)
  const approaches = parseApproaches(path.join(problemDir, 'approaches'))

  return {
    slug,
    title,
    phase: entry.phase,
    status: entry.status,
    tier,
    path: entry.path,
    problemStatement: {
      formal: extractFormalStatement(problemMd),
      plain: extractPlainStatement(problemMd),
      whyMatters: extractWhyMatters(problemMd)
    },
    knownResults: {
      proven: [],
      open: [],
      goal: ''
    },
    currentState,
    knowledge,
    approaches,
    tags,
    relatedProofs,
    references: {
      papers: [],
      urls: [],
      mathlib: []
    },
    started: entry.started,
    lastUpdate: entry.lastUpdate,
    completed: entry.completed,
    significance,
    tractability
  }
}

/**
 * Generate lightweight listing from full problem
 */
function generateListing(problem: ResearchProblem): ResearchListing {
  return {
    slug: problem.slug,
    title: problem.title,
    description: problem.problemStatement.plain || problem.title,
    phase: problem.phase,
    status: problem.status,
    tier: problem.tier,
    path: problem.path,
    tags: problem.tags,
    started: problem.started,
    lastUpdate: problem.lastUpdate,
    completed: problem.completed,
    attemptCount: problem.currentState.attemptCounts.total,
    approachCount: problem.approaches.length,
    linkedProof: problem.linkedProof,
    significance: problem.significance,
    tractability: problem.tractability
  }
}

/**
 * Main build function
 */
function build(): void {
  console.log('🔬 Building research data...\n')

  // Read registry
  const registryPath = path.join(RESEARCH_DIR, 'registry.json')
  if (!fs.existsSync(registryPath)) {
    console.error('Error: registry.json not found')
    process.exit(1)
  }
  const registry: Registry = JSON.parse(fs.readFileSync(registryPath, 'utf-8'))
  console.log(`   Found ${registry.problems.length} problems in registry\n`)

  // Ensure output directories exist
  if (!fs.existsSync(PROBLEMS_OUTPUT_DIR)) {
    fs.mkdirSync(PROBLEMS_OUTPUT_DIR, { recursive: true })
  }

  // Process each problem
  const problems: ResearchProblem[] = []
  const listings: ResearchListing[] = []

  for (const entry of registry.problems) {
    // Skip template-derived problems (low-value stamp collecting)
    if (entry.template) {
      console.log(`   Skipping ${entry.slug} (template-derived)`)
      continue
    }

    // Skip graduated/blocked problems (they're in the proof gallery now)
    if (entry.status === 'graduated' || entry.status === 'blocked') {
      console.log(`   Skipping ${entry.slug} (${entry.status})`)
      continue
    }

    console.log(`   Processing ${entry.slug}...`)
    const problem = processProblem(entry.slug, entry)
    if (problem) {
      problems.push(problem)
      listings.push(generateListing(problem))

      // Write individual problem JSON
      const outputPath = path.join(PROBLEMS_OUTPUT_DIR, `${entry.slug}.json`)
      fs.writeFileSync(outputPath, JSON.stringify(problem, null, 2) + '\n')
    }
  }

  // Write listings
  const listingsPath = path.join(OUTPUT_DIR, 'research-listings.json')
  fs.writeFileSync(listingsPath, JSON.stringify(listings, null, 2) + '\n')

  // Summary
  const activeCount = listings.filter(l => l.status === 'active').length
  const graduatedCount = listings.filter(l => l.status === 'graduated').length

  console.log(`\n📊 Summary:`)
  console.log(`   Active:    ${activeCount} problems`)
  console.log(`   Graduated: ${graduatedCount} problems`)
  console.log(`   Total:     ${problems.length} problems`)
  console.log(`\n✅ Generated research-listings.json (${Math.round(fs.statSync(listingsPath).size / 1024)}KB)`)
  console.log(`   Generated ${problems.length} individual problem files`)
}

// Run
build()
