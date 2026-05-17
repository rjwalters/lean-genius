#!/usr/bin/env npx tsx
/**
 * Research Data Build Script
 *
 * Builds research data for the website:
 * 1. research-listings.json - lightweight gallery index (always rebuilt)
 * 2. Individual problem JSON files for detail pages
 *
 * Strategy: Committed JSON files in src/data/research/problems/ are the
 * source of truth. The build preserves them as-is (updating only registry
 * metadata like phase/status/dates). Markdown-to-JSON generation is used
 * only as a fallback for NEW problems that don't yet have a JSON file.
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
type ResearchPhase = 'NEW' | 'OBSERVE' | 'ORIENT' | 'DECIDE' | 'ACT' | 'VERIFY' | 'LEARN' | 'COMPLETED' | 'PIVOT'
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
  linkedProof?: string
  significance?: number
  tractability?: number
  leanFileCount?: number
  totalLeanLines?: number
}

interface ArchivedSession {
  filename: string
  date: string
  sessionNumber: number
  markdown: string
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
    markdown?: string  // Full knowledge.md content for rich rendering
    archivedSessions?: ArchivedSession[]  // Older sessions from sessions/ directory
  }
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
  leanFiles?: { path: string; filename: string; lineCount: number; theoremCount: number; axiomCount: number; defCount: number; sorryCount: number; isAristotle: boolean; githubUrl: string }[]
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
      // Skip table headers ("Proof", "Relevance") and separator rows
      if (slug &&
          !slug.includes('Proof') &&
          slug !== 'Relevance' &&
          !slug.match(/^[-=]+$/)) {
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
 * Preserves full markdown content for rich rendering on frontend
 */
function parseKnowledge(content: string): ResearchProblem['knowledge'] {
  // Store the full markdown for rich rendering (if non-empty)
  const markdown = content.trim() ? content : undefined
  // Try multiple patterns for progress summary
  const progressMatch = content.match(/\*\*Milestone achieved\*\*:\s*(.+)/) ||
    content.match(/\*\*Status\*\*:\s*(.+)/)

  // Extract insights from multiple possible sections
  // Try: "### What's Proven", "## What We've Built", "### In This Repository"
  const provenMatch = content.match(/###\s*What's Proven[^\n]*\n([\s\S]*?)(?=\n###|\n##)/m)
  const builtMatch = content.match(/##\s*What We've Built\s*\n([\s\S]*?)(?=\n##\s+[^#])/m) ||
    content.match(/###\s*In This Repository\s*\n([\s\S]*?)(?=\n###|\n##)/m)

  // Try multiple patterns for Mathlib gaps
  // Pattern 1: "### What Mathlib Lacks" subsection
  // Pattern 2: "### Missing in Mathlib" subsection
  // Pattern 3: "## Blockers" section (old Millennium problems - parse "- [ ]" items)
  // Pattern 4: "### In Mathlib" table (scout format - parse ❌ items)
  // Pattern 5: "### Primary Blocker:" section (scout format - parse requirements)
  const gapsMatch = content.match(/###\s*What Mathlib Lacks\s*\n([\s\S]*?)(?=\n###|\n##)/m) ||
    content.match(/###\s*Missing in Mathlib\s*\n([\s\S]*?)(?=\n###|\n##)/m) ||
    content.match(/##\s*Blockers\s*\n([\s\S]*?)(?=\n##\s+[^#])/m) ||
    content.match(/###\s*In Mathlib\s*\n([\s\S]*?)(?=\n##)/m) ||
    content.match(/###\s*In Mathlib Now\s*\n([\s\S]*?)(?=\n##)/m) ||
    content.match(/###\s*Mathlib Status\s*\n([\s\S]*?)(?=\n##)/m) ||
    content.match(/###\s*Primary Blocker[^\n]*\n([\s\S]*?)(?=\n###|\n##)/m)

  // Try multiple patterns for next steps - at end of file or before next ##
  // Pattern 1: "## Next Steps" section
  // Pattern 2: "## Tractable Partial Work" (old Millennium problems)
  // Pattern 3: "### What We Could Still Do" (scout format)
  const nextMatch = content.match(/##\s*Next Steps[^\n]*\n([\s\S]*?)(?=\n##)/i) ||
    content.match(/##\s*Next Steps[^\n]*\n([\s\S]*)$/i) ||
    content.match(/##\s*Tractable Partial Work\s*\n([\s\S]*?)(?=\n##)/m) ||
    content.match(/###\s*What We Could Still Do\s*\n([\s\S]*?)(?=\n##)/m)

  const insights: string[] = []
  const builtItems: { name: string; description: string; proven: boolean }[] = []

  // Parse "What's Proven" section (format: - `name` - description)
  if (provenMatch) {
    const lines = provenMatch[1].split('\n')
    for (const line of lines) {
      const itemMatch = line.match(/^-\s+`([^`]+)`\s*-?\s*(.*)$/)
      if (itemMatch) {
        insights.push(itemMatch[1])
        builtItems.push({
          name: itemMatch[1],
          description: itemMatch[2]?.trim() || '',
          proven: true
        })
      }
    }
  }

  // Parse "What We've Built" section (format: - `name` - description OR subsections)
  if (builtMatch) {
    const lines = builtMatch[1].split('\n')
    for (const line of lines) {
      // Match: - `name` - description  OR  - `name (params)` - description
      const itemMatch = line.match(/^-\s+`([^`]+)`\s*-?\s*(.*)$/)
      if (itemMatch) {
        const name = itemMatch[1].split(/\s*\(/)[0].trim() // Extract just the name
        insights.push(name)
        builtItems.push({
          name,
          description: itemMatch[2]?.trim() || '',
          proven: true
        })
      }
    }
  }

  const mathlibGaps: string[] = []
  if (gapsMatch) {
    const lines = gapsMatch[1].split('\n')
    for (const line of lines) {
      // Match regular list items: "- item"
      // Also match checkbox items: "- [ ] item" or "- [x] item"
      const checkboxMatch = line.match(/^-\s+\[[ x]\]\s+(.+)$/)
      const itemMatch = line.match(/^-\s+(.+)$/)
      // Match table rows with ❌ or ⚠️: "| Component | ❌ | Notes |" or "| Component | ❌ Not available |"
      const tableMatch = line.match(/\|\s*([^|]+)\s*\|\s*[❌⚠️]/)
      // Match numbered requirements: "1. **Name**: description"
      const numberedMatch = line.match(/^\d+\.\s+\*\*([^*]+)\*\*/)

      if (checkboxMatch) {
        mathlibGaps.push(checkboxMatch[1].trim())
      } else if (tableMatch && !tableMatch[1].includes('---')) {
        mathlibGaps.push(tableMatch[1].trim())
      } else if (numberedMatch) {
        mathlibGaps.push(numberedMatch[1].trim())
      } else if (itemMatch && !itemMatch[1].startsWith('[')) {
        mathlibGaps.push(itemMatch[1].trim())
      }
    }
  }

  const nextSteps: string[] = []
  if (nextMatch) {
    const lines = nextMatch[1].split('\n')
    for (const line of lines) {
      // Match bold items: "1. **Step**" or plain items: "1. Step"
      const boldMatch = line.match(/^\d+\.\s+\*\*([^*]+)\*\*/)
      const plainMatch = line.match(/^\d+\.\s+(.+)$/)
      if (boldMatch) {
        nextSteps.push(boldMatch[1].trim())
      } else if (plainMatch && !plainMatch[1].startsWith('**')) {
        nextSteps.push(plainMatch[1].trim())
      }
    }
  }

  return {
    progressSummary: progressMatch?.[1] || '',
    builtItems,
    insights,
    mathlibGaps,
    nextSteps,
    markdown
  }
}

/**
 * Read archived sessions from sessions/ subdirectory
 */
function readArchivedSessions(sessionsDir: string): ArchivedSession[] {
  if (!fs.existsSync(sessionsDir)) return []

  const sessions: ArchivedSession[] = []
  const files = fs.readdirSync(sessionsDir)
    .filter(f => f.endsWith('.md'))
    .sort()  // Sort chronologically by filename

  for (const filename of files) {
    const filePath = path.join(sessionsDir, filename)
    const content = fs.readFileSync(filePath, 'utf-8')

    // Parse filename: 2026-01-01-s01.md -> date=2026-01-01, sessionNumber=1
    const match = filename.match(/^(\d{4}-\d{2}-\d{2})-s(\d+)\.md$/)
    if (match) {
      sessions.push({
        filename,
        date: match[1],
        sessionNumber: parseInt(match[2], 10),
        markdown: content
      })
    } else {
      // Fallback for files without standard naming
      sessions.push({
        filename,
        date: 'unknown',
        sessionNumber: sessions.length + 1,
        markdown: content
      })
    }
  }

  return sessions
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

  // Read archived sessions from sessions/ subdirectory
  const sessionsDir = path.join(problemDir, 'sessions')
  const archivedSessions = readArchivedSessions(sessionsDir)
  if (archivedSessions.length > 0) {
    knowledge.archivedSessions = archivedSessions
  }

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

// Status prefixes that indicate placeholder descriptions (safety net)
const PLACEHOLDER_PREFIXES = ['AVAILABLE', 'IN-PROGRESS', 'IN PROGRESS', 'COMPLETED', 'SKIPPED', 'SURVEYED']

/**
 * Check if a description is a status placeholder that should be replaced
 */
function isDescriptionPlaceholder(desc: string): boolean {
  const trimmed = desc.trim().replace(/\.$/, '').trim()
  if (!trimmed) return true
  const upper = trimmed.toUpperCase()
  for (const prefix of PLACEHOLDER_PREFIXES) {
    if (upper === prefix) return true
  }
  if (trimmed === '[Explain what we\'re trying to prove in accessible terms]') return true
  return false
}

/**
 * Check if a problem is an unfilled Seeker stub that should not appear in the
 * public listings. The Seeker drops `research/problems/<slug>/problem.md` from
 * a template; if no Researcher ever fills it in, the derived site JSON keeps
 * the literal placeholder strings ("[Problem Title]", `\text{[LaTeX
 * formulation of the theorem/conjecture]}`), which render verbatim on the
 * gallery and per-problem pages. We drop those from the listings index so
 * they stop appearing as public entries until backfilled.
 */
function isUnfilledStub(problem: ResearchProblem): boolean {
  const title = (problem.title || '').trim()
  if (title === '[Problem Title]') return true
  const formal = (problem.problemStatement?.formal || '').trim()
  if (formal.includes('[LaTeX formulation of the theorem/conjecture]')) return true
  return false
}

/**
 * Generate lightweight listing from full problem
 */
function generateListing(problem: ResearchProblem): ResearchListing {
  // Safety net: if problemStatement.plain is a status placeholder, fall back to title
  const rawDescription = problem.problemStatement?.plain || ''
  const description = isDescriptionPlaceholder(rawDescription)
    ? problem.title
    : rawDescription

  return {
    slug: problem.slug,
    title: problem.title,
    description,
    phase: problem.phase,
    status: problem.status,
    tier: problem.tier,
    path: problem.path,
    tags: problem.tags ?? [],
    started: problem.started,
    lastUpdate: problem.lastUpdate,
    completed: problem.completed,
    attemptCount: problem.currentState?.attemptCounts?.total ?? 0,
    linkedProof: problem.linkedProof,
    significance: problem.significance,
    tractability: problem.tractability,
    leanFileCount: problem.leanFiles?.length,
    totalLeanLines: problem.leanFiles?.reduce((sum, f) => sum + f.lineCount, 0),
  }
}

/**
 * Load an existing committed JSON file for a problem.
 * Returns the parsed ResearchProblem if the file exists, null otherwise.
 */
function loadExistingProblemJson(slug: string): ResearchProblem | null {
  const jsonPath = path.join(PROBLEMS_OUTPUT_DIR, `${slug}.json`)
  if (!fs.existsSync(jsonPath)) {
    return null
  }
  try {
    const content = fs.readFileSync(jsonPath, 'utf-8')
    return JSON.parse(content) as ResearchProblem
  } catch {
    console.warn(`  Warning: Failed to parse existing JSON for ${slug}, will regenerate from markdown`)
    return null
  }
}

/**
 * Update registry-derived fields on an existing problem JSON.
 * The registry may have more current phase/status/dates than the committed JSON.
 */
function updateRegistryFields(problem: ResearchProblem, entry: RegistryEntry): ResearchProblem {
  return {
    ...problem,
    phase: entry.phase,
    status: entry.status,
    path: entry.path,
    started: entry.started,
    lastUpdate: entry.lastUpdate ?? problem.lastUpdate,
    completed: entry.completed ?? problem.completed,
  }
}

/**
 * Main build function
 */
function build(): void {
  console.log('Building research data...\n')

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
  let preservedCount = 0
  let generatedCount = 0
  let stubSkippedCount = 0
  const stubSkippedSlugs: string[] = []

  for (const entry of registry.problems) {
    // Skip template-derived problems (low-value stamp collecting)
    if (entry.template) {
      console.log(`   Skipping ${entry.slug} (template-derived)`)
      continue
    }

    // Strategy: Use committed JSON as source of truth if it exists.
    // Only fall back to generating from markdown for new problems.
    const existingProblem = loadExistingProblemJson(entry.slug)

    if (existingProblem) {
      // Existing committed JSON found - preserve it, just update registry fields
      const problem = updateRegistryFields(existingProblem, entry)
      problems.push(problem)
      if (isUnfilledStub(problem)) {
        // Stub: keep the JSON file (deep-link still resolves) but omit from listings
        // so the public gallery page doesn't surface literal "[Problem Title]" rows.
        stubSkippedCount++
        stubSkippedSlugs.push(entry.slug)
      } else {
        listings.push(generateListing(problem))
      }
      preservedCount++
      console.log(`   Preserved ${entry.slug} (from committed JSON)`)
    } else {
      // No existing JSON - generate from markdown (new problem bootstrap)
      console.log(`   Generating ${entry.slug} (new, from markdown)...`)
      const problem = processProblem(entry.slug, entry)
      if (problem) {
        problems.push(problem)
        if (isUnfilledStub(problem)) {
          stubSkippedCount++
          stubSkippedSlugs.push(entry.slug)
        } else {
          listings.push(generateListing(problem))
        }
        generatedCount++

        // Write individual problem JSON only for newly generated problems
        const outputPath = path.join(PROBLEMS_OUTPUT_DIR, `${entry.slug}.json`)
        fs.writeFileSync(outputPath, JSON.stringify(problem, null, 2) + '\n')
      }
    }
  }

  // Write listings index (always rebuilt from the loaded problem data)
  const listingsPath = path.join(OUTPUT_DIR, 'research-listings.json')
  fs.writeFileSync(listingsPath, JSON.stringify(listings, null, 2) + '\n')

  // Summary
  const activeCount = listings.filter(l => l.status === 'active').length
  const graduatedCount = listings.filter(l => l.status === 'graduated').length

  console.log(`\nSummary:`)
  console.log(`   Active:    ${activeCount} problems`)
  console.log(`   Graduated: ${graduatedCount} problems`)
  console.log(`   Total:     ${problems.length} problems`)
  console.log(`   Preserved: ${preservedCount} (from committed JSON)`)
  console.log(`   Generated: ${generatedCount} (new, from markdown)`)
  if (stubSkippedCount > 0) {
    console.log(`   Listings:  ${listings.length} (skipped ${stubSkippedCount} unfilled Seeker stub${stubSkippedCount === 1 ? '' : 's'})`)
    const preview = stubSkippedSlugs.slice(0, 10).join(', ')
    const suffix = stubSkippedSlugs.length > 10 ? `, … (+${stubSkippedSlugs.length - 10} more)` : ''
    console.log(`              ${preview}${suffix}`)
  }

  // NOTE: We intentionally do NOT delete JSON files that are not in the registry.
  // They may be legitimate committed data from researchers.

  console.log(`\nGenerated research-listings.json (${Math.round(fs.statSync(listingsPath).size / 1024)}KB)`)
  console.log(`   ${listings.length} problems in listings index`)
}

// Run
build()
