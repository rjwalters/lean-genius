/**
 * Generate research topic entries for open Erdős problems
 *
 * Creates:
 * - research/problems/erdos-{n}-{slug}/problem.md
 * - research/problems/erdos-{n}-{slug}/state.md
 * - research/problems/erdos-{n}-{slug}/knowledge.md
 *
 * Also updates research/registry.json
 */

import * as fs from 'fs'
import * as path from 'path'
import type { TransformedProblem, ResearchGenerationResult } from './types'

const RESEARCH_DIR = 'research/problems'
const REGISTRY_FILE = 'research/registry.json'

/**
 * Generate problem.md content
 */
function generateProblemMd(problem: TransformedProblem): string {
  const tagsYaml = problem.mappedTags.map(t => `  - ${t}`).join('\n')
  const refsSection = problem.references.length > 0
    ? problem.references.map(r => `- [${r.key}]${r.citation ? `: ${r.citation}` : ''}`).join('\n')
    : '(No references available)'

  const relatedSection = problem.relatedProblems.length > 0
    ? problem.relatedProblems.map(n => `- [Problem #${n}](https://www.erdosproblems.com/${n})`).join('\n')
    : '(No related problems listed)'

  // Clean up statement
  let plainStatement = problem.statement.latex || problem.statement.html
  // Remove HTML tags
  plainStatement = plainStatement.replace(/<[^>]+>/g, '')
  // Limit length
  if (plainStatement.length > 500) {
    plainStatement = plainStatement.slice(0, 497) + '...'
  }

  const formalStatement = problem.statement.latex || '(LaTeX not available)'

  return `# Problem: Erdős #${problem.number}

## Statement

### Plain Language
${plainStatement}

### Formal Statement
$$
${formalStatement}
$$

## Classification

\`\`\`yaml
tier: ${problem.tier}
significance: ${Math.round(problem.tractability * 0.7 + 3)}
tractability: ${problem.tractability}
erdosNumber: ${problem.number}
erdosUrl: ${problem.sourceUrl}
${problem.prize ? `prize: ${problem.prize}` : ''}
tags:
${tagsYaml}
\`\`\`

**Significance**: ${Math.round(problem.tractability * 0.7 + 3)}/10
**Tractability**: ${problem.tractability}/10

## Why This Matters

1. **Erdős Legacy** - Part of Paul Erdős's influential problem collection
2. **Mathematical significance** - ${problem.tractabilityReason}
${problem.prize ? `3. **Prize** - ${problem.prize} offered for solution` : ''}

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| --- | --- |

## Related Problems

${relatedSection}

## References

${refsSection}

## OEIS Sequences

${problem.oeis && problem.oeis.length > 0 ? problem.oeis.map(seq => `- [${seq}](https://oeis.org/${seq})`).join('\n') : '(None listed)'}
`
}

/**
 * Generate state.md content
 */
function generateStateMd(): string {
  const now = new Date().toISOString()

  return `# Current State

**Phase**: NEW
**Since**: ${now}
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
 * Generate knowledge.md content
 */
function generateKnowledgeMd(problem: TransformedProblem): string {
  const tagsSection = problem.mappedTags.map(t => `- ${t}`).join('\n')
  const relatedSection = problem.relatedProblems.length > 0
    ? problem.relatedProblems.map(n => `- Problem #${n}`).join('\n')
    : '- (None listed)'
  const refsSection = problem.references.length > 0
    ? problem.references.map(r => `- ${r.key}${r.citation ? `: ${r.citation}` : ''}`).join('\n')
    : '- (None available)'

  return `# Erdős #${problem.number} - Knowledge Base

## Problem Statement

${problem.statement.latex || problem.statement.html.slice(0, 1000)}

## Status

**Erdős Database Status**: ${problem.status}
${problem.prize ? `**Prize**: ${problem.prize}` : ''}
**Tractability Score**: ${problem.tractability}/10
**Aristotle Suitable**: ${problem.aristotleSuitable ? 'Yes' : 'No'}

## Tags

${tagsSection}

## Related Problems

${relatedSection}

## References

${refsSection}

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on ${new Date().toISOString().split('T')[0]}*
`
}

/**
 * Load the registry
 */
function loadRegistry(): { version: string; problems: any[]; config: any } {
  const registryPath = path.resolve(process.cwd(), REGISTRY_FILE)

  if (fs.existsSync(registryPath)) {
    try {
      return JSON.parse(fs.readFileSync(registryPath, 'utf-8'))
    } catch {
      // Corrupted registry
    }
  }

  return {
    version: '1.0.0',
    problems: [],
    config: {
      maxActiveProblemsPerAgent: 1,
      oodaTimeoutMinutes: 60,
      attemptsBeforePivot: 5,
    },
  }
}

/**
 * Save the registry
 */
function saveRegistry(registry: { version: string; problems: any[]; config: any }): void {
  const registryPath = path.resolve(process.cwd(), REGISTRY_FILE)
  fs.writeFileSync(registryPath, JSON.stringify(registry, null, 2))
}

/**
 * Generate research entry for a single problem
 */
export function generateResearchEntry(
  problem: TransformedProblem,
  dryRun = false
): ResearchGenerationResult {
  const researchPath = path.resolve(process.cwd(), RESEARCH_DIR, problem.slug)

  const files: string[] = []

  // Check if research directory already exists
  if (fs.existsSync(researchPath)) {
    return {
      number: problem.number,
      slug: problem.slug,
      files: [],
      skipped: true,
      skipReason: 'Research directory already exists',
    }
  }

  if (dryRun) {
    return {
      number: problem.number,
      slug: problem.slug,
      files: [
        path.join(RESEARCH_DIR, problem.slug, 'problem.md'),
        path.join(RESEARCH_DIR, problem.slug, 'state.md'),
        path.join(RESEARCH_DIR, problem.slug, 'knowledge.md'),
      ],
      skipped: false,
    }
  }

  // Create research directory
  fs.mkdirSync(researchPath, { recursive: true })

  // Write problem.md
  const problemPath = path.join(researchPath, 'problem.md')
  fs.writeFileSync(problemPath, generateProblemMd(problem))
  files.push(path.join(RESEARCH_DIR, problem.slug, 'problem.md'))

  // Write state.md
  const statePath = path.join(researchPath, 'state.md')
  fs.writeFileSync(statePath, generateStateMd())
  files.push(path.join(RESEARCH_DIR, problem.slug, 'state.md'))

  // Write knowledge.md
  const knowledgePath = path.join(researchPath, 'knowledge.md')
  fs.writeFileSync(knowledgePath, generateKnowledgeMd(problem))
  files.push(path.join(RESEARCH_DIR, problem.slug, 'knowledge.md'))

  return {
    number: problem.number,
    slug: problem.slug,
    files,
    skipped: false,
  }
}

/**
 * Generate research entries for multiple problems
 */
export function generateResearchEntries(
  problems: TransformedProblem[],
  dryRun = false,
  updateRegistry = true
): ResearchGenerationResult[] {
  // Filter to only open problems
  const openProblems = problems.filter(p => p.status === 'OPEN')

  console.log(`Generating research entries for ${openProblems.length} open problems...`)

  const results: ResearchGenerationResult[] = []
  const newRegistryEntries: any[] = []

  for (const problem of openProblems) {
    const result = generateResearchEntry(problem, dryRun)
    results.push(result)

    if (!result.skipped) {
      console.log(`  Created: ${problem.slug}`)

      // Prepare registry entry
      newRegistryEntries.push({
        slug: problem.slug,
        phase: 'NEW',
        path: problem.tier === 'S' || problem.tier === 'A' ? 'fast' : 'full',
        started: new Date().toISOString(),
        status: 'active',
      })
    }
  }

  // Update registry with new entries
  if (updateRegistry && !dryRun && newRegistryEntries.length > 0) {
    const registry = loadRegistry()

    // Check for existing slugs to avoid duplicates
    const existingSlugs = new Set(registry.problems.map((p: any) => p.slug))

    for (const entry of newRegistryEntries) {
      if (!existingSlugs.has(entry.slug)) {
        registry.problems.push(entry)
      }
    }

    saveRegistry(registry)
    console.log(`  Updated registry with ${newRegistryEntries.length} new entries`)
  }

  const created = results.filter(r => !r.skipped).length
  const skipped = results.filter(r => r.skipped).length

  console.log(`Research generation complete: ${created} created, ${skipped} skipped`)

  return results
}

/**
 * Get research generation statistics
 */
export function getResearchStats(results: ResearchGenerationResult[]): {
  created: number
  skipped: number
  skipReasons: Record<string, number>
  filesCreated: number
} {
  const skipReasons: Record<string, number> = {}

  for (const result of results) {
    if (result.skipped && result.skipReason) {
      skipReasons[result.skipReason] = (skipReasons[result.skipReason] || 0) + 1
    }
  }

  return {
    created: results.filter(r => !r.skipped).length,
    skipped: results.filter(r => r.skipped).length,
    skipReasons,
    filesCreated: results.reduce((sum, r) => sum + r.files.length, 0),
  }
}
