/**
 * Transform scraped problems to gallery/research format
 *
 * - Maps erdosproblems.com tags to gallery taxonomy
 * - Calculates tractability scores
 * - Generates slugs
 */

import type { ScrapedProblem, TransformedProblem } from './types'

/**
 * Tag mapping from erdosproblems.com to gallery taxonomy
 * Always adds 'erdos' tag
 */
const TAG_MAPPING: Record<string, string[]> = {
  // Number theory
  'number theory': ['number-theory'],
  'primes': ['number-theory', 'primes'],
  'divisors': ['number-theory', 'divisors'],
  'factorials': ['number-theory', 'factorial'],
  'binomial coefficients': ['number-theory', 'binomial'],
  'polynomials': ['algebra', 'polynomials'],
  'covering systems': ['number-theory', 'covering-systems'],
  'unit fractions': ['number-theory', 'fractions'],
  'egyptian fractions': ['number-theory', 'fractions'],

  // Combinatorics
  'combinatorics': ['combinatorics'],
  'additive combinatorics': ['combinatorics', 'additive'],
  'arithmetic progressions': ['combinatorics', 'arithmetic-progressions'],
  'sidon sets': ['number-theory', 'sidon-sets'],
  'ramsey theory': ['combinatorics', 'ramsey-theory'],
  'extremal combinatorics': ['combinatorics', 'extremal'],
  'set theory': ['combinatorics', 'set-theory'],
  'sum-free': ['combinatorics', 'sum-free'],
  'sequences': ['combinatorics', 'sequences'],

  // Graph theory
  'graph theory': ['graph-theory'],
  'hypergraphs': ['graph-theory', 'hypergraphs'],
  'chromatic number': ['graph-theory', 'chromatic'],
  'planar graphs': ['graph-theory', 'planar'],
  'bipartite graphs': ['graph-theory', 'bipartite'],
  'matchings': ['graph-theory', 'matchings'],
  'paths': ['graph-theory', 'paths'],
  'cycles': ['graph-theory', 'cycles'],
  'trees': ['graph-theory', 'trees'],
  'connectivity': ['graph-theory', 'connectivity'],

  // Geometry
  'geometry': ['geometry'],
  'distances': ['geometry', 'distances'],
  'convex geometry': ['geometry', 'convex'],
  'discrete geometry': ['geometry', 'discrete'],
  'circles': ['geometry', 'circles'],
  'collinearity': ['geometry', 'collinearity'],

  // Analysis
  'analysis': ['analysis'],
  'measure theory': ['analysis', 'measure-theory'],
  'probability': ['analysis', 'probability'],
  'asymptotics': ['analysis', 'asymptotics'],
  'density': ['analysis', 'density'],

  // Other
  'topology': ['topology'],
  'algebra': ['algebra'],
  'group theory': ['algebra', 'group-theory'],
  'logic': ['logic'],
}

/**
 * Generate a slug from problem number and title
 */
export function generateSlug(problem: ScrapedProblem): string {
  // Start with erdos-{number}
  let slug = `erdos-${problem.number}`

  // Try to add a descriptive suffix from tags or title
  if (problem.tags.length > 0) {
    // Use the most specific tag (not generic like "number theory")
    const specificTags = problem.tags.filter(
      t => !['number theory', 'combinatorics', 'graph theory', 'geometry', 'analysis'].includes(t.toLowerCase())
    )
    if (specificTags.length > 0) {
      const tagSlug = specificTags[0]
        .toLowerCase()
        .replace(/[^a-z0-9]+/g, '-')
        .replace(/^-|-$/g, '')
      if (tagSlug.length > 2 && tagSlug.length < 30) {
        slug = `${slug}-${tagSlug}`
      }
    }
  }

  return slug
}

/**
 * Map tags from erdosproblems.com to gallery taxonomy
 */
export function mapTags(tags: string[]): string[] {
  const mapped = new Set<string>(['erdos']) // Always include erdos tag

  for (const tag of tags) {
    const normalizedTag = tag.toLowerCase().trim()
    const mappedTags = TAG_MAPPING[normalizedTag]

    if (mappedTags) {
      for (const t of mappedTags) {
        mapped.add(t)
      }
    } else {
      // If no mapping, add the tag as-is with normalization
      const normalizedSlug = normalizedTag.replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '')
      if (normalizedSlug.length > 2) {
        mapped.add(normalizedSlug)
      }
    }
  }

  return Array.from(mapped).sort()
}

/**
 * Calculate tractability score (1-10)
 *
 * Higher scores mean more tractable for formalization:
 * - Solved problems get higher scores (we know there's a proof)
 * - Shorter statements are often simpler
 * - Some tags indicate classical/tractable problems
 */
export function calculateTractability(problem: ScrapedProblem): {
  score: number
  reason: string
  aristotleSuitable: boolean
} {
  let score = 5 // Default middle score
  const reasons: string[] = []

  // Status-based scoring
  if (problem.status === 'SOLVED') {
    score += 3
    reasons.push('solved (formalization target)')
  } else if (problem.status === 'PARTIALLY_SOLVED') {
    score += 1
    reasons.push('partially solved')
  } else {
    score -= 1
    reasons.push('open problem')
  }

  // Statement length scoring
  const statementLength = (problem.statement.latex || problem.statement.html).length
  if (statementLength < 200) {
    score += 2
    reasons.push('short statement')
  } else if (statementLength < 500) {
    score += 1
    reasons.push('moderate statement')
  } else if (statementLength > 1500) {
    score -= 1
    reasons.push('long statement')
  }

  // Tag-based scoring
  const tags = problem.tags.map(t => t.toLowerCase())

  // Higher tractability tags
  const tractableTags = ['classical', 'finite', 'elementary', 'easy', 'solved']
  for (const tag of tractableTags) {
    if (tags.some(t => t.includes(tag))) {
      score += 1
      reasons.push(`tag: ${tag}`)
      break
    }
  }

  // Lower tractability indicators
  const hardTags = ['conjecture', 'millennium', 'famous', 'open', 'unsolved', 'prize']
  for (const tag of hardTags) {
    if (tags.some(t => t.includes(tag))) {
      score -= 1
      reasons.push(`tag: ${tag}`)
      break
    }
  }

  // Prize indicates difficulty (famous open problems)
  if (problem.prize && problem.status !== 'SOLVED') {
    const amount = parseInt(problem.prize.replace(/[$,]/g, ''))
    if (amount >= 1000) {
      score -= 2
      reasons.push('large prize (famous open problem)')
    }
  }

  // Clamp score to 1-10
  score = Math.max(1, Math.min(10, score))

  // Aristotle suitability: solved problems with tractability >= 6
  // or open problems with very high tractability
  const aristotleSuitable =
    (problem.status === 'SOLVED' && score >= 5) ||
    (problem.status !== 'SOLVED' && score >= 8)

  return {
    score,
    reason: reasons.join('; '),
    aristotleSuitable,
  }
}

/**
 * Calculate tier based on tractability and status
 */
export function calculateTier(problem: ScrapedProblem, tractability: number): 'S' | 'A' | 'B' | 'C' | 'D' {
  // S-tier: Solved, high tractability, or already has progress
  if (problem.status === 'SOLVED' && tractability >= 7) {
    return 'S'
  }

  // A-tier: Solved or tractable open problems
  if (problem.status === 'SOLVED' || tractability >= 7) {
    return 'A'
  }

  // B-tier: Moderate tractability
  if (tractability >= 5) {
    return 'B'
  }

  // C-tier: Low tractability
  if (tractability >= 3) {
    return 'C'
  }

  // D-tier: Very hard / famous unsolved
  return 'D'
}

/**
 * Transform a scraped problem to the gallery/research format
 */
export function transformProblem(problem: ScrapedProblem): TransformedProblem {
  const slug = generateSlug(problem)
  const mappedTags = mapTags(problem.tags)
  const { score, reason, aristotleSuitable } = calculateTractability(problem)
  const tier = calculateTier(problem, score)

  return {
    ...problem,
    slug,
    mappedTags,
    tractability: score,
    tractabilityReason: reason,
    aristotleSuitable,
    tier,
  }
}

/**
 * Transform multiple problems
 */
export function transformProblems(problems: ScrapedProblem[]): TransformedProblem[] {
  return problems.map(transformProblem)
}

/**
 * Get transformation statistics
 */
export function getTransformStats(problems: TransformedProblem[]): {
  totalTags: number
  tierDistribution: Record<string, number>
  aristotleSuitableCount: number
  avgTractability: number
} {
  const tagSet = new Set<string>()
  const tierDist: Record<string, number> = { S: 0, A: 0, B: 0, C: 0, D: 0 }
  let tractabilitySum = 0

  for (const p of problems) {
    for (const tag of p.mappedTags) {
      tagSet.add(tag)
    }
    tierDist[p.tier]++
    tractabilitySum += p.tractability
  }

  return {
    totalTags: tagSet.size,
    tierDistribution: tierDist,
    aristotleSuitableCount: problems.filter(p => p.aristotleSuitable).length,
    avgTractability: problems.length > 0 ? tractabilitySum / problems.length : 0,
  }
}
