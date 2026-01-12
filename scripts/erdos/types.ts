/**
 * Types for Erdos Problems scraping and generation pipeline
 */

// Re-export relevant types from proof types
export type { ErdosProblemStatus, ProofMeta, ProofBadge } from '../../src/types/proof'

/**
 * Problem status as scraped from erdosproblems.com
 */
export type ScrapedStatus = 'OPEN' | 'SOLVED' | 'PARTIALLY_SOLVED'

/**
 * Raw problem data scraped from erdosproblems.com
 */
export interface ScrapedProblem {
  /** Problem number (1-1135+) */
  number: number
  /** Problem title extracted from page */
  title: string
  /** Problem status */
  status: ScrapedStatus
  /** Prize amount if any (e.g., "$500") */
  prize?: string
  /** Mathematical statement */
  statement: {
    /** Raw LaTeX source */
    latex: string
    /** Rendered HTML for reference */
    html: string
  }
  /** Tags from erdosproblems.com */
  tags: string[]
  /** Related problem numbers */
  relatedProblems: number[]
  /** References and citations */
  references: Array<{
    /** Citation key (e.g., "Er56") */
    key: string
    /** Full citation text */
    citation?: string
  }>
  /** Last edited date */
  lastEdited?: string
  /** OEIS sequence numbers if any */
  oeis?: string[]
  /** Source URL */
  sourceUrl: string
}

/**
 * Transformed problem with mapped tags and tractability
 */
export interface TransformedProblem extends ScrapedProblem {
  /** Generated slug for file paths */
  slug: string
  /** Tags mapped to gallery taxonomy */
  mappedTags: string[]
  /** Tractability score (1-10) */
  tractability: number
  /** Reason for tractability score */
  tractabilityReason: string
  /** Whether suitable for Aristotle */
  aristotleSuitable: boolean
  /** Tier classification (S/A/B/C/D) */
  tier: 'S' | 'A' | 'B' | 'C' | 'D'
}

/**
 * Cache manifest entry
 */
export interface CacheEntry {
  /** Problem number */
  number: number
  /** Last fetch timestamp */
  fetchedAt: string
  /** HTTP status code */
  status: number
  /** Whether LaTeX was fetched */
  hasLatex: boolean
}

/**
 * Cache manifest
 */
export interface CacheManifest {
  version: string
  lastUpdate: string
  entries: Record<number, CacheEntry>
}

/**
 * Deduplication result
 */
export interface DedupeResult {
  /** Problem number */
  number: number
  /** Whether it's a duplicate */
  isDuplicate: boolean
  /** Type of existing entry if duplicate */
  existingType?: 'gallery' | 'research' | 'both'
  /** Existing slug if duplicate */
  existingSlug?: string
  /** Match reason */
  matchReason?: string
}

/**
 * Gallery generation result
 */
export interface GalleryGenerationResult {
  /** Problem number */
  number: number
  /** Generated slug */
  slug: string
  /** Files created */
  files: string[]
  /** Whether it was skipped */
  skipped: boolean
  /** Skip reason if applicable */
  skipReason?: string
}

/**
 * Research generation result
 */
export interface ResearchGenerationResult {
  /** Problem number */
  number: number
  /** Generated slug */
  slug: string
  /** Files created */
  files: string[]
  /** Whether it was skipped */
  skipped: boolean
  /** Skip reason if applicable */
  skipReason?: string
}

/**
 * Aristotle job candidate
 */
export interface AristotleCandidate {
  /** Problem ID (slug) */
  problemId: string
  /** Erdos problem number */
  erdosNumber: number
  /** Source of the problem */
  source: string
  /** Tractability score */
  tractabilityScore: number
  /** Why this is suitable */
  reason: string
  /** Suggested Lean file path */
  suggestedFile: string
  /** Additional notes */
  notes?: string
}

/**
 * CLI options
 */
export interface CliOptions {
  /** Preview without writing */
  dryRun: boolean
  /** Range of problems to process (e.g., "1-100") */
  range?: string
  /** Process next N uncached problems */
  batch?: number
  /** Slow/polite mode - 60s between requests */
  slow: boolean
  /** Use Playwright browser instead of fetch */
  playwright: boolean
  /** Ignore cache, fetch fresh */
  refresh: boolean
  /** Only generate gallery */
  galleryOnly: boolean
  /** Only generate research */
  researchOnly: boolean
  /** Show status only */
  status: boolean
  /** Verbose output */
  verbose: boolean
}

/**
 * Pipeline statistics
 */
export interface PipelineStats {
  /** Total problems scraped */
  totalScraped: number
  /** Solved problems */
  solvedCount: number
  /** Open problems */
  openCount: number
  /** Partially solved */
  partiallySolvedCount: number
  /** Gallery entries created */
  galleryCreated: number
  /** Gallery entries skipped (duplicates) */
  gallerySkipped: number
  /** Research entries created */
  researchCreated: number
  /** Research entries skipped */
  researchSkipped: number
  /** Aristotle candidates */
  aristotleCandidates: number
  /** Errors encountered */
  errors: number
}
