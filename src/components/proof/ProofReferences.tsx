import { BookOpen, ExternalLink } from 'lucide-react'
import type { ProofReference } from '@/types/proof'

interface ProofReferencesProps {
  references?: ProofReference[]
}

/**
 * Format the author list from a ProofReference into a display string.
 * Handles: string[], single string, legacy `author` field, or undefined.
 */
function formatAuthors(reference: ProofReference): string | undefined {
  if (reference.authors) {
    if (Array.isArray(reference.authors)) {
      return reference.authors.join(', ')
    }
    return reference.authors
  }
  if (reference.author) {
    return reference.author
  }
  return undefined
}

/**
 * Format a year value (string or number) into a display string.
 */
function formatYear(year: string | number | undefined): string | undefined {
  if (year == null) return undefined
  return String(year)
}

/**
 * Build a formatted citation string from structured fields.
 * Returns undefined if the reference has no structured fields to format.
 */
function formatStructuredCitation(reference: ProofReference): string | undefined {
  const parts: string[] = []

  const authors = formatAuthors(reference)
  if (authors) parts.push(authors)

  if (reference.title) {
    parts.push(`"${reference.title}"`)
  }

  if (reference.venue) {
    parts.push(reference.venue)
  }

  const details: string[] = []
  if (reference.volume) details.push(`vol. ${reference.volume}`)
  if (reference.pages) details.push(`pp. ${reference.pages}`)
  const year = formatYear(reference.year)
  if (year) details.push(year)
  if (details.length > 0) {
    parts.push(details.join(', '))
  } else if (year) {
    parts.push(`(${year})`)
  }

  if (parts.length === 0) return undefined
  return parts.join('. ') + '.'
}

/**
 * Render a single reference entry.
 */
function ReferenceEntry({ reference, index }: { reference: ProofReference; index: number }) {
  // Legacy schema: use citation field directly
  const legacyCitation = reference.citation
  const structuredCitation = formatStructuredCitation(reference)
  const displayText = legacyCitation || structuredCitation

  // Fallback for ad hoc {text, url} references that have no structured or legacy fields
  const textFallback = !displayText ? reference.text : undefined

  // If the reference has no displayable content at all, skip it
  if (!displayText && !textFallback && !reference.note) return null

  // Build link targets
  const doiUrl = reference.doi ? `https://doi.org/${reference.doi}` : undefined
  const arxivUrl = reference.arxiv ? `https://arxiv.org/abs/${reference.arxiv}` : undefined
  const directUrl = reference.url

  // Pick primary link: DOI > arXiv > direct URL
  const primaryUrl = doiUrl || arxivUrl || directUrl

  return (
    <li className="flex gap-3 text-sm">
      <span className="shrink-0 h-5 w-5 rounded-full bg-blue-500/20 text-blue-400 text-xs flex items-center justify-center font-medium mt-0.5">
        {index + 1}
      </span>
      <div className="min-w-0 space-y-1">
        {/* Citation text */}
        {displayText && (
          <p className="text-foreground/90 leading-relaxed">
            {primaryUrl ? (
              <a
                href={primaryUrl}
                target="_blank"
                rel="noopener noreferrer"
                className="hover:text-blue-400 transition-colors"
              >
                {displayText}
              </a>
            ) : (
              displayText
            )}
          </p>
        )}

        {/* Fallback: plain text (and optional URL) for ad hoc {text, url} references */}
        {textFallback && (
          <p className="text-foreground/90 leading-relaxed">
            {reference.url ? (
              <a
                href={reference.url}
                target="_blank"
                rel="noopener noreferrer"
                className="hover:text-blue-400 transition-colors"
              >
                {textFallback}
              </a>
            ) : (
              textFallback
            )}
          </p>
        )}

        {/* Note */}
        {reference.note && (
          <p className="text-xs text-muted-foreground leading-relaxed italic">
            {reference.note}
          </p>
        )}

        {/* Link badges */}
        <div className="flex flex-wrap gap-2">
          {doiUrl && (
            <a
              href={doiUrl}
              target="_blank"
              rel="noopener noreferrer"
              className="inline-flex items-center gap-1 text-xs px-2 py-0.5 rounded bg-blue-500/10 text-blue-400 border border-blue-500/20 hover:bg-blue-500/20 transition-colors"
            >
              <ExternalLink className="h-3 w-3" />
              DOI
            </a>
          )}
          {arxivUrl && (
            <a
              href={arxivUrl}
              target="_blank"
              rel="noopener noreferrer"
              className="inline-flex items-center gap-1 text-xs px-2 py-0.5 rounded bg-orange-500/10 text-orange-400 border border-orange-500/20 hover:bg-orange-500/20 transition-colors"
            >
              <ExternalLink className="h-3 w-3" />
              arXiv
            </a>
          )}
          {directUrl && !doiUrl && !arxivUrl && (
            <a
              href={directUrl}
              target="_blank"
              rel="noopener noreferrer"
              className="inline-flex items-center gap-1 text-xs px-2 py-0.5 rounded bg-muted/50 text-muted-foreground border border-border/50 hover:bg-muted/70 transition-colors"
            >
              <ExternalLink className="h-3 w-3" />
              Link
            </a>
          )}
          {reference.key && (
            <span className="text-xs px-2 py-0.5 rounded bg-muted/30 text-muted-foreground font-mono">
              [{reference.key}]
            </span>
          )}
        </div>
      </div>
    </li>
  )
}

/**
 * Renders a bibliography / references section for a proof.
 * Handles modern, legacy, and ad hoc reference schemas gracefully.
 * Renders nothing when references is absent, empty, or has no displayable entries.
 */
export function ProofReferences({ references }: ProofReferencesProps) {
  if (!references || references.length === 0) return null

  return (
    <section>
      <h3 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground mb-3 flex items-center gap-2">
        <BookOpen className="h-4 w-4 text-blue-400" />
        References
      </h3>
      <ul className="space-y-3">
        {references.map((reference, i) => (
          <ReferenceEntry key={reference.key || reference.doi || reference.title || i} reference={reference} index={i} />
        ))}
      </ul>
    </section>
  )
}
