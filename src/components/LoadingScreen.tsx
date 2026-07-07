import { useEffect, useState } from 'react'
import { Link } from 'react-router-dom'
import { cn } from '@/lib/utils'
import loadingFactsData from '@/data/loading-facts.json'

/**
 * Entertaining loading screen (issue #35117, Track B).
 *
 * Shows a spinner plus a rotating math fact/quote sampled at build time from
 * the gallery's keyInsights (scripts/gallery/build-loading-facts.ts). Facts
 * with a slug deep-link to their proof page. Respects
 * `prefers-reduced-motion` by pinning a single static fact.
 */

interface LoadingFact {
  fact: string
  slug: string | null
  title: string
}

const FACTS = loadingFactsData as LoadingFact[]

const ROTATE_MS = 3500
const FADE_MS = 400

function prefersReducedMotion(): boolean {
  return (
    typeof window !== 'undefined' &&
    window.matchMedia?.('(prefers-reduced-motion: reduce)').matches
  )
}

function RotatingFact() {
  const [index, setIndex] = useState(() =>
    Math.floor(Math.random() * FACTS.length)
  )
  const [visible, setVisible] = useState(true)
  const [reducedMotion] = useState(prefersReducedMotion)

  useEffect(() => {
    if (reducedMotion || FACTS.length < 2) return
    const interval = setInterval(() => {
      setVisible(false)
      // Swap the fact once the fade-out completes, then fade back in
      setTimeout(() => {
        setIndex((i) => (i + 1) % FACTS.length)
        setVisible(true)
      }, FADE_MS)
    }, ROTATE_MS)
    return () => clearInterval(interval)
  }, [reducedMotion])

  const fact = FACTS[index]
  if (!fact) return null

  return (
    <div
      aria-live="polite"
      className={cn(
        'max-w-md min-h-24 px-6 text-center transition-opacity',
        visible ? 'opacity-100' : 'opacity-0'
      )}
      style={{ transitionDuration: `${FADE_MS}ms` }}
    >
      <p className="text-sm text-muted-foreground italic">
        &ldquo;{fact.fact}&rdquo;
      </p>
      {fact.slug ? (
        <Link
          to={`/proof/${fact.slug}`}
          className="mt-2 inline-block text-xs text-annotation hover:underline"
        >
          from {fact.title}
        </Link>
      ) : (
        <p className="mt-2 text-xs text-muted-foreground/70">
          &mdash; {fact.title}
        </p>
      )}
    </div>
  )
}

interface LoadingScreenProps {
  /** Status line under the spinner, e.g. "Loading proof..." */
  message?: string
  className?: string
}

export function LoadingScreen({ message, className }: LoadingScreenProps) {
  return (
    <div
      className={cn(
        'min-h-screen flex flex-col items-center justify-center gap-4',
        className
      )}
    >
      <div className="animate-spin rounded-full h-8 w-8 border-b-2 border-annotation" />
      {message && <p className="text-muted-foreground">{message}</p>}
      <RotatingFact />
    </div>
  )
}
