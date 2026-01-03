import { Link } from 'react-router-dom'
import { Github } from 'lucide-react'

// Format ISO date to readable format
function formatBuildTime(isoString: string): string {
  try {
    const date = new Date(isoString)
    return date.toLocaleDateString('en-US', {
      year: 'numeric',
      month: 'short',
      day: 'numeric',
      hour: '2-digit',
      minute: '2-digit',
      timeZoneName: 'short'
    })
  } catch {
    return isoString
  }
}

export function Footer() {
  const commitHash = __COMMIT_HASH__
  const buildTime = __BUILD_TIME__

  return (
    <footer className="border-t border-border">
      <div className="max-w-6xl mx-auto px-6 py-8 text-center text-sm text-muted-foreground">
        <p>
          Proofs are formalized in{' '}
          <a
            href="https://lean-lang.org/"
            target="_blank"
            rel="noopener noreferrer"
            className="text-annotation hover:underline"
          >
            Lean 4
          </a>{' '}
          with{' '}
          <a
            href="https://github.com/leanprover-community/mathlib4"
            target="_blank"
            rel="noopener noreferrer"
            className="text-annotation hover:underline"
          >
            Mathlib
          </a>
          {' · '}
          <Link to="/about" className="text-annotation hover:underline">
            About
          </Link>
          {' · '}
          <a
            href="https://github.com/rjwalters/lean-genius"
            target="_blank"
            rel="noopener noreferrer"
            className="inline-flex items-center gap-1 text-annotation hover:underline"
          >
            <Github className="h-3.5 w-3.5" />
            <span>GitHub</span>
          </a>
        </p>
        <p className="mt-2 text-xs text-muted-foreground/60">
          <a
            href={`https://github.com/rjwalters/lean-genius/commit/${commitHash}`}
            target="_blank"
            rel="noopener noreferrer"
            className="font-mono hover:text-muted-foreground"
          >
            {commitHash}
          </a>
          {' · '}
          <span>Deployed {formatBuildTime(buildTime)}</span>
        </p>
      </div>
    </footer>
  )
}
