import { Link } from 'react-router-dom'
import { PhaseIndicator } from './PhaseIndicator'
import { TierBadge } from './TierBadge'
import { PHASE_INFO } from '@/types/research'
import type { ResearchListing } from '@/types/research'
import { ArrowRight, FlaskConical, CheckCircle2, Zap } from 'lucide-react'

interface ResearchCardProps {
  problem: ResearchListing
}

/**
 * Card component for displaying a research problem in the gallery
 */
export function ResearchCard({ problem }: ResearchCardProps) {
  const isGraduated = problem.status === 'graduated'
  const isBreakthrough = problem.phase === 'BREAKTHROUGH'
  const phaseInfo = PHASE_INFO[problem.phase]

  return (
    <Link
      to={`/research/${problem.slug}`}
      className="group block bg-card border border-border rounded-xl p-6 hover:border-annotation/50 hover:bg-card/80 transition-all"
    >
      {/* Header with badges */}
      <div className="flex items-start justify-between mb-4">
        <div className="flex items-center gap-2">
          <PhaseIndicator phase={problem.phase} size="sm" />
          {isGraduated && (
            <span className="inline-flex items-center gap-1 px-2 py-0.5 rounded text-xs font-medium bg-green-500/20 text-green-400">
              <CheckCircle2 className="h-3 w-3" />
              Graduated
            </span>
          )}
        </div>
        <TierBadge tier={problem.tier} size="sm" showLabel={false} />
      </div>

      {/* Title with icon */}
      <div className="flex items-start gap-3 mb-3">
        <div
          className="h-10 w-10 rounded-lg flex items-center justify-center flex-shrink-0"
          style={{ backgroundColor: `${phaseInfo.color}20` }}
        >
          {isBreakthrough ? (
            <Zap className="h-5 w-5" style={{ color: phaseInfo.color }} />
          ) : (
            <FlaskConical className="h-5 w-5" style={{ color: phaseInfo.color }} />
          )}
        </div>
        <h3 className="text-lg font-semibold group-hover:text-annotation transition-colors pt-1">
          {problem.title}
        </h3>
      </div>

      {/* Date */}
      <p className="text-xs text-muted-foreground mb-2">
        Started {new Date(problem.started).toLocaleDateString()}
        {problem.completed && (
          <> · Completed {new Date(problem.completed).toLocaleDateString()}</>
        )}
      </p>

      {/* Description */}
      <p className="text-sm text-muted-foreground mb-4 line-clamp-3">
        {problem.description}
      </p>

      {/* Stats */}
      <div className="flex items-center gap-4 text-xs text-muted-foreground mb-4">
        <span>{problem.approachCount} approach{problem.approachCount !== 1 ? 'es' : ''}</span>
        <span>{problem.attemptCount} attempt{problem.attemptCount !== 1 ? 's' : ''}</span>
        {problem.significance && (
          <span>Significance: {problem.significance}/10</span>
        )}
      </div>

      {/* Tags */}
      <div className="flex flex-wrap gap-2">
        {problem.tags.slice(0, 3).map((tag) => (
          <span
            key={tag}
            className="px-2 py-0.5 bg-muted rounded text-xs text-muted-foreground"
          >
            {tag}
          </span>
        ))}
        {problem.tags.length > 3 && (
          <span className="text-xs text-muted-foreground">
            +{problem.tags.length - 3} more
          </span>
        )}
      </div>

      {/* Hover action */}
      <div className="mt-4 flex items-center text-sm text-annotation opacity-0 group-hover:opacity-100 transition-opacity">
        <span>View research</span>
        <ArrowRight className="h-4 w-4 ml-1" />
      </div>
    </Link>
  )
}
