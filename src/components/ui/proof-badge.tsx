import { BADGE_INFO, type ProofBadge as ProofBadgeType } from '@/types/proof'
import { Tooltip, TooltipTrigger, TooltipContent } from './tooltip'

interface ProofBadgeProps {
  badge?: ProofBadgeType
  size?: 'sm' | 'md'
  showLabel?: boolean
  className?: string
}

/**
 * Displays a proof category badge with tooltip
 */
export function ProofBadge({
  badge,
  size = 'sm',
  showLabel = true,
  className = ''
}: ProofBadgeProps) {
  if (!badge) return null

  const info = BADGE_INFO[badge]
  if (!info) return null

  const sizeClasses = size === 'sm'
    ? 'px-2 py-0.5 text-xs'
    : 'px-3 py-1 text-sm'

  // Convert hex color to Tailwind-compatible rgba for background
  const style = {
    backgroundColor: `${info.color}20`, // 20 = 12.5% opacity in hex
    color: info.color
  }

  return (
    <Tooltip>
      <TooltipTrigger asChild>
        <span
          className={`inline-flex items-center gap-1 rounded font-medium ${sizeClasses} ${className}`}
          style={style}
        >
          <span>{info.emoji}</span>
          {showLabel && <span>{info.label}</span>}
        </span>
      </TooltipTrigger>
      <TooltipContent>
        <p>{info.description}</p>
      </TooltipContent>
    </Tooltip>
  )
}

interface BadgeFilterProps {
  selectedBadges: ProofBadgeType[]
  onToggle: (badge: ProofBadgeType) => void
  className?: string
}

/**
 * Filter buttons for selecting proof badges
 */
export function BadgeFilter({ selectedBadges, onToggle, className = '' }: BadgeFilterProps) {
  const badges: ProofBadgeType[] = ['original', 'mathlib-exploration', 'mathlib-extension', 'pedagogical', 'from-axioms', 'wip']

  return (
    <div className={`flex flex-wrap gap-2 ${className}`}>
      {badges.map((badge) => {
        const info = BADGE_INFO[badge]
        const isSelected = selectedBadges.length === 0 || selectedBadges.includes(badge)

        return (
          <button
            key={badge}
            onClick={() => onToggle(badge)}
            className={`inline-flex items-center gap-1 px-3 py-1.5 rounded-lg text-sm font-medium transition-all
              ${isSelected
                ? 'ring-2 ring-offset-2 ring-offset-background'
                : 'opacity-50 hover:opacity-75'
              }`}
            style={{
              backgroundColor: `${info.color}20`,
              color: info.color,
              ...(isSelected && { ringColor: info.color })
            }}
          >
            <span>{info.emoji}</span>
            <span className="hidden sm:inline">{info.label}</span>
          </button>
        )
      })}
    </div>
  )
}

interface MathlibIndicatorProps {
  dependencyCount?: number
  sorries?: number
  className?: string
}

/**
 * Shows Mathlib dependency count and sorry status
 */
export function MathlibIndicator({ dependencyCount, sorries, className = '' }: MathlibIndicatorProps) {
  if (dependencyCount === undefined && sorries === undefined) return null

  return (
    <div className={`flex items-center gap-3 text-xs text-muted-foreground ${className}`}>
      {dependencyCount !== undefined && (
        <Tooltip>
          <TooltipTrigger asChild>
            <span className="flex items-center gap-1">
              <span>📦</span>
              <span>{dependencyCount} Mathlib</span>
            </span>
          </TooltipTrigger>
          <TooltipContent>
            <p>Uses {dependencyCount} theorem{dependencyCount !== 1 ? 's' : ''} from Mathlib</p>
          </TooltipContent>
        </Tooltip>
      )}
      {sorries !== undefined && sorries > 0 && (
        <Tooltip>
          <TooltipTrigger asChild>
            <span className="flex items-center gap-1 text-orange-400">
              <span>⚠️</span>
              <span>{sorries} sorry</span>
            </span>
          </TooltipTrigger>
          <TooltipContent>
            <p>{sorries} incomplete proof step{sorries !== 1 ? 's' : ''}</p>
          </TooltipContent>
        </Tooltip>
      )}
      {sorries === 0 && (
        <Tooltip>
          <TooltipTrigger asChild>
            <span className="flex items-center gap-1 text-green-400">
              <span>✓</span>
              <span>Complete</span>
            </span>
          </TooltipTrigger>
          <TooltipContent>
            <p>No sorry statements - proof is complete</p>
          </TooltipContent>
        </Tooltip>
      )}
    </div>
  )
}
