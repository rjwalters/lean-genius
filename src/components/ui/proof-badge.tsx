import { BADGE_INFO, WIEDIJK_BADGE_INFO, WIEDIJK_THEOREMS, type ProofBadge as ProofBadgeType } from '@/types/proof'
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

interface WiedijkBadgeProps {
  number?: number
  size?: 'sm' | 'md'
  className?: string
}

/**
 * Displays a medallion badge for Wiedijk's 100 Famous Theorems
 */
export function WiedijkBadge({
  number,
  size = 'sm',
  className = ''
}: WiedijkBadgeProps) {
  if (!number) return null

  const sizeClasses = size === 'sm'
    ? 'h-6 w-6 text-[10px]'
    : 'h-8 w-8 text-xs'

  const paddedNumber = number.toString().padStart(2, '0')
  const theoremName = WIEDIJK_THEOREMS[number] || `Theorem #${number}`

  return (
    <Tooltip>
      <TooltipTrigger asChild>
        <span
          className={`inline-flex items-center justify-center rounded-full font-bold shrink-0 ${sizeClasses} ${className}`}
          style={{
            backgroundColor: `${WIEDIJK_BADGE_INFO.color}25`,
            color: WIEDIJK_BADGE_INFO.textColor,
            border: `1.5px solid ${WIEDIJK_BADGE_INFO.color}50`
          }}
        >
          {paddedNumber}
        </span>
      </TooltipTrigger>
      <TooltipContent>
        <p className="font-medium">Wiedijk's 100 Famous Theorems #{number}</p>
        <p className="text-muted-foreground">{theoremName}</p>
        <a
          href={`${WIEDIJK_BADGE_INFO.url}#${number}`}
          target="_blank"
          rel="noopener noreferrer"
          className="text-xs text-annotation hover:underline mt-1 block"
          onClick={(e) => e.stopPropagation()}
        >
          View on Wiedijk's list →
        </a>
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
  const badges: ProofBadgeType[] = ['original', 'mathlib', 'pedagogical', 'from-axioms', 'fallacy', 'wip']

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
