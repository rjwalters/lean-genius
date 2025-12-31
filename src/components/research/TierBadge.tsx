import { TIER_INFO, type ValueTier } from '@/types/research'
import { Tooltip, TooltipTrigger, TooltipContent } from '@/components/ui/tooltip'

interface TierBadgeProps {
  tier: ValueTier
  size?: 'sm' | 'md'
  showLabel?: boolean
  className?: string
}

/**
 * Displays a value tier badge (S/A/B/C/D)
 */
export function TierBadge({
  tier,
  size = 'sm',
  showLabel = true,
  className = ''
}: TierBadgeProps) {
  const info = TIER_INFO[tier]

  const sizeClasses = size === 'sm'
    ? 'h-5 w-5 text-[10px]'
    : 'h-6 w-6 text-xs'

  return (
    <Tooltip>
      <TooltipTrigger asChild>
        <span className={`inline-flex items-center gap-1.5 ${className}`}>
          <span
            className={`inline-flex items-center justify-center rounded font-bold ${sizeClasses}`}
            style={{
              backgroundColor: `${info.color}25`,
              color: info.color,
              border: `1.5px solid ${info.color}50`
            }}
          >
            {tier}
          </span>
          {showLabel && (
            <span className="text-xs text-muted-foreground">{info.label}</span>
          )}
        </span>
      </TooltipTrigger>
      <TooltipContent>
        <p className="font-medium">Tier {tier}: {info.label}</p>
        <p className="text-muted-foreground text-sm">{info.description}</p>
      </TooltipContent>
    </Tooltip>
  )
}
