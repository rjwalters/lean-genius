import { PHASE_INFO, type ResearchPhase } from '@/types/research'
import { Tooltip, TooltipTrigger, TooltipContent } from '@/components/ui/tooltip'
import {
  Plus,
  Eye,
  Compass,
  GitBranch,
  Play,
  CheckCircle,
  BookOpen,
  Sparkles,
  RotateCcw
} from 'lucide-react'

const PHASE_ICONS: Record<ResearchPhase, typeof Plus> = {
  NEW: Plus,
  OBSERVE: Eye,
  ORIENT: Compass,
  DECIDE: GitBranch,
  ACT: Play,
  VERIFY: CheckCircle,
  LEARN: BookOpen,
  BREAKTHROUGH: Sparkles,
  PIVOT: RotateCcw
}

interface PhaseIndicatorProps {
  phase: ResearchPhase
  size?: 'sm' | 'md' | 'lg'
  showLabel?: boolean
  className?: string
}

/**
 * Displays a colored badge indicating the current OODA phase
 */
export function PhaseIndicator({
  phase,
  size = 'sm',
  showLabel = true,
  className = ''
}: PhaseIndicatorProps) {
  const info = PHASE_INFO[phase]
  const Icon = PHASE_ICONS[phase]

  const sizeClasses = {
    sm: 'px-2 py-0.5 text-xs',
    md: 'px-3 py-1 text-sm',
    lg: 'px-4 py-1.5 text-base'
  }

  const iconSizes = {
    sm: 'h-3 w-3',
    md: 'h-4 w-4',
    lg: 'h-5 w-5'
  }

  return (
    <Tooltip>
      <TooltipTrigger asChild>
        <span
          className={`inline-flex items-center gap-1.5 rounded-full font-medium ${sizeClasses[size]} ${className}`}
          style={{
            backgroundColor: `${info.color}20`,
            color: info.color
          }}
        >
          <Icon className={iconSizes[size]} />
          {showLabel && <span>{info.label}</span>}
        </span>
      </TooltipTrigger>
      <TooltipContent>
        <p className="font-medium">{info.label} Phase</p>
        <p className="text-muted-foreground text-sm">{info.description}</p>
      </TooltipContent>
    </Tooltip>
  )
}
