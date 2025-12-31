import { PHASE_INFO, type ResearchPhase } from '@/types/research'
import { Tooltip, TooltipTrigger, TooltipContent } from '@/components/ui/tooltip'

// OODA phases in order (excluding PIVOT which is a special transition)
const PHASE_ORDER: ResearchPhase[] = [
  'NEW',
  'OBSERVE',
  'ORIENT',
  'DECIDE',
  'ACT',
  'VERIFY',
  'LEARN',
  'BREAKTHROUGH'
]

interface PhaseProgressProps {
  currentPhase: ResearchPhase
  className?: string
}

/**
 * Horizontal progress bar showing OODA phases
 */
export function PhaseProgress({ currentPhase, className = '' }: PhaseProgressProps) {
  const currentIndex = PHASE_ORDER.indexOf(currentPhase)
  const isPivot = currentPhase === 'PIVOT'

  return (
    <div className={`flex items-center gap-1 ${className}`}>
      {PHASE_ORDER.map((phase, index) => {
        const info = PHASE_INFO[phase]
        const isCompleted = index < currentIndex
        const isCurrent = phase === currentPhase
        const isFuture = index > currentIndex

        return (
          <Tooltip key={phase}>
            <TooltipTrigger asChild>
              <div
                className={`h-2 flex-1 rounded-full transition-all ${
                  isCurrent ? 'ring-2 ring-offset-1 ring-offset-background' : ''
                }`}
                style={{
                  backgroundColor: isCompleted || isCurrent
                    ? info.color
                    : isFuture
                    ? `${info.color}30`
                    : info.color,
                  opacity: isFuture ? 0.3 : 1
                }}
              />
            </TooltipTrigger>
            <TooltipContent>
              <p className="font-medium">{info.label}</p>
              <p className="text-muted-foreground text-sm">{info.description}</p>
              {isCompleted && <p className="text-green-400 text-xs mt-1">Completed</p>}
              {isCurrent && <p className="text-yellow-400 text-xs mt-1">Current</p>}
            </TooltipContent>
          </Tooltip>
        )
      })}

      {isPivot && (
        <div className="ml-2 text-xs text-red-400 font-medium">
          (Pivoting)
        </div>
      )}
    </div>
  )
}

interface PhaseProgressVerticalProps {
  currentPhase: ResearchPhase
  className?: string
}

/**
 * Vertical progress indicator for sidebar navigation
 */
export function PhaseProgressVertical({ currentPhase, className = '' }: PhaseProgressVerticalProps) {
  const currentIndex = PHASE_ORDER.indexOf(currentPhase)

  return (
    <div className={`flex flex-col gap-2 ${className}`}>
      {PHASE_ORDER.map((phase, index) => {
        const info = PHASE_INFO[phase]
        const isCompleted = index < currentIndex
        const isCurrent = phase === currentPhase
        const isFuture = index > currentIndex

        return (
          <div
            key={phase}
            className={`flex items-center gap-3 py-1 ${
              isFuture ? 'opacity-40' : ''
            }`}
          >
            <div
              className={`h-3 w-3 rounded-full flex-shrink-0 ${
                isCurrent ? 'ring-2 ring-offset-2 ring-offset-background' : ''
              }`}
              style={{
                backgroundColor: info.color
              }}
            />
            <span
              className={`text-sm ${
                isCurrent ? 'font-medium' : ''
              }`}
              style={{ color: isCurrent ? info.color : undefined }}
            >
              {info.label}
            </span>
            {isCompleted && (
              <span className="text-xs text-green-400 ml-auto">Done</span>
            )}
            {isCurrent && (
              <span className="text-xs text-yellow-400 ml-auto">Now</span>
            )}
          </div>
        )
      })}
    </div>
  )
}
