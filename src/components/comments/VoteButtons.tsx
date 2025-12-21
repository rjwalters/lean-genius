import { ChevronUp, ChevronDown } from 'lucide-react'
import { cn } from '@/lib/utils'

interface VoteButtonsProps {
  score: number
  userVote: 1 | -1 | null
  onVote: (value: 1 | -1 | 0) => void
  disabled?: boolean
}

export function VoteButtons({ score, userVote, onVote, disabled }: VoteButtonsProps) {
  const handleUpvote = () => {
    if (disabled) return
    // If already upvoted, remove vote (toggle off)
    onVote(userVote === 1 ? 0 : 1)
  }

  const handleDownvote = () => {
    if (disabled) return
    // If already downvoted, remove vote (toggle off)
    onVote(userVote === -1 ? 0 : -1)
  }

  return (
    <div className="flex flex-col items-center gap-0.5 mr-2">
      <button
        onClick={handleUpvote}
        disabled={disabled}
        className={cn(
          'p-0.5 rounded transition-colors',
          disabled
            ? 'cursor-not-allowed opacity-50'
            : 'hover:bg-muted cursor-pointer',
          userVote === 1 && 'text-orange-500'
        )}
        aria-label="Upvote"
      >
        <ChevronUp className="h-4 w-4" />
      </button>
      <span
        className={cn(
          'text-xs font-medium min-w-[1.5rem] text-center',
          score > 0 && 'text-orange-500',
          score < 0 && 'text-blue-500',
          score === 0 && 'text-muted-foreground'
        )}
      >
        {score}
      </span>
      <button
        onClick={handleDownvote}
        disabled={disabled}
        className={cn(
          'p-0.5 rounded transition-colors',
          disabled
            ? 'cursor-not-allowed opacity-50'
            : 'hover:bg-muted cursor-pointer',
          userVote === -1 && 'text-blue-500'
        )}
        aria-label="Downvote"
      >
        <ChevronDown className="h-4 w-4" />
      </button>
    </div>
  )
}
