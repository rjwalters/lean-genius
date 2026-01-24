import { ExternalLink, CheckCircle, CircleDot, Circle, MessageCircle, Megaphone } from 'lucide-react'
import { ERDOS_BADGE_INFO, type ErdosProblemStatus } from '@/types/proof'

interface ErdosProblemCardProps {
  erdosNumber: number
  erdosUrl?: string
  erdosProblemStatus?: ErdosProblemStatus
  solvedBy?: string
  solvedDate?: string
  prizeValue?: string
  forumUrl?: string
  announcementUrl?: string
}

function getStatusConfig(status?: ErdosProblemStatus) {
  const configs: Record<ErdosProblemStatus, { icon: typeof CheckCircle; label: string; className: string }> = {
    'solved': { icon: CheckCircle, label: 'Solved', className: 'text-green-400' },
    'disproved': { icon: CheckCircle, label: 'Disproved', className: 'text-purple-400' },
    'partially-solved': { icon: CircleDot, label: 'Partially Solved', className: 'text-yellow-400' },
    'open': { icon: Circle, label: 'Open', className: 'text-muted-foreground' }
  }
  return (status && configs[status]) ? configs[status] : configs['open']
}

export function ErdosProblemCard({
  erdosNumber,
  erdosUrl,
  erdosProblemStatus,
  solvedBy,
  solvedDate,
  prizeValue,
  forumUrl,
  announcementUrl
}: ErdosProblemCardProps) {
  const statusConfig = getStatusConfig(erdosProblemStatus)
  const StatusIcon = statusConfig.icon
  const problemUrl = erdosUrl || `https://www.erdosproblems.com/${erdosNumber}`

  const formatDate = (dateStr: string) => {
    const date = new Date(dateStr)
    return date.toLocaleDateString('en-US', {
      year: 'numeric',
      month: 'long'
    })
  }

  return (
    <div
      className="rounded-lg border overflow-hidden sm:col-span-2"
      style={{
        backgroundColor: `${ERDOS_BADGE_INFO.color}10`,
        borderColor: `${ERDOS_BADGE_INFO.color}30`
      }}
    >
      {/* Header */}
      <div className="px-4 py-3 flex items-center justify-between border-b" style={{ borderColor: `${ERDOS_BADGE_INFO.color}20` }}>
        <div className="flex items-center gap-2">
          <span className="text-lg font-bold" style={{ color: ERDOS_BADGE_INFO.color }}>
            E#{erdosNumber}
          </span>
        </div>
        <a
          href={problemUrl}
          target="_blank"
          rel="noopener noreferrer"
          className="text-sm flex items-center gap-1 hover:underline"
          style={{ color: ERDOS_BADGE_INFO.color }}
        >
          erdosproblems.com
          <ExternalLink className="h-3 w-3" />
        </a>
      </div>

      {/* Body */}
      <div className="px-4 py-3 space-y-2">
        {/* Status and Prize row */}
        <div className="flex items-center gap-3 text-sm">
          <span className={`flex items-center gap-1.5 ${statusConfig.className}`}>
            <StatusIcon className="h-4 w-4" />
            {statusConfig.label}
          </span>
          {prizeValue && (
            <>
              <span className="text-muted-foreground">·</span>
              <span className="text-foreground/90">{prizeValue} Prize</span>
            </>
          )}
        </div>

        {/* Solver attribution */}
        {solvedBy && (
          <div className="text-sm">
            <span className="text-muted-foreground">Solved by: </span>
            <span className="text-foreground/90 font-medium">{solvedBy}</span>
          </div>
        )}

        {/* Solved date */}
        {solvedDate && (
          <div className="text-sm text-muted-foreground">
            {formatDate(solvedDate)}
          </div>
        )}
      </div>

      {/* Footer - External links */}
      {(forumUrl || announcementUrl) && (
        <div className="px-4 py-2 flex items-center gap-3 border-t" style={{ borderColor: `${ERDOS_BADGE_INFO.color}20` }}>
          <a
            href={problemUrl}
            target="_blank"
            rel="noopener noreferrer"
            className="text-xs flex items-center gap-1 text-muted-foreground hover:text-foreground transition-colors"
          >
            <ExternalLink className="h-3 w-3" />
            Problem Page
          </a>
          {forumUrl && (
            <a
              href={forumUrl}
              target="_blank"
              rel="noopener noreferrer"
              className="text-xs flex items-center gap-1 text-muted-foreground hover:text-foreground transition-colors"
            >
              <MessageCircle className="h-3 w-3" />
              Forum
            </a>
          )}
          {announcementUrl && (
            <a
              href={announcementUrl}
              target="_blank"
              rel="noopener noreferrer"
              className="text-xs flex items-center gap-1 text-muted-foreground hover:text-foreground transition-colors"
            >
              <Megaphone className="h-3 w-3" />
              Announcement
            </a>
          )}
        </div>
      )}
    </div>
  )
}
