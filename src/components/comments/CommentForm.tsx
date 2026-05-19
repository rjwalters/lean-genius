import { useId, useState } from 'react'
import { Button } from '@/components/ui/button'
import { MathText } from '@/components/ui/math'
import { cn } from '@/lib/utils'

interface CommentFormProps {
  onSubmit: (content: string) => Promise<void>
  onCancel?: () => void
  placeholder?: string
  initialValue?: string
  submitLabel?: string
}

export function CommentForm({
  onSubmit,
  onCancel,
  placeholder = 'Write a comment...',
  initialValue = '',
  submitLabel = 'Post',
}: CommentFormProps) {
  const [content, setContent] = useState(initialValue)
  const [showPreview, setShowPreview] = useState(false)
  const [isSubmitting, setIsSubmitting] = useState(false)
  const [error, setError] = useState<string | null>(null)
  const formId = useId()
  const writeTabId = `${formId}-write-tab`
  const previewTabId = `${formId}-preview-tab`
  const writePanelId = `${formId}-write-panel`
  const previewPanelId = `${formId}-preview-panel`

  const handleSubmit = async (e: React.FormEvent) => {
    e.preventDefault()
    if (!content.trim()) return

    setIsSubmitting(true)
    setError(null)

    try {
      await onSubmit(content.trim())
      setContent('')
      setShowPreview(false)
    } catch (err) {
      setError(err instanceof Error ? err.message : 'Failed to post comment')
    } finally {
      setIsSubmitting(false)
    }
  }

  return (
    <form onSubmit={handleSubmit} className="space-y-2">
      <div className="flex gap-2 text-xs border-b border-border" role="tablist" aria-label="Comment editor mode">
        <button
          type="button"
          id={writeTabId}
          role="tab"
          aria-selected={!showPreview}
          aria-controls={writePanelId}
          onClick={() => setShowPreview(false)}
          className={cn(
            'px-2 py-1 -mb-px border-b-2 transition-colors',
            !showPreview
              ? 'border-annotation text-foreground'
              : 'border-transparent text-muted-foreground hover:text-foreground'
          )}
        >
          Write
        </button>
        <button
          type="button"
          id={previewTabId}
          role="tab"
          aria-selected={showPreview}
          aria-controls={previewPanelId}
          onClick={() => setShowPreview(true)}
          className={cn(
            'px-2 py-1 -mb-px border-b-2 transition-colors',
            showPreview
              ? 'border-annotation text-foreground'
              : 'border-transparent text-muted-foreground hover:text-foreground'
          )}
        >
          Preview
        </button>
      </div>

      {showPreview ? (
        <div
          id={previewPanelId}
          role="tabpanel"
          aria-labelledby={previewTabId}
          className="min-h-[80px] p-2 border border-border rounded-md bg-muted/30"
        >
          {content ? (
            <div className="text-sm">
              <MathText>{content}</MathText>
            </div>
          ) : (
            <p className="text-sm text-muted-foreground">Nothing to preview</p>
          )}
        </div>
      ) : (
        <div id={writePanelId} role="tabpanel" aria-labelledby={writeTabId}>
          <textarea
            value={content}
            onChange={(e) => setContent(e.target.value)}
            placeholder={placeholder}
            className={cn(
              'w-full min-h-[80px] p-2 text-sm rounded-md border border-border',
              'bg-background text-foreground resize-y',
              'focus:outline-none focus:ring-2 focus:ring-annotation'
            )}
          />
        </div>
      )}

      {error && (
        <p className="text-xs text-red-400">{error}</p>
      )}

      <div className="flex items-center justify-between">
        <p className="text-xs text-muted-foreground">
          Supports LaTeX: $inline$ and $$block$$
        </p>
        <div className="flex gap-2">
          {onCancel && (
            <Button
              type="button"
              variant="ghost"
              size="sm"
              onClick={onCancel}
              disabled={isSubmitting}
            >
              Cancel
            </Button>
          )}
          <Button
            type="submit"
            size="sm"
            disabled={isSubmitting || !content.trim()}
          >
            {isSubmitting ? 'Posting...' : submitLabel}
          </Button>
        </div>
      </div>
    </form>
  )
}
