/**
 * Footer for a grid rendered in batches by `useIncrementalList`.
 *
 * Renders an invisible sentinel that the hook's IntersectionObserver watches to
 * append the next batch as the user scrolls, plus an explicit "show all"
 * control. The button is not just a fallback: browser find-in-page only
 * searches mounted DOM, so a user who wants Ctrl-F across the whole result set
 * needs one click to get there.
 */
export function LoadMore({
  sentinelRef,
  remaining,
  onShowAll,
  noun,
}: {
  sentinelRef: (node: HTMLElement | null) => void
  remaining: number
  onShowAll: () => void
  /** Plural noun for the label, e.g. "proofs", "problems". */
  noun: string
}) {
  return (
    <div ref={sentinelRef} className="flex flex-col items-center gap-2 py-8">
      <p className="text-sm text-muted-foreground" aria-live="polite">
        {remaining.toLocaleString()} more {noun} below
      </p>
      <button
        type="button"
        onClick={onShowAll}
        className="text-sm text-annotation hover:underline"
      >
        Show all
      </button>
    </div>
  )
}
