import { useCallback, useEffect, useRef, useState } from 'react'

/** How many items to reveal initially and per subsequent batch. */
const DEFAULT_BATCH_SIZE = 60

/**
 * Reveal a long list in batches instead of mounting every item at once.
 *
 * The gallery grids render one card per entry with no upper bound — the proof
 * gallery alone mounts ~1,600 cards, which React must reconcile on every
 * filter, sort or search change. This hook caps what is mounted: the first
 * `batchSize` items render immediately, and more are appended as the user
 * scrolls a sentinel element into view (or clicks "show all").
 *
 * This is deliberately *not* windowed virtualization. The cards are
 * variable-height and the grid's column count is responsive, which makes
 * absolute-positioned windowing fragile; and because revealed items stay
 * mounted, native scrolling, in-page anchors and scroll restoration keep
 * working. The win is bounded initial work per filter change, not bounded
 * memory over a long scroll.
 *
 * Usage:
 *
 * ```tsx
 * const { visible, hasMore, remaining, sentinelRef, showAll } = useIncrementalList(items)
 * // …render `visible`…
 * {hasMore && <div ref={sentinelRef} />}
 * ```
 *
 * The count resets to one batch whenever `items` changes identity, so a new
 * search result always starts from the top.
 *
 * @param items The full, already-filtered list.
 * @param batchSize Items per batch (default 60).
 */
export function useIncrementalList<T>(
  items: readonly T[],
  batchSize: number = DEFAULT_BATCH_SIZE
): {
  /** The prefix of `items` that should be rendered. */
  visible: readonly T[]
  /** True while items remain unrevealed. */
  hasMore: boolean
  /** How many items are still hidden. */
  remaining: number
  /** Callback ref for the sentinel element that triggers the next batch. */
  sentinelRef: (node: HTMLElement | null) => void
  /** Reveal everything at once (escape hatch for find-in-page / Ctrl-F). */
  showAll: () => void
} {
  const [count, setCount] = useState(batchSize)

  // A new filter/sort/search result is a new array identity — start over so the
  // user is looking at the top of the new list, not deep into the old one.
  // Adjusted during render rather than in an effect: React re-runs this
  // component immediately without committing the stale count or painting the
  // intermediate state, so there is no cascading-render pass.
  // https://react.dev/reference/react/useState#storing-information-from-previous-renders
  const [prevItems, setPrevItems] = useState(items)
  if (prevItems !== items) {
    setPrevItems(items)
    setCount(batchSize)
  }

  const observerRef = useRef<IntersectionObserver | null>(null)

  const sentinelRef = useCallback(
    (node: HTMLElement | null) => {
      observerRef.current?.disconnect()
      observerRef.current = null
      if (!node) return

      // Without IntersectionObserver there is no scroll trigger, so fall back
      // to rendering everything rather than stranding the user mid-list.
      if (typeof IntersectionObserver === 'undefined') {
        setCount(Number.MAX_SAFE_INTEGER)
        return
      }

      const observer = new IntersectionObserver(
        (entries) => {
          if (entries.some((entry) => entry.isIntersecting)) {
            setCount((current) => current + batchSize)
          }
        },
        // Start loading before the sentinel is actually on screen so the next
        // batch is usually mounted by the time the user scrolls to it.
        { rootMargin: '800px' }
      )
      observer.observe(node)
      observerRef.current = observer
    },
    [batchSize]
  )

  useEffect(() => {
    return () => {
      observerRef.current?.disconnect()
      observerRef.current = null
    }
  }, [])

  const showAll = useCallback(() => setCount(Number.MAX_SAFE_INTEGER), [])

  const clamped = Math.min(count, items.length)
  return {
    visible: count >= items.length ? items : items.slice(0, count),
    hasMore: clamped < items.length,
    remaining: items.length - clamped,
    sentinelRef,
    showAll,
  }
}
