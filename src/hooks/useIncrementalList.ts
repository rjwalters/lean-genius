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
 * @param batchSizeOrOptions Items per batch (default 60), or an options object
 *   (`batchSize`, `persistKey`, `restore`) — see `IncrementalListOptions`.
 */
export interface IncrementalListOptions {
  /** Items per batch (default 60). */
  batchSize?: number
  /**
   * When set, the revealed count is remembered in `sessionStorage` under this
   * key (use the route's pathname + search) so a Back navigation can mount
   * the same depth again before scroll restoration runs. See
   * `useScrollRestoration`.
   */
  persistKey?: string
  /**
   * True to start from the remembered count for `persistKey` (a POP
   * navigation); false to start from one batch as usual.
   */
  restore?: boolean
}

const COUNT_PREFIX = 'reveal:'

function readCount(key: string): number | null {
  try {
    const raw = window.sessionStorage.getItem(COUNT_PREFIX + key)
    if (raw === null) return null
    const value = Number(raw)
    return Number.isInteger(value) && value > 0 ? value : null
  } catch {
    return null
  }
}

function writeCount(key: string, value: number): void {
  try {
    window.sessionStorage.setItem(COUNT_PREFIX + key, String(value))
  } catch {
    // Storage unavailable: fall back to the pre-existing one-batch behaviour.
  }
}

export function useIncrementalList<T>(
  items: readonly T[],
  batchSizeOrOptions: number | IncrementalListOptions = DEFAULT_BATCH_SIZE
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
  const options: IncrementalListOptions =
    typeof batchSizeOrOptions === 'number' ? { batchSize: batchSizeOrOptions } : batchSizeOrOptions
  const batchSize = options.batchSize ?? DEFAULT_BATCH_SIZE
  const { persistKey, restore } = options

  const [count, setCount] = useState(() => {
    if (restore && persistKey && typeof window !== 'undefined') {
      const saved = readCount(persistKey)
      if (saved !== null && saved > batchSize) return saved
    }
    return batchSize
  })

  // A new filter/sort/search result is a new array identity — start over so the
  // user is looking at the top of the new list, not deep into the old one.
  // Adjusted during render rather than in an effect: React re-runs this
  // component immediately without committing the stale count or painting the
  // intermediate state, so there is no cascading-render pass.
  // https://react.dev/reference/react/useState#storing-information-from-previous-renders
  //
  // One exception: when restoring, the very first transition from "no items
  // yet" (data still loading) to the real list must keep the remembered
  // count, otherwise the restored depth is thrown away before it is used.
  const [restoring, setRestoring] = useState(Boolean(restore && persistKey))
  const [prevItems, setPrevItems] = useState(items)
  if (prevItems !== items) {
    setPrevItems(items)
    const firstRealList = prevItems.length === 0 && items.length > 0
    if (!(restoring && firstRealList)) {
      setCount(batchSize)
    }
    if (restoring) setRestoring(false)
  }

  // Remember how deep the user has revealed, so Back can rebuild the same page
  // height before scroll restoration runs. Nothing is written while the list
  // is still empty (loading), which would clobber a remembered depth.
  useEffect(() => {
    if (!persistKey || items.length === 0) return
    writeCount(persistKey, Math.min(count, items.length))
  }, [persistKey, count, items.length])

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
