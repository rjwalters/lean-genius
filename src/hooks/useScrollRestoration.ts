import { useEffect, useLayoutEffect, useRef } from 'react'

/** Upper bound on animation frames to wait for the page to grow tall enough. */
const MAX_FRAMES = 180

const STORAGE_PREFIX = 'scroll:'

function readOffset(key: string): number | null {
  try {
    const raw = window.sessionStorage.getItem(STORAGE_PREFIX + key)
    if (raw === null) return null
    const value = Number(raw)
    return Number.isFinite(value) ? value : null
  } catch {
    return null
  }
}

function writeOffset(key: string, value: number): void {
  try {
    window.sessionStorage.setItem(STORAGE_PREFIX + key, String(Math.round(value)))
  } catch {
    // Storage can be unavailable (private mode, quota); losing the offset is
    // the pre-existing behaviour, not an error.
  }
}

/**
 * Deliberate scroll restoration for pages whose content arrives late.
 *
 * The browser restores `scrollY` on Back at the moment the history entry is
 * activated. On the gallery routes that moment shows a `LoadingScreen`: the
 * listings are still being fetched and `useIncrementalList` has mounted only
 * its first batch, so the saved offset does not exist yet and the browser
 * either clamps to the top or, as the batches reveal, lands at the bottom
 * (#43696). This hook takes over instead:
 *
 * - while mounted, `history.scrollRestoration` is set to `manual` (and put
 *   back on unmount), so the browser stops competing;
 * - the current offset is saved per route key as the user scrolls and again
 *   on unmount (never while a restore is still pending);
 * - once `ready` is true (data loaded, restored batch count mounted) and the
 *   navigation was a Back/Forward (`restore`), the page waits until the
 *   document is tall enough to contain the saved offset and scrolls there;
 * - a fresh visit (`restore` false) starts at the top.
 *
 * Pair it with `useIncrementalList`'s `persistKey`/`restore` options using the
 * same key so the reveal count is restored first and the target offset is
 * reachable without triggering the sentinel cascade.
 *
 * @param key Route identity (pathname + search) the offset is stored under.
 * @param ready True once the content the offset refers to is mounted.
 * @param restore True for POP navigations (Back/Forward); false to start at top.
 */
export function useScrollRestoration(key: string, ready: boolean, restore: boolean): void {
  // Take over from the browser for the lifetime of this page.
  useEffect(() => {
    if (typeof window === 'undefined' || !('scrollRestoration' in window.history)) return
    const previous = window.history.scrollRestoration
    window.history.scrollRestoration = 'manual'
    return () => {
      window.history.scrollRestoration = previous
    }
  }, [])

  // The offset to restore, captured synchronously at mount before any scroll
  // event on this page can overwrite it: the browser fires `scroll` when the
  // loading screen replaces the tall gallery and clamps `scrollY` to 0, and a
  // naive listener would save that 0 as the "current" position. While a
  // restore is pending, nothing is written.
  const pendingRef = useRef<number | null>(null)
  const doneRef = useRef(false)

  // Remember where the user is: throttled to one write per frame while
  // scrolling, plus a final write when the page unmounts. This must be a
  // layout effect: its cleanup runs while the gallery DOM is still attached,
  // whereas a passive cleanup runs after React has swapped in the next route,
  // by which time the browser has clamped `scrollY` to the shorter page (0).
  useLayoutEffect(() => {
    if (typeof window === 'undefined') return
    if (restore && !doneRef.current) pendingRef.current = readOffset(key)
    let frame = 0
    const save = () => {
      frame = 0
      if (pendingRef.current === null) writeOffset(key, window.scrollY)
    }
    const onScroll = () => {
      if (!frame) frame = window.requestAnimationFrame(save)
    }
    window.addEventListener('scroll', onScroll, { passive: true })
    return () => {
      if (frame) window.cancelAnimationFrame(frame)
      window.removeEventListener('scroll', onScroll)
      if (pendingRef.current === null) writeOffset(key, window.scrollY)
    }
  }, [key, restore])

  // Restore once, when the content is there.
  useEffect(() => {
    if (doneRef.current || !ready || typeof window === 'undefined') return
    doneRef.current = true

    if (!restore) {
      pendingRef.current = null
      window.scrollTo(0, 0)
      return
    }

    const target = pendingRef.current
    if (target === null || target <= 0) {
      pendingRef.current = null
      return
    }

    let frames = 0
    let cancelled = false
    const attempt = () => {
      if (cancelled) return
      const maxOffset = document.documentElement.scrollHeight - window.innerHeight
      if (maxOffset >= target || frames >= MAX_FRAMES) {
        window.scrollTo(0, target)
        pendingRef.current = null
        return
      }
      frames++
      window.requestAnimationFrame(attempt)
    }
    attempt()
    return () => {
      cancelled = true
    }
  }, [ready, restore, key])
}
