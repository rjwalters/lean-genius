import { useEffect, useRef, useState } from 'react'

/**
 * Lazily load async data the first time `enabled` becomes true (issue #35117).
 *
 * Unlike `useFetchedData`, which fetches on mount, this hook defers the fetch
 * until `enabled` flips to true — then keeps the result cached for the rest of
 * the session (the underlying `load` also caches its promise module-level, so
 * repeated calls are free). Built for the search-index loaders
 * (`getSearchIndex`, `getResearchSearchIndex`), which should only be fetched
 * once the user actually searches, so the eager first paint never pays for the
 * index download.
 *
 * `load` must be referentially stable (e.g. a module-level function); passing
 * an inline closure would refire the effect on every render.
 */
export function useLazyFetchedData<T>(
  load: () => Promise<T>,
  enabled: boolean
): {
  data: T | null
  error: boolean
} {
  const [data, setData] = useState<T | null>(null)
  const [error, setError] = useState(false)
  // Guards against re-firing the fetch on subsequent renders. A ref (not state)
  // so flipping it doesn't itself trigger a render / setState-in-effect.
  const startedRef = useRef(false)

  useEffect(() => {
    if (!enabled || startedRef.current) return
    startedRef.current = true
    let cancelled = false
    load()
      .then((d) => {
        if (!cancelled) setData(d)
      })
      .catch(() => {
        if (!cancelled) setError(true)
      })
    return () => {
      cancelled = true
    }
  }, [enabled, load])

  return { data, error }
}
