import { useEffect, useState } from 'react'

/**
 * Load async data on mount and expose { data, error } (issue #35117).
 *
 * Built for the runtime listings loaders (`getListings`,
 * `getResearchListings`), which cache their promise module-level — so
 * remounting a page that uses this hook does not refetch.
 *
 * `load` must be referentially stable (e.g. a module-level function); passing
 * an inline closure would refire the effect every render.
 */
export function useFetchedData<T>(load: () => Promise<T>): {
  data: T | null
  error: boolean
} {
  const [data, setData] = useState<T | null>(null)
  const [error, setError] = useState(false)

  useEffect(() => {
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
  }, [load])

  return { data, error }
}
