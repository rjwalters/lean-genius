import { lazy } from 'react'

/**
 * Wraps React.lazy with retry logic for chunk loading failures.
 * When a deployment changes asset hashes, cached HTML may reference
 * stale chunk URLs. This detects the failure and reloads the page once
 * to pick up the new HTML with correct chunk references.
 */
export function lazyWithRetry<T extends React.ComponentType<unknown>>(
  factory: () => Promise<{ default: T }>
) {
  return lazy(() =>
    factory().catch((error: unknown) => {
      const isChunkError =
        error instanceof Error &&
        (error.message.includes('dynamically imported module') ||
         error.message.includes('Failed to fetch') ||
         error.message.includes('Loading chunk') ||
         error.message.includes('Loading CSS chunk'))

      if (isChunkError) {
        const key = 'chunk-reload-ts'
        const lastReload = sessionStorage.getItem(key)
        const now = Date.now()

        // Only auto-reload once per 30 seconds to avoid infinite loops
        if (!lastReload || now - Number(lastReload) > 30_000) {
          sessionStorage.setItem(key, String(now))
          window.location.reload()
        }
      }

      throw error
    })
  )
}
