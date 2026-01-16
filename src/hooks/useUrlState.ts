import { useSearchParams } from 'react-router-dom'
import { useCallback, useMemo, useRef, useEffect, useState } from 'react'

/**
 * Serializer interface for converting values to/from URL strings
 */
type Serializer<T> = {
  parse: (value: string | null) => T
  stringify: (value: T) => string | null // null = remove from URL
}

/**
 * Common serializers for URL state
 */
export const serializers = {
  /**
   * String serializer - empty string removes from URL
   */
  string: {
    parse: (v: string | null): string => v || '',
    stringify: (v: string): string | null => v || null,
  } as Serializer<string>,

  /**
   * String array serializer - comma-separated values
   * Empty array removes from URL
   */
  stringArray: {
    parse: (v: string | null): string[] => v?.split(',').filter(Boolean) ?? [],
    stringify: (v: string[]): string | null => v.length ? v.join(',') : null,
  } as Serializer<string[]>,

  /**
   * Boolean serializer - '1' for true, removed for false
   */
  boolean: {
    parse: (v: string | null): boolean => v === '1',
    stringify: (v: boolean): string | null => v ? '1' : null,
  } as Serializer<boolean>,

  /**
   * Enum serializer factory - validates against allowed values
   */
  enum: <T extends string>(defaultValue: T, allowedValues: T[]): Serializer<T> => ({
    parse: (v: string | null): T =>
      v && allowedValues.includes(v as T) ? v as T : defaultValue,
    stringify: (v: T): string | null => v === defaultValue ? null : v,
  }),
}

/**
 * Hook for syncing React state with URL search params
 *
 * @param key - The URL param key
 * @param defaultValue - Default value when param is not in URL
 * @param serializer - Serializer for converting to/from URL string
 * @returns [value, setValue] tuple similar to useState
 *
 * @example
 * // String state
 * const [query, setQuery] = useUrlState('q', '', serializers.string)
 *
 * @example
 * // Array state
 * const [badges, setBadges] = useUrlState('badges', [], serializers.stringArray)
 *
 * @example
 * // Boolean state
 * const [showOnly, setShowOnly] = useUrlState('erdos', false, serializers.boolean)
 *
 * @example
 * // Enum state
 * const [sort, setSort] = useUrlState('sort', 'newest', serializers.enum('newest', ['newest', 'oldest', 'alphabetical']))
 */
export function useUrlState<T>(
  key: string,
  _defaultValue: T, // Unused - serializers handle defaults internally
  serializer: Serializer<T>
): [T, (value: T | ((prev: T) => T)) => void] {
  const [searchParams, setSearchParams] = useSearchParams()

  // Parse value from URL
  const value = useMemo(() => {
    const urlValue = searchParams.get(key)
    return serializer.parse(urlValue)
  }, [searchParams, key, serializer])

  // Ref to track if we're updating to prevent loops
  const isUpdating = useRef(false)

  // Update URL when value changes
  const setValue = useCallback((newValueOrUpdater: T | ((prev: T) => T)) => {
    if (isUpdating.current) return
    isUpdating.current = true

    setSearchParams((prev) => {
      const currentValue = serializer.parse(prev.get(key))
      const newValue = typeof newValueOrUpdater === 'function'
        ? (newValueOrUpdater as (prev: T) => T)(currentValue)
        : newValueOrUpdater

      const stringValue = serializer.stringify(newValue)
      const newParams = new URLSearchParams(prev)

      if (stringValue === null) {
        newParams.delete(key)
      } else {
        newParams.set(key, stringValue)
      }

      return newParams
    }, { replace: true }) // Use replace to avoid polluting history

    // Reset flag after update
    requestAnimationFrame(() => {
      isUpdating.current = false
    })
  }, [key, serializer, setSearchParams])

  return [value, setValue]
}

/**
 * Hook for debounced URL state updates
 * Useful for search inputs to avoid updating URL on every keystroke
 *
 * @param key - The URL param key
 * @param defaultValue - Default value when param is not in URL
 * @param serializer - Serializer for converting to/from URL string
 * @param delay - Debounce delay in ms (default: 300)
 * @returns [value, setValue, debouncedValue] tuple
 */
export function useDebouncedUrlState<T>(
  key: string,
  defaultValue: T,
  serializer: Serializer<T>,
  delay: number = 300
): [T, (value: T | ((prev: T) => T)) => void, T] {
  const [urlValue, setUrlValue] = useUrlState(key, defaultValue, serializer)
  const [localValue, setLocalValue] = useState<T>(urlValue)
  const timeoutRef = useRef<ReturnType<typeof setTimeout> | undefined>(undefined)

  // Sync local value when URL changes externally (e.g., back button)
  useEffect(() => {
    setLocalValue(urlValue)
  }, [urlValue])

  // Debounced setter
  const setValue = useCallback((newValueOrUpdater: T | ((prev: T) => T)) => {
    const newValue = typeof newValueOrUpdater === 'function'
      ? (newValueOrUpdater as (prev: T) => T)(localValue)
      : newValueOrUpdater

    setLocalValue(newValue)

    if (timeoutRef.current) {
      clearTimeout(timeoutRef.current)
    }

    timeoutRef.current = setTimeout(() => {
      setUrlValue(newValue)
    }, delay)
  }, [localValue, setUrlValue, delay])

  // Cleanup timeout on unmount
  useEffect(() => {
    return () => {
      if (timeoutRef.current) {
        clearTimeout(timeoutRef.current)
      }
    }
  }, [])

  return [localValue, setValue, urlValue]
}

