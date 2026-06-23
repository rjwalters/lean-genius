import { drizzle } from 'drizzle-orm/d1'
import * as schema from './schema'

/**
 * Create a Drizzle database client from a D1 database instance.
 * Use this in Cloudflare Workers/Pages Functions.
 */
export function createDb(d1: D1Database) {
  return drizzle(d1, { schema })
}

export type Database = ReturnType<typeof createDb>
