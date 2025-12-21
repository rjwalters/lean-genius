import { createDb } from '../../../shared/db/client'
import { comments } from '../../../shared/db/schema'
import { eq, isNull, sql } from 'drizzle-orm'

interface Env {
  DB: D1Database
}

// GET /api/comments/counts?proof_id=X - Get comment counts per line
export async function onRequestGet(context: EventContext<Env, string, unknown>) {
  const { DB } = context.env
  const db = createDb(DB)

  try {
    const url = new URL(context.request.url)
    const proofId = url.searchParams.get('proof_id')

    if (!proofId) {
      return new Response(
        JSON.stringify({ error: 'proof_id is required' }),
        { status: 400, headers: { 'Content-Type': 'application/json' } }
      )
    }

    // Get comment counts grouped by line number
    const result = await db
      .select({
        lineNumber: comments.lineNumber,
        count: sql<number>`count(*)`.as('count'),
      })
      .from(comments)
      .where(
        sql`${comments.proofId} = ${proofId} AND ${comments.deletedAt} IS NULL`
      )
      .groupBy(comments.lineNumber)

    // Convert to a map for easier client-side use
    const counts: Record<number, number> = {}
    for (const row of result) {
      counts[row.lineNumber] = row.count
    }

    return new Response(
      JSON.stringify({ counts }),
      { status: 200, headers: { 'Content-Type': 'application/json' } }
    )
  } catch (error) {
    console.error('Get comment counts error:', error)
    return new Response(
      JSON.stringify({ error: 'Internal server error' }),
      { status: 500, headers: { 'Content-Type': 'application/json' } }
    )
  }
}
