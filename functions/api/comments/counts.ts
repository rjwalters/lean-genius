import { createDb } from '../../../shared/db/client'
import { comments } from '../../../shared/db/schema'
import { sql } from 'drizzle-orm'

interface Env {
  DB: D1Database
}

// GET /api/comments/counts?proof_id=X - Get comment counts per line and annotation
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

    // Get comment counts grouped by line number (for legacy line-based comments)
    const lineResult = await db
      .select({
        lineNumber: comments.lineNumber,
        count: sql<number>`count(*)`.as('count'),
      })
      .from(comments)
      .where(
        sql`${comments.proofId} = ${proofId} AND ${comments.deletedAt} IS NULL AND ${comments.lineNumber} IS NOT NULL`
      )
      .groupBy(comments.lineNumber)

    // Get comment counts grouped by annotation ID (for annotation-anchored comments)
    const annotationResult = await db
      .select({
        annotationId: comments.annotationId,
        count: sql<number>`count(*)`.as('count'),
      })
      .from(comments)
      .where(
        sql`${comments.proofId} = ${proofId} AND ${comments.deletedAt} IS NULL AND ${comments.annotationId} IS NOT NULL`
      )
      .groupBy(comments.annotationId)

    // Convert to maps for easier client-side use
    const lineCounts: Record<number, number> = {}
    for (const row of lineResult) {
      if (row.lineNumber !== null) {
        lineCounts[row.lineNumber] = row.count
      }
    }

    const annotationCounts: Record<string, number> = {}
    for (const row of annotationResult) {
      if (row.annotationId !== null) {
        annotationCounts[row.annotationId] = row.count
      }
    }

    return new Response(
      JSON.stringify({
        counts: lineCounts,           // Legacy: { lineNumber: count }
        annotationCounts,             // New: { annotationId: count }
      }),
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
