import { validateSession } from '../../../lib/auth'
import { createDb } from '../../../../shared/db/client'
import { comments } from '../../../../shared/db/schema'
import { eq, and, isNull, desc } from 'drizzle-orm'

interface Env {
  DB: D1Database
}

// GET /api/users/me/comments - Get current user's comments
export async function onRequestGet(context: EventContext<Env, string, unknown>) {
  const { DB } = context.env
  const db = createDb(DB)

  try {
    const session = await validateSession(context.request, DB)
    if (!session.valid) {
      return new Response(
        JSON.stringify({ error: session.error }),
        { status: 401, headers: { 'Content-Type': 'application/json' } }
      )
    }

    // Fetch user's non-deleted comments, most recent first
    const result = await db
      .select({
        id: comments.id,
        proofId: comments.proofId,
        lineNumber: comments.lineNumber,
        parentId: comments.parentId,
        content: comments.content,
        createdAt: comments.createdAt,
        updatedAt: comments.updatedAt,
      })
      .from(comments)
      .where(and(
        eq(comments.userId, session.userId),
        isNull(comments.deletedAt)
      ))
      .orderBy(desc(comments.createdAt))

    return new Response(
      JSON.stringify({
        comments: result,
        totalCount: result.length,
      }),
      { status: 200, headers: { 'Content-Type': 'application/json' } }
    )
  } catch (error) {
    console.error('Get user comments error:', error)
    return new Response(
      JSON.stringify({ error: 'Internal server error' }),
      { status: 500, headers: { 'Content-Type': 'application/json' } }
    )
  }
}
