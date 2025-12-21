import { createDb } from '../../../shared/db/client'
import { comments, users } from '../../../shared/db/schema'
import { eq, and, isNull } from 'drizzle-orm'

interface Env {
  DB: D1Database
}

export async function onRequestGet(context: EventContext<Env, string, unknown>) {
  const { DB } = context.env
  const db = createDb(DB)

  try {
    const url = new URL(context.request.url)
    const proofId = url.searchParams.get('proof_id')
    const lineNumberStr = url.searchParams.get('line')

    if (!proofId) {
      return new Response(
        JSON.stringify({ error: 'proof_id is required' }),
        { status: 400, headers: { 'Content-Type': 'application/json' } }
      )
    }

    // Build query conditions
    const conditions = [
      eq(comments.proofId, proofId),
      isNull(comments.deletedAt),
    ]

    // If line number specified, filter to that line
    if (lineNumberStr) {
      const lineNumber = parseInt(lineNumberStr, 10)
      if (isNaN(lineNumber)) {
        return new Response(
          JSON.stringify({ error: 'Invalid line number' }),
          { status: 400, headers: { 'Content-Type': 'application/json' } }
        )
      }
      conditions.push(eq(comments.lineNumber, lineNumber))
    }

    // Fetch comments with user info
    const result = await db
      .select({
        id: comments.id,
        proofId: comments.proofId,
        lineNumber: comments.lineNumber,
        parentId: comments.parentId,
        content: comments.content,
        createdAt: comments.createdAt,
        updatedAt: comments.updatedAt,
        authorId: users.id,
        authorUsername: users.username,
      })
      .from(comments)
      .innerJoin(users, eq(comments.userId, users.id))
      .where(and(...conditions))
      .orderBy(comments.createdAt)

    // Transform to response format
    const commentsData = result.map(row => ({
      id: row.id,
      proofId: row.proofId,
      lineNumber: row.lineNumber,
      parentId: row.parentId,
      content: row.content,
      createdAt: row.createdAt,
      updatedAt: row.updatedAt,
      author: {
        id: row.authorId,
        username: row.authorUsername,
      },
    }))

    return new Response(
      JSON.stringify({ comments: commentsData }),
      { status: 200, headers: { 'Content-Type': 'application/json' } }
    )
  } catch (error) {
    console.error('Get comments error:', error)
    return new Response(
      JSON.stringify({ error: 'Internal server error' }),
      { status: 500, headers: { 'Content-Type': 'application/json' } }
    )
  }
}
