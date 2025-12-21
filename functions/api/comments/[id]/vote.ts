import { z } from 'zod'
import { voteCommentSchema, formatZodError } from '../../../lib/schemas'
import { validateSession } from '../../../lib/auth'
import { createDb } from '../../../../shared/db/client'
import { comments, commentVotes } from '../../../../shared/db/schema'
import { eq, and, sum, isNull } from 'drizzle-orm'

interface Env {
  DB: D1Database
}

export async function onRequestPost(context: EventContext<Env, string, unknown>) {
  const { DB } = context.env
  const db = createDb(DB)

  try {
    // Validate session
    const session = await validateSession(context.request, DB)
    if (!session.valid) {
      return new Response(
        JSON.stringify({ error: session.error }),
        { status: 401, headers: { 'Content-Type': 'application/json' } }
      )
    }

    // Get comment ID from URL
    const url = new URL(context.request.url)
    const pathParts = url.pathname.split('/')
    const commentId = pathParts[pathParts.length - 2] // /api/comments/:id/vote

    // Verify comment exists and is not deleted
    const comment = await db.query.comments.findFirst({
      where: and(eq(comments.id, commentId), isNull(comments.deletedAt)),
      columns: { id: true },
    })

    if (!comment) {
      return new Response(
        JSON.stringify({ error: 'Comment not found' }),
        { status: 404, headers: { 'Content-Type': 'application/json' } }
      )
    }

    // Parse and validate request body
    const body = await context.request.json()
    const { value } = voteCommentSchema.parse(body)

    const now = Date.now()

    if (value === 0) {
      // Remove vote
      await db
        .delete(commentVotes)
        .where(
          and(
            eq(commentVotes.commentId, commentId),
            eq(commentVotes.userId, session.userId)
          )
        )
    } else {
      // Upsert vote using INSERT OR REPLACE
      await db
        .insert(commentVotes)
        .values({
          commentId,
          userId: session.userId,
          value,
          createdAt: now,
        })
        .onConflictDoUpdate({
          target: [commentVotes.commentId, commentVotes.userId],
          set: { value, createdAt: now },
        })
    }

    // Calculate new score
    const scoreResult = await db
      .select({ total: sum(commentVotes.value) })
      .from(commentVotes)
      .where(eq(commentVotes.commentId, commentId))

    const score = Number(scoreResult[0]?.total) || 0

    return new Response(
      JSON.stringify({
        score,
        userVote: value === 0 ? null : value,
      }),
      { status: 200, headers: { 'Content-Type': 'application/json' } }
    )
  } catch (error) {
    console.error('Vote comment error:', error)

    if (error instanceof z.ZodError) {
      return new Response(JSON.stringify(formatZodError(error)), {
        status: 400,
        headers: { 'Content-Type': 'application/json' },
      })
    }

    return new Response(
      JSON.stringify({ error: 'Internal server error' }),
      { status: 500, headers: { 'Content-Type': 'application/json' } }
    )
  }
}
