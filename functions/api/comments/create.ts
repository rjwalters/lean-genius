import { z } from 'zod'
import { createCommentSchema, formatZodError } from '../../lib/schemas'
import { validateSession } from '../../lib/auth'
import { createDb } from '../../../shared/db/client'
import { comments, commentVotes } from '../../../shared/db/schema'
import { eq } from 'drizzle-orm'

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

    // Parse and validate request body
    const body = await context.request.json()
    const { proofId, lineNumber, parentId, content } = createCommentSchema.parse(body)

    // If parentId provided, verify it exists
    if (parentId) {
      const parent = await db.query.comments.findFirst({
        where: eq(comments.id, parentId),
        columns: { id: true, proofId: true, lineNumber: true },
      })

      if (!parent) {
        return new Response(
          JSON.stringify({ error: 'Parent comment not found' }),
          { status: 404, headers: { 'Content-Type': 'application/json' } }
        )
      }

      // Replies must be on the same proof/line as parent
      if (parent.proofId !== proofId || parent.lineNumber !== lineNumber) {
        return new Response(
          JSON.stringify({ error: 'Reply must be on the same proof line as parent' }),
          { status: 400, headers: { 'Content-Type': 'application/json' } }
        )
      }
    }

    // Create comment
    const commentId = crypto.randomUUID()
    const now = Date.now()

    await db.insert(comments).values({
      id: commentId,
      proofId,
      lineNumber,
      parentId: parentId || null,
      userId: session.userId,
      content,
      createdAt: now,
      updatedAt: now,
    })

    // Auto-upvote: the author automatically upvotes their own comment (Reddit-style)
    await db.insert(commentVotes).values({
      commentId,
      userId: session.userId,
      value: 1,
      createdAt: now,
    })

    return new Response(
      JSON.stringify({
        comment: {
          id: commentId,
          proofId,
          lineNumber,
          parentId: parentId || null,
          content,
          createdAt: now,
          updatedAt: now,
          author: {
            id: session.user.id,
            username: session.user.username,
          },
          score: 1,
          userVote: 1,
        },
      }),
      { status: 201, headers: { 'Content-Type': 'application/json' } }
    )
  } catch (error) {
    console.error('Create comment error:', error)

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
