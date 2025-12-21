import { z } from 'zod'
import { updateCommentSchema, formatZodError } from '../../lib/schemas'
import { validateSession } from '../../lib/auth'
import { createDb } from '../../../shared/db/client'
import { comments, users } from '../../../shared/db/schema'
import { eq } from 'drizzle-orm'

interface Env {
  DB: D1Database
}

// GET /api/comments/:id - Get a single comment
export async function onRequestGet(context: EventContext<Env, string, { id: string }>) {
  const { DB } = context.env
  const db = createDb(DB)
  const commentId = context.params.id

  try {
    const result = await db
      .select({
        id: comments.id,
        proofId: comments.proofId,
        lineNumber: comments.lineNumber,
        parentId: comments.parentId,
        content: comments.content,
        createdAt: comments.createdAt,
        updatedAt: comments.updatedAt,
        deletedAt: comments.deletedAt,
        authorId: users.id,
        authorUsername: users.username,
      })
      .from(comments)
      .innerJoin(users, eq(comments.userId, users.id))
      .where(eq(comments.id, commentId))
      .limit(1)

    if (result.length === 0) {
      return new Response(
        JSON.stringify({ error: 'Comment not found' }),
        { status: 404, headers: { 'Content-Type': 'application/json' } }
      )
    }

    const row = result[0]

    return new Response(
      JSON.stringify({
        comment: {
          id: row.id,
          proofId: row.proofId,
          lineNumber: row.lineNumber,
          parentId: row.parentId,
          content: row.deletedAt ? '[deleted]' : row.content,
          createdAt: row.createdAt,
          updatedAt: row.updatedAt,
          deleted: !!row.deletedAt,
          author: {
            id: row.authorId,
            username: row.deletedAt ? '[deleted]' : row.authorUsername,
          },
        },
      }),
      { status: 200, headers: { 'Content-Type': 'application/json' } }
    )
  } catch (error) {
    console.error('Get comment error:', error)
    return new Response(
      JSON.stringify({ error: 'Internal server error' }),
      { status: 500, headers: { 'Content-Type': 'application/json' } }
    )
  }
}

// PUT /api/comments/:id - Update a comment
export async function onRequestPut(context: EventContext<Env, string, { id: string }>) {
  const { DB } = context.env
  const db = createDb(DB)
  const commentId = context.params.id

  try {
    // Validate session
    const session = await validateSession(context.request, DB)
    if (!session.valid) {
      return new Response(
        JSON.stringify({ error: session.error }),
        { status: 401, headers: { 'Content-Type': 'application/json' } }
      )
    }

    // Get existing comment
    const existing = await db.query.comments.findFirst({
      where: eq(comments.id, commentId),
    })

    if (!existing) {
      return new Response(
        JSON.stringify({ error: 'Comment not found' }),
        { status: 404, headers: { 'Content-Type': 'application/json' } }
      )
    }

    // Check ownership
    if (existing.userId !== session.userId) {
      return new Response(
        JSON.stringify({ error: 'Not authorized to edit this comment' }),
        { status: 403, headers: { 'Content-Type': 'application/json' } }
      )
    }

    // Check if deleted
    if (existing.deletedAt) {
      return new Response(
        JSON.stringify({ error: 'Cannot edit a deleted comment' }),
        { status: 400, headers: { 'Content-Type': 'application/json' } }
      )
    }

    // Parse and validate request body
    const body = await context.request.json()
    const { content } = updateCommentSchema.parse(body)

    const now = Date.now()

    // Update comment
    await db.update(comments)
      .set({ content, updatedAt: now })
      .where(eq(comments.id, commentId))

    return new Response(
      JSON.stringify({
        comment: {
          id: commentId,
          proofId: existing.proofId,
          lineNumber: existing.lineNumber,
          parentId: existing.parentId,
          content,
          createdAt: existing.createdAt,
          updatedAt: now,
          author: {
            id: session.user.id,
            username: session.user.username,
          },
        },
      }),
      { status: 200, headers: { 'Content-Type': 'application/json' } }
    )
  } catch (error) {
    console.error('Update comment error:', error)

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

// DELETE /api/comments/:id - Soft delete a comment
export async function onRequestDelete(context: EventContext<Env, string, { id: string }>) {
  const { DB } = context.env
  const db = createDb(DB)
  const commentId = context.params.id

  try {
    // Validate session
    const session = await validateSession(context.request, DB)
    if (!session.valid) {
      return new Response(
        JSON.stringify({ error: session.error }),
        { status: 401, headers: { 'Content-Type': 'application/json' } }
      )
    }

    // Get existing comment
    const existing = await db.query.comments.findFirst({
      where: eq(comments.id, commentId),
    })

    if (!existing) {
      return new Response(
        JSON.stringify({ error: 'Comment not found' }),
        { status: 404, headers: { 'Content-Type': 'application/json' } }
      )
    }

    // Check ownership
    if (existing.userId !== session.userId) {
      return new Response(
        JSON.stringify({ error: 'Not authorized to delete this comment' }),
        { status: 403, headers: { 'Content-Type': 'application/json' } }
      )
    }

    // Soft delete
    const now = Date.now()
    await db.update(comments)
      .set({ deletedAt: now, updatedAt: now })
      .where(eq(comments.id, commentId))

    return new Response(
      JSON.stringify({ success: true }),
      { status: 200, headers: { 'Content-Type': 'application/json' } }
    )
  } catch (error) {
    console.error('Delete comment error:', error)
    return new Response(
      JSON.stringify({ error: 'Internal server error' }),
      { status: 500, headers: { 'Content-Type': 'application/json' } }
    )
  }
}
