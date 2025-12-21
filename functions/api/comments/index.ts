import { createDb } from '../../../shared/db/client'
import { comments, users, commentVotes } from '../../../shared/db/schema'
import { eq, and, isNull, sql } from 'drizzle-orm'
import { validateSession } from '../../lib/auth'

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

    // Check for optional authentication to get user's votes
    const session = await validateSession(context.request, DB)
    const currentUserId = session.valid ? session.userId : null

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

    // Get vote scores for all comments
    const commentIds = result.map(r => r.id)

    // Aggregate vote scores
    const voteScores = commentIds.length > 0
      ? await db
          .select({
            commentId: commentVotes.commentId,
            score: sql<number>`COALESCE(SUM(${commentVotes.value}), 0)`.as('score'),
          })
          .from(commentVotes)
          .where(sql`${commentVotes.commentId} IN (${sql.join(commentIds.map(id => sql`${id}`), sql`, `)})`)
          .groupBy(commentVotes.commentId)
      : []

    // Get current user's votes if authenticated
    const userVotes = currentUserId && commentIds.length > 0
      ? await db
          .select({
            commentId: commentVotes.commentId,
            value: commentVotes.value,
          })
          .from(commentVotes)
          .where(
            and(
              sql`${commentVotes.commentId} IN (${sql.join(commentIds.map(id => sql`${id}`), sql`, `)})`,
              eq(commentVotes.userId, currentUserId)
            )
          )
      : []

    // Create lookup maps
    const scoreMap = new Map(voteScores.map(v => [v.commentId, Number(v.score)]))
    const userVoteMap = new Map(userVotes.map(v => [v.commentId, v.value as 1 | -1]))

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
      score: scoreMap.get(row.id) ?? 0,
      userVote: userVoteMap.get(row.id) ?? null,
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
