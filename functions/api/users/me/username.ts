import { z } from 'zod'
import { validateSession } from '../../../lib/auth'
import { usernameSchema, formatZodError } from '../../../lib/schemas'
import { createDb } from '../../../../shared/db/client'
import { users } from '../../../../shared/db/schema'
import { eq, and, ne, sql } from 'drizzle-orm'

interface Env {
  DB: D1Database
}

// 30-day cooldown for username changes
const USERNAME_COOLDOWN_MS = 30 * 24 * 60 * 60 * 1000

// GET /api/users/me/username - Get username status
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

    const user = await db.query.users.findFirst({
      where: eq(users.id, session.userId),
      columns: {
        username: true,
        usernameChangedAt: true,
        email: true,
      },
    })

    if (!user) {
      return new Response(
        JSON.stringify({ error: 'User not found' }),
        { status: 404, headers: { 'Content-Type': 'application/json' } }
      )
    }

    const now = Date.now()
    const canChange = !user.usernameChangedAt || now - user.usernameChangedAt >= USERNAME_COOLDOWN_MS
    const nextChangeAt = user.usernameChangedAt ? user.usernameChangedAt + USERNAME_COOLDOWN_MS : null

    return new Response(
      JSON.stringify({
        username: user.username,
        displayName: user.username || user.email.split('@')[0],
        canChange,
        nextChangeAt: canChange ? null : nextChangeAt,
      }),
      { status: 200, headers: { 'Content-Type': 'application/json' } }
    )
  } catch (error) {
    console.error('Get username error:', error)
    return new Response(
      JSON.stringify({ error: 'Internal server error' }),
      { status: 500, headers: { 'Content-Type': 'application/json' } }
    )
  }
}

// PUT /api/users/me/username - Update username
export async function onRequestPut(context: EventContext<Env, string, unknown>) {
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

    // Parse and validate request body
    const body = await context.request.json()
    const updateSchema = z.object({ username: usernameSchema })
    const { username } = updateSchema.parse(body)

    // Get current user
    const user = await db.query.users.findFirst({
      where: eq(users.id, session.userId),
      columns: {
        username: true,
        usernameChangedAt: true,
      },
    })

    if (!user) {
      return new Response(
        JSON.stringify({ error: 'User not found' }),
        { status: 404, headers: { 'Content-Type': 'application/json' } }
      )
    }

    // Check cooldown (skip if same username or first change)
    const now = Date.now()
    if (user.usernameChangedAt && user.username?.toLowerCase() !== username.toLowerCase()) {
      const timeSinceChange = now - user.usernameChangedAt
      if (timeSinceChange < USERNAME_COOLDOWN_MS) {
        const daysRemaining = Math.ceil((USERNAME_COOLDOWN_MS - timeSinceChange) / (24 * 60 * 60 * 1000))
        return new Response(
          JSON.stringify({
            error: `You can change your username again in ${daysRemaining} day(s)`,
            nextChangeAt: user.usernameChangedAt + USERNAME_COOLDOWN_MS,
          }),
          { status: 429, headers: { 'Content-Type': 'application/json' } }
        )
      }
    }

    // Check uniqueness (case-insensitive, excluding current user)
    const existing = await db.query.users.findFirst({
      where: and(
        sql`LOWER(${users.username}) = LOWER(${username})`,
        ne(users.id, session.userId)
      ),
      columns: { id: true },
    })

    if (existing) {
      return new Response(
        JSON.stringify({ error: 'This username is already taken' }),
        { status: 409, headers: { 'Content-Type': 'application/json' } }
      )
    }

    // Update username
    await db.update(users)
      .set({
        username,
        usernameChangedAt: now,
        updatedAt: now,
      })
      .where(eq(users.id, session.userId))

    return new Response(
      JSON.stringify({
        success: true,
        username,
        nextChangeAt: now + USERNAME_COOLDOWN_MS,
      }),
      { status: 200, headers: { 'Content-Type': 'application/json' } }
    )
  } catch (error) {
    console.error('Update username error:', error)

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
