import { createDb } from '../../../shared/db/client'
import { sessionTokens, users } from '../../../shared/db/schema'
import { eq } from 'drizzle-orm'

interface Env {
  DB: D1Database
}

export async function onRequestGet(context: EventContext<Env, string, unknown>) {
  const { DB } = context.env
  const db = createDb(DB)

  try {
    // Get session token from Authorization header or query param
    const authHeader = context.request.headers.get('Authorization')
    const url = new URL(context.request.url)
    const sessionToken = authHeader?.replace('Bearer ', '') || url.searchParams.get('session_token')

    if (!sessionToken) {
      return new Response(
        JSON.stringify({
          error: 'Session token required',
        }),
        {
          status: 401,
          headers: { 'Content-Type': 'application/json' },
        }
      )
    }

    // Find session token and check if it's expired
    const session = await db.query.sessionTokens.findFirst({
      where: eq(sessionTokens.id, sessionToken),
    })

    if (!session) {
      return new Response(
        JSON.stringify({
          error: 'Invalid session token',
        }),
        {
          status: 401,
          headers: { 'Content-Type': 'application/json' },
        }
      )
    }

    // Check if expired
    if (session.expiresAt < Date.now()) {
      // Delete expired token
      await db.delete(sessionTokens).where(eq(sessionTokens.id, sessionToken))

      return new Response(
        JSON.stringify({
          error: 'Session expired',
        }),
        {
          status: 401,
          headers: { 'Content-Type': 'application/json' },
        }
      )
    }

    // Get user
    const user = await db.query.users.findFirst({
      where: eq(users.id, session.userId),
      columns: {
        id: true,
        email: true,
        username: true,
        createdAt: true,
        lastLogin: true,
        updatedAt: true,
      },
    })

    if (!user) {
      return new Response(
        JSON.stringify({
          error: 'User not found',
        }),
        {
          status: 404,
          headers: { 'Content-Type': 'application/json' },
        }
      )
    }

    return new Response(
      JSON.stringify({
        user: {
          id: user.id,
          email: user.email,
          username: user.username,
          createdAt: user.createdAt,
          lastLogin: user.lastLogin,
          updatedAt: user.updatedAt,
        },
      }),
      {
        status: 200,
        headers: { 'Content-Type': 'application/json' },
      }
    )
  } catch (error) {
    console.error('Me endpoint error:', error)

    return new Response(
      JSON.stringify({
        error: 'Internal server error',
      }),
      {
        status: 500,
        headers: { 'Content-Type': 'application/json' },
      }
    )
  }
}
