import { z } from 'zod'
import * as bcrypt from 'bcryptjs'
import { loginRequestSchema, formatZodError } from '../../lib/schemas'
import { createDb } from '../../../shared/db/client'
import { users, sessionTokens } from '../../../shared/db/schema'
import { eq } from 'drizzle-orm'

interface Env {
  DB: D1Database
}

const SESSION_DURATION_MS = 30 * 24 * 60 * 60 * 1000 // 30 days

export async function onRequestPost(context: EventContext<Env, string, unknown>) {
  const { DB } = context.env
  const db = createDb(DB)

  try {
    // Parse and validate request body
    const body = await context.request.json()
    const { email, password } = loginRequestSchema.parse(body)

    // Find user by email
    const user = await db.query.users.findFirst({
      where: eq(users.email, email),
    })

    if (!user) {
      return new Response(
        JSON.stringify({
          error: 'Invalid credentials',
          details: 'Email or password is incorrect',
        }),
        {
          status: 401,
          headers: { 'Content-Type': 'application/json' },
        }
      )
    }

    // Verify password
    const passwordMatch = await bcrypt.compare(password, user.passwordHash)

    if (!passwordMatch) {
      return new Response(
        JSON.stringify({
          error: 'Invalid credentials',
          details: 'Email or password is incorrect',
        }),
        {
          status: 401,
          headers: { 'Content-Type': 'application/json' },
        }
      )
    }

    // Create session token
    const sessionTokenId = crypto.randomUUID()
    const now = Date.now()
    const expiresAt = now + SESSION_DURATION_MS

    await db.insert(sessionTokens).values({
      id: sessionTokenId,
      userId: user.id,
      expiresAt,
      createdAt: now,
    })

    // Update last login
    await db.update(users)
      .set({ lastLogin: now, updatedAt: now })
      .where(eq(users.id, user.id))

    return new Response(
      JSON.stringify({
        user: {
          id: user.id,
          email: user.email,
          username: user.username,
          createdAt: user.createdAt,
          lastLogin: now,
        },
        session_token: sessionTokenId,
      }),
      {
        status: 200,
        headers: { 'Content-Type': 'application/json' },
      }
    )
  } catch (error) {
    console.error('Login error:', error)

    if (error instanceof z.ZodError) {
      return new Response(JSON.stringify(formatZodError(error)), {
        status: 400,
        headers: { 'Content-Type': 'application/json' },
      })
    }

    return new Response(
      JSON.stringify({
        error: 'Internal server error',
        details: 'An unexpected error occurred',
      }),
      {
        status: 500,
        headers: { 'Content-Type': 'application/json' },
      }
    )
  }
}
