import { z } from 'zod'
import * as bcrypt from 'bcryptjs'
import { registerRequestSchema, formatZodError } from '../../lib/schemas'
import { createDb } from '../../../shared/db/client'
import { users, sessionTokens } from '../../../shared/db/schema'
import { eq, sql } from 'drizzle-orm'

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
    const { email, password, username } = registerRequestSchema.parse(body)

    // Check if email already exists
    const existingEmail = await db.query.users.findFirst({
      where: eq(users.email, email),
      columns: { id: true },
    })

    if (existingEmail) {
      return new Response(
        JSON.stringify({
          error: 'User already exists',
          details: 'An account with this email address already exists',
        }),
        {
          status: 409,
          headers: { 'Content-Type': 'application/json' },
        }
      )
    }

    // Check if username is already taken (case-insensitive)
    const existingUsername = await db.query.users.findFirst({
      where: sql`LOWER(${users.username}) = LOWER(${username})`,
      columns: { id: true },
    })

    if (existingUsername) {
      return new Response(
        JSON.stringify({
          error: 'Username taken',
          details: 'This username is already taken',
        }),
        {
          status: 409,
          headers: { 'Content-Type': 'application/json' },
        }
      )
    }

    // Hash password
    const passwordHash = await bcrypt.hash(password, 10)

    // Generate user ID
    const userId = crypto.randomUUID()
    const now = Date.now()

    // Create user
    await db.insert(users).values({
      id: userId,
      email,
      passwordHash,
      username,
      createdAt: now,
      lastLogin: now,
      updatedAt: now,
    })

    // Create session token
    const sessionTokenId = crypto.randomUUID()
    const expiresAt = now + SESSION_DURATION_MS

    await db.insert(sessionTokens).values({
      id: sessionTokenId,
      userId,
      expiresAt,
      createdAt: now,
    })

    return new Response(
      JSON.stringify({
        user: {
          id: userId,
          email,
          username,
          createdAt: now,
        },
        session_token: sessionTokenId,
        message: 'Registration successful',
      }),
      {
        status: 201,
        headers: { 'Content-Type': 'application/json' },
      }
    )
  } catch (error) {
    console.error('Registration error:', error)

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
