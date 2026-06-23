import { createDb } from '../../shared/db/client'
import { sessionTokens, users } from '../../shared/db/schema'
import { eq } from 'drizzle-orm'

export type SessionResult = {
  valid: true
  userId: string
  sessionId: string
  user: {
    id: string
    email: string
    username: string
  }
} | {
  valid: false
  error: string
}

export function extractBearerToken(request: Request): string | null {
  const authHeader = request.headers.get('Authorization')
  const match = authHeader?.match(/^Bearer\s+(\S+)\s*$/i)
  return match?.[1] ?? null
}

/**
 * Validate a session token and return user info if valid.
 * Extracts Bearer token from Authorization header.
 */
export async function validateSession(
  request: Request,
  DB: D1Database
): Promise<SessionResult> {
  const sessionToken = extractBearerToken(request)

  if (!sessionToken) {
    return { valid: false, error: 'Session token required' }
  }

  const db = createDb(DB)

  // Find session token
  const session = await db.query.sessionTokens.findFirst({
    where: eq(sessionTokens.id, sessionToken),
  })

  if (!session) {
    return { valid: false, error: 'Invalid session token' }
  }

  // Check if expired
  if (session.expiresAt < Date.now()) {
    // Delete expired token
    await db.delete(sessionTokens).where(eq(sessionTokens.id, sessionToken))
    return { valid: false, error: 'Session expired' }
  }

  // Get user
  const user = await db.query.users.findFirst({
    where: eq(users.id, session.userId),
    columns: {
      id: true,
      email: true,
      username: true,
    },
  })

  if (!user) {
    return { valid: false, error: 'User not found' }
  }

  return {
    valid: true,
    userId: user.id,
    sessionId: session.id,
    user,
  }
}
