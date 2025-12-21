/**
 * Google OAuth callback endpoint
 * Handles the redirect from Google after user authorization
 */

import { createDb } from '../../../../shared/db/client'
import { users, sessionTokens } from '../../../../shared/db/schema'
import { eq, and } from 'drizzle-orm'

interface Env {
  DB: D1Database
  GOOGLE_CLIENT_ID: string
  GOOGLE_CLIENT_SECRET: string
}

interface GoogleTokenResponse {
  access_token: string
  expires_in: number
  token_type: string
  scope: string
  id_token?: string
}

interface GoogleUserInfo {
  id: string
  email: string
  verified_email: boolean
  name?: string
  given_name?: string
  family_name?: string
  picture?: string
}

const SESSION_DURATION_MS = 30 * 24 * 60 * 60 * 1000 // 30 days

export async function onRequestGet(context: EventContext<Env, string, unknown>) {
  const { DB, GOOGLE_CLIENT_ID, GOOGLE_CLIENT_SECRET } = context.env
  const db = createDb(DB)
  const url = new URL(context.request.url)

  // Get authorization code and state from query params
  const code = url.searchParams.get('code')
  const state = url.searchParams.get('state')
  const error = url.searchParams.get('error')

  // Handle OAuth errors
  if (error) {
    return redirectWithError(url.origin, `OAuth error: ${error}`)
  }

  if (!code || !state) {
    return redirectWithError(url.origin, 'Missing authorization code or state')
  }

  // Verify state from cookie (CSRF protection)
  const cookies = parseCookies(context.request.headers.get('Cookie') || '')
  const storedState = cookies['oauth_state']

  if (!storedState || storedState !== state) {
    return redirectWithError(url.origin, 'Invalid state parameter')
  }

  try {
    // Exchange authorization code for access token
    const redirectUri = `${url.origin}/api/auth/google/callback`
    const tokenResponse = await fetch('https://oauth2.googleapis.com/token', {
      method: 'POST',
      headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
      body: new URLSearchParams({
        code,
        client_id: GOOGLE_CLIENT_ID,
        client_secret: GOOGLE_CLIENT_SECRET,
        redirect_uri: redirectUri,
        grant_type: 'authorization_code',
      }),
    })

    if (!tokenResponse.ok) {
      const errorData = await tokenResponse.text()
      console.error('Token exchange failed:', errorData)
      return redirectWithError(url.origin, 'Failed to exchange authorization code')
    }

    const tokenData: GoogleTokenResponse = await tokenResponse.json()

    // Fetch user info from Google
    const userInfoResponse = await fetch('https://www.googleapis.com/oauth2/v2/userinfo', {
      headers: { 'Authorization': `Bearer ${tokenData.access_token}` },
    })

    if (!userInfoResponse.ok) {
      return redirectWithError(url.origin, 'Failed to fetch user info from Google')
    }

    const googleUser: GoogleUserInfo = await userInfoResponse.json()

    if (!googleUser.email) {
      return redirectWithError(url.origin, 'No email provided by Google')
    }

    // Find or create user in database
    const now = Date.now()
    let user = await db.query.users.findFirst({
      where: and(
        eq(users.oauthProvider, 'google'),
        eq(users.oauthId, googleUser.id)
      ),
    })

    let userId: string

    if (!user) {
      // Check if email already exists (might have registered with password)
      const existingUser = await db.query.users.findFirst({
        where: eq(users.email, googleUser.email),
      })

      if (existingUser) {
        // Link Google account to existing user
        await db.update(users)
          .set({
            oauthProvider: 'google',
            oauthId: googleUser.id,
            updatedAt: now,
          })
          .where(eq(users.id, existingUser.id))
        userId = existingUser.id
      } else {
        // Create new user
        userId = crypto.randomUUID()
        // Generate username from email or Google name
        const baseUsername = googleUser.name?.replace(/\s+/g, '') ||
                            googleUser.email.split('@')[0]
        const username = await generateUniqueUsername(db, baseUsername)

        await db.insert(users).values({
          id: userId,
          email: googleUser.email,
          username,
          oauthProvider: 'google',
          oauthId: googleUser.id,
          createdAt: now,
          lastLogin: now,
          updatedAt: now,
        })
      }
    } else {
      // Update last login
      userId = user.id
      await db.update(users)
        .set({ lastLogin: now, updatedAt: now })
        .where(eq(users.id, user.id))
    }

    // Create session token
    const sessionTokenId = crypto.randomUUID()
    const expiresAt = now + SESSION_DURATION_MS

    await db.insert(sessionTokens).values({
      id: sessionTokenId,
      userId: userId,
      expiresAt,
      createdAt: now,
    })

    // Redirect to frontend with session token
    // The frontend will store this and complete the auth flow
    const successUrl = new URL('/', url.origin)
    successUrl.searchParams.set('oauth_token', sessionTokenId)
    successUrl.searchParams.set('oauth_provider', 'google')

    // Clear the state cookie
    const clearStateCookie = 'oauth_state=; Path=/; HttpOnly; Secure; SameSite=Lax; Max-Age=0'

    return new Response(null, {
      status: 302,
      headers: {
        'Location': successUrl.toString(),
        'Set-Cookie': clearStateCookie,
      },
    })
  } catch (err) {
    console.error('OAuth callback error:', err)
    return redirectWithError(url.origin, 'An unexpected error occurred')
  }
}

function redirectWithError(origin: string, message: string): Response {
  const errorUrl = new URL('/', origin)
  errorUrl.searchParams.set('auth_error', message)

  return new Response(null, {
    status: 302,
    headers: {
      'Location': errorUrl.toString(),
      'Set-Cookie': 'oauth_state=; Path=/; HttpOnly; Secure; SameSite=Lax; Max-Age=0',
    },
  })
}

function parseCookies(cookieHeader: string): Record<string, string> {
  const cookies: Record<string, string> = {}
  if (!cookieHeader) return cookies

  for (const cookie of cookieHeader.split(';')) {
    const [name, ...rest] = cookie.trim().split('=')
    if (name && rest.length > 0) {
      cookies[name] = rest.join('=')
    }
  }
  return cookies
}

async function generateUniqueUsername(
  db: ReturnType<typeof createDb>,
  baseUsername: string
): Promise<string> {
  // Clean the base username
  let username = baseUsername.toLowerCase().replace(/[^a-z0-9_]/g, '')
  if (username.length < 3) username = 'user'
  if (username.length > 20) username = username.slice(0, 20)

  // Check if it's already taken
  const existing = await db.query.users.findFirst({
    where: eq(users.username, username),
  })

  if (!existing) return username

  // Add random suffix
  for (let i = 0; i < 10; i++) {
    const suffix = Math.floor(Math.random() * 10000)
    const candidate = `${username.slice(0, 15)}${suffix}`
    const exists = await db.query.users.findFirst({
      where: eq(users.username, candidate),
    })
    if (!exists) return candidate
  }

  // Fallback to UUID-based username
  return `user_${crypto.randomUUID().slice(0, 8)}`
}
