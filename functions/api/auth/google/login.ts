/**
 * Google OAuth initiation endpoint
 * Redirects user to Google's OAuth consent screen
 */

interface Env {
  GOOGLE_CLIENT_ID: string
  GOOGLE_CLIENT_SECRET: string
}

export async function onRequestGet(context: EventContext<Env, string, unknown>) {
  const { GOOGLE_CLIENT_ID } = context.env

  if (!GOOGLE_CLIENT_ID) {
    return new Response(
      JSON.stringify({ error: 'Google OAuth not configured' }),
      { status: 500, headers: { 'Content-Type': 'application/json' } }
    )
  }

  // Determine the redirect URI based on the request origin
  const url = new URL(context.request.url)
  const redirectUri = `${url.origin}/api/auth/google/callback`

  // Generate a random state for CSRF protection
  const state = crypto.randomUUID()

  // Store state in a short-lived cookie for verification
  const stateCookie = `oauth_state=${state}; Path=/; HttpOnly; Secure; SameSite=Lax; Max-Age=600`

  // Build Google OAuth URL
  const googleAuthUrl = new URL('https://accounts.google.com/o/oauth2/v2/auth')
  googleAuthUrl.searchParams.set('client_id', GOOGLE_CLIENT_ID)
  googleAuthUrl.searchParams.set('redirect_uri', redirectUri)
  googleAuthUrl.searchParams.set('response_type', 'code')
  googleAuthUrl.searchParams.set('scope', 'openid email profile')
  googleAuthUrl.searchParams.set('state', state)
  googleAuthUrl.searchParams.set('access_type', 'online')
  googleAuthUrl.searchParams.set('prompt', 'select_account')

  return new Response(null, {
    status: 302,
    headers: {
      'Location': googleAuthUrl.toString(),
      'Set-Cookie': stateCookie,
    },
  })
}
