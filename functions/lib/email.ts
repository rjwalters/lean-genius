/**
 * Email service for Cloudflare Workers using Resend
 */

interface EmailOptions {
  to: string
  subject: string
  html: string
  text?: string
  replyTo?: string
}

interface EmailEnv {
  RESEND_API_KEY?: string
  EMAIL_FROM?: string
}

export interface SendEmailResult {
  success: boolean
  id?: string
  error?: string
}

/**
 * Send an email using Resend
 */
export async function sendEmail(
  options: EmailOptions,
  env: EmailEnv
): Promise<SendEmailResult> {
  const apiKey = env.RESEND_API_KEY
  const from = env.EMAIL_FROM || 'LeanGenius <noreply@lean-genius.com>'

  // Development mode - log to console if no API key
  if (!apiKey) {
    console.log('=== EMAIL (No API Key - Development Mode) ===')
    console.log(`To: ${options.to}`)
    console.log(`From: ${from}`)
    console.log(`Subject: ${options.subject}`)
    console.log(`Reply-To: ${options.replyTo || 'N/A'}`)
    console.log(`Body: ${options.text || options.html}`)
    console.log('==============================================')
    return { success: true, id: 'dev-mode' }
  }

  try {
    const response = await fetch('https://api.resend.com/emails', {
      method: 'POST',
      headers: {
        'Authorization': `Bearer ${apiKey}`,
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({
        from,
        to: [options.to],
        subject: options.subject,
        html: options.html,
        text: options.text,
        reply_to: options.replyTo,
      }),
    })

    if (!response.ok) {
      const errorData = await response.json().catch(() => ({}))
      console.error('Resend API error:', response.status, errorData)
      return {
        success: false,
        error: (errorData as { message?: string }).message || `Email send failed with status ${response.status}`,
      }
    }

    const data = await response.json()
    return {
      success: true,
      id: (data as { id?: string }).id,
    }
  } catch (error) {
    console.error('Email send error:', error)
    return {
      success: false,
      error: error instanceof Error ? error.message : 'Unknown email error',
    }
  }
}

/**
 * Generate proof submission email HTML
 */
export function generateSubmissionEmail(submission: {
  title: string
  description: string
  leanSource: string
  mathlibVersion?: string
  githubUrl?: string
  additionalNotes?: string
  userEmail: string
  username: string
  submittedAt: string
}): { subject: string; html: string; text: string } {
  const subject = `[LeanGenius] New Submission: ${submission.title}`

  const html = `
<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>New Proof Submission</title>
</head>
<body style="font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif; line-height: 1.6; color: #333; max-width: 800px; margin: 0 auto; padding: 20px;">
  <div style="background: linear-gradient(135deg, #3b82f6 0%, #8b5cf6 100%); padding: 24px; border-radius: 8px 8px 0 0;">
    <h1 style="color: white; margin: 0; font-size: 20px;">New Proof Submission</h1>
  </div>

  <div style="background: #f9fafb; padding: 24px; border: 1px solid #e5e7eb; border-top: none;">
    <p style="margin-top: 0;">
      <strong>${submission.username}</strong> (${submission.userEmail}) submitted a proof.
    </p>

    <h2 style="font-size: 18px; margin-top: 24px; color: #111;">Title</h2>
    <p style="background: white; padding: 12px; border-radius: 6px; border: 1px solid #e5e7eb;">${escapeHtml(submission.title)}</p>

    <h2 style="font-size: 18px; margin-top: 24px; color: #111;">Description</h2>
    <p style="background: white; padding: 12px; border-radius: 6px; border: 1px solid #e5e7eb; white-space: pre-wrap;">${escapeHtml(submission.description)}</p>

    <h2 style="font-size: 18px; margin-top: 24px; color: #111;">Mathlib Version</h2>
    <p style="background: white; padding: 12px; border-radius: 6px; border: 1px solid #e5e7eb;">${escapeHtml(submission.mathlibVersion || 'Not specified')}</p>

    <h2 style="font-size: 18px; margin-top: 24px; color: #111;">GitHub Repository</h2>
    <p style="background: white; padding: 12px; border-radius: 6px; border: 1px solid #e5e7eb;">
      ${submission.githubUrl
        ? `<a href="${escapeHtml(submission.githubUrl)}" style="color: #3b82f6;">${escapeHtml(submission.githubUrl)}</a>`
        : 'Not provided'}
    </p>

    ${submission.additionalNotes ? `
    <h2 style="font-size: 18px; margin-top: 24px; color: #111;">Additional Notes</h2>
    <p style="background: white; padding: 12px; border-radius: 6px; border: 1px solid #e5e7eb; white-space: pre-wrap;">${escapeHtml(submission.additionalNotes)}</p>
    ` : ''}

    <h2 style="font-size: 18px; margin-top: 24px; color: #111;">Lean Source Code</h2>
    <pre style="background: #1e1e1e; color: #d4d4d4; padding: 16px; border-radius: 6px; overflow-x: auto; font-family: 'Fira Code', 'Consolas', monospace; font-size: 13px; line-height: 1.5;">${escapeHtml(submission.leanSource)}</pre>
  </div>

  <div style="background: #f3f4f6; padding: 16px; border: 1px solid #e5e7eb; border-top: none; border-radius: 0 0 8px 8px; font-size: 12px; color: #6b7280;">
    <p style="margin: 0;">Submitted: ${submission.submittedAt}</p>
    <p style="margin: 4px 0 0 0;">Reply directly to this email to respond to the submitter.</p>
  </div>
</body>
</html>
`.trim()

  const text = `
New Proof Submission
====================

From: ${submission.username} (${submission.userEmail})
Submitted: ${submission.submittedAt}

Title
-----
${submission.title}

Description
-----------
${submission.description}

Mathlib Version
---------------
${submission.mathlibVersion || 'Not specified'}

GitHub Repository
-----------------
${submission.githubUrl || 'Not provided'}

${submission.additionalNotes ? `Additional Notes
----------------
${submission.additionalNotes}

` : ''}Lean Source Code
----------------
${submission.leanSource}

---
Reply directly to this email to respond to the submitter.
`.trim()

  return { subject, html, text }
}

function escapeHtml(text: string): string {
  return text
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#039;')
}
