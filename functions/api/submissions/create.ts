import { z } from 'zod'
import { submitProofSchema, formatZodError } from '../../lib/schemas'
import { validateSession } from '../../lib/auth'
import { sendEmail, generateSubmissionEmail } from '../../lib/email'

interface Env {
  DB: D1Database
  RESEND_API_KEY?: string
  EMAIL_FROM?: string
  SUBMISSION_EMAIL?: string
}

export async function onRequestPost(context: EventContext<Env, string, unknown>) {
  const { DB, RESEND_API_KEY, EMAIL_FROM, SUBMISSION_EMAIL } = context.env

  try {
    // Validate session - must be logged in
    const session = await validateSession(context.request, DB)
    if (!session.valid) {
      return new Response(
        JSON.stringify({ error: 'You must be logged in to submit a proof' }),
        { status: 401, headers: { 'Content-Type': 'application/json' } }
      )
    }

    // Parse and validate request body
    const body = await context.request.json()
    const submission = submitProofSchema.parse(body)

    // Generate email content
    const emailContent = generateSubmissionEmail({
      title: submission.title,
      description: submission.description,
      leanSource: submission.leanSource,
      mathlibVersion: submission.mathlibVersion,
      githubUrl: submission.githubUrl || undefined,
      additionalNotes: submission.additionalNotes,
      userEmail: session.user.email,
      username: session.user.username,
      submittedAt: new Date().toISOString(),
    })

    // Send email to admin
    const adminEmail = SUBMISSION_EMAIL || 'proofs@lean-genius.com'
    const result = await sendEmail(
      {
        to: adminEmail,
        subject: emailContent.subject,
        html: emailContent.html,
        text: emailContent.text,
        replyTo: session.user.email, // So admin can reply directly to submitter
      },
      { RESEND_API_KEY, EMAIL_FROM }
    )

    if (!result.success) {
      console.error('Failed to send submission email:', result.error)
      return new Response(
        JSON.stringify({ error: 'Failed to send submission. Please try again later.' }),
        { status: 500, headers: { 'Content-Type': 'application/json' } }
      )
    }

    return new Response(
      JSON.stringify({
        success: true,
        message: 'Your proof has been submitted! We\'ll review it and get back to you.',
      }),
      { status: 200, headers: { 'Content-Type': 'application/json' } }
    )
  } catch (error) {
    console.error('Submission error:', error)

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
