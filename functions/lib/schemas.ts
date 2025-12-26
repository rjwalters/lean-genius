import { z } from 'zod'

// Username validation: 3-20 chars, alphanumeric + underscores, must start with letter
export const usernameSchema = z
  .string()
  .min(3, 'Username must be at least 3 characters')
  .max(20, 'Username must be at most 20 characters')
  .regex(
    /^[a-zA-Z][a-zA-Z0-9_]{2,19}$/,
    'Username must start with a letter and contain only letters, numbers, and underscores'
  )

// Registration request
export const registerRequestSchema = z.object({
  email: z.string().email('Invalid email address'),
  password: z
    .string()
    .min(8, 'Password must be at least 8 characters')
    .max(128, 'Password must be less than 128 characters'),
  username: usernameSchema,
})

export type RegisterRequest = z.infer<typeof registerRequestSchema>

// Login request
export const loginRequestSchema = z.object({
  email: z.string().email('Invalid email address'),
  password: z.string().min(1, 'Password is required'),
})

export type LoginRequest = z.infer<typeof loginRequestSchema>

// Comment request
// Comments can anchor to either:
//   - annotationId (stable - survives source changes, preferred)
//   - lineNumber (legacy - may drift when source changes)
// At least one anchor must be provided
export const createCommentSchema = z.object({
  proofId: z.string().min(1, 'Proof ID is required'),
  annotationId: z.string().optional(), // Stable anchor to author annotation
  lineNumber: z.number().int().positive('Line number must be positive').optional(), // Legacy anchor
  parentId: z.string().optional(),
  content: z.string().min(1, 'Content is required').max(10000, 'Content too long'),
}).refine(
  (data) => data.annotationId || data.lineNumber,
  { message: 'Either annotationId or lineNumber must be provided' }
)

export type CreateCommentRequest = z.infer<typeof createCommentSchema>

export const updateCommentSchema = z.object({
  content: z.string().min(1, 'Content is required').max(10000, 'Content too long'),
})

export type UpdateCommentRequest = z.infer<typeof updateCommentSchema>

// Vote request
export const voteCommentSchema = z.object({
  value: z.union([z.literal(1), z.literal(-1), z.literal(0)]),
})

export type VoteCommentRequest = z.infer<typeof voteCommentSchema>

// Proof submission request
export const submitProofSchema = z.object({
  title: z.string().min(1, 'Title is required').max(200, 'Title too long'),
  description: z.string().min(10, 'Please provide a description (at least 10 characters)').max(5000, 'Description too long'),
  leanSource: z.string().min(10, 'Lean source code is required').max(100000, 'Source code too long'),
  mathlibVersion: z.string().max(50).optional(),
  githubUrl: z.string().url('Invalid URL').optional().or(z.literal('')),
  additionalNotes: z.string().max(5000).optional(),
})

export type SubmitProofRequest = z.infer<typeof submitProofSchema>

// Error response
export interface ErrorResponse {
  error: string
  details?: string
}

// Helper to format validation errors
export function formatZodError(error: z.ZodError): ErrorResponse {
  const issues = error.issues || []
  return {
    error: 'Validation error',
    details: issues[0]?.message || 'Unknown validation error',
  }
}
