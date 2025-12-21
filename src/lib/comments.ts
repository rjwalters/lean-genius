import type { Comment, CommentCounts } from '@/types/comment'
import { getSessionToken } from '@/contexts/AuthContext'

const API_BASE = '/api/comments'

// Build a tree structure from flat comment list
export function buildCommentTree(comments: Comment[]): Comment[] {
  const map = new Map<string, Comment>()
  const roots: Comment[] = []

  // First pass: create a map and initialize children arrays
  for (const comment of comments) {
    map.set(comment.id, { ...comment, children: [] })
  }

  // Second pass: build the tree
  for (const comment of comments) {
    const node = map.get(comment.id)!
    if (comment.parentId) {
      const parent = map.get(comment.parentId)
      if (parent) {
        parent.children = parent.children || []
        parent.children.push(node)
      } else {
        // Parent not found (maybe deleted), treat as root
        roots.push(node)
      }
    } else {
      roots.push(node)
    }
  }

  return roots
}

// Fetch comments for a proof/line
export async function fetchComments(proofId: string, lineNumber?: number): Promise<Comment[]> {
  const params = new URLSearchParams({ proof_id: proofId })
  if (lineNumber !== undefined) {
    params.set('line', lineNumber.toString())
  }

  // Include auth header if available to get user's votes
  const token = getSessionToken()
  const headers: HeadersInit = {}
  if (token) {
    headers.Authorization = `Bearer ${token}`
  }

  const response = await fetch(`${API_BASE}?${params}`, { headers })
  if (!response.ok) {
    throw new Error('Failed to fetch comments')
  }

  const data = await response.json()
  return data.comments
}

// Fetch comment counts per line for a proof
export async function fetchCommentCounts(proofId: string): Promise<CommentCounts> {
  const response = await fetch(`${API_BASE}/counts?proof_id=${proofId}`)
  if (!response.ok) {
    throw new Error('Failed to fetch comment counts')
  }

  const data = await response.json()
  return data.counts
}

// Create a new comment
export async function createComment(
  proofId: string,
  lineNumber: number,
  content: string,
  parentId?: string
): Promise<Comment> {
  const token = getSessionToken()
  if (!token) {
    throw new Error('Not authenticated')
  }

  const response = await fetch(`${API_BASE}/create`, {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
      Authorization: `Bearer ${token}`,
    },
    body: JSON.stringify({ proofId, lineNumber, content, parentId }),
  })

  if (!response.ok) {
    const data = await response.json()
    throw new Error(data.error || 'Failed to create comment')
  }

  const data = await response.json()
  return data.comment
}

// Update a comment
export async function updateComment(commentId: string, content: string): Promise<Comment> {
  const token = getSessionToken()
  if (!token) {
    throw new Error('Not authenticated')
  }

  const response = await fetch(`${API_BASE}/${commentId}`, {
    method: 'PUT',
    headers: {
      'Content-Type': 'application/json',
      Authorization: `Bearer ${token}`,
    },
    body: JSON.stringify({ content }),
  })

  if (!response.ok) {
    const data = await response.json()
    throw new Error(data.error || 'Failed to update comment')
  }

  const data = await response.json()
  return data.comment
}

// Delete a comment
export async function deleteComment(commentId: string): Promise<void> {
  const token = getSessionToken()
  if (!token) {
    throw new Error('Not authenticated')
  }

  const response = await fetch(`${API_BASE}/${commentId}`, {
    method: 'DELETE',
    headers: {
      Authorization: `Bearer ${token}`,
    },
  })

  if (!response.ok) {
    const data = await response.json()
    throw new Error(data.error || 'Failed to delete comment')
  }
}

// Vote on a comment
export async function voteComment(
  commentId: string,
  value: 1 | -1 | 0
): Promise<{ score: number; userVote: 1 | -1 | null }> {
  const token = getSessionToken()
  if (!token) {
    throw new Error('Not authenticated')
  }

  const response = await fetch(`${API_BASE}/${commentId}/vote`, {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
      Authorization: `Bearer ${token}`,
    },
    body: JSON.stringify({ value }),
  })

  if (!response.ok) {
    const data = await response.json()
    throw new Error(data.error || 'Failed to vote')
  }

  return response.json()
}

// Format relative time
export function formatRelativeTime(timestamp: number): string {
  const now = Date.now()
  const diff = now - timestamp

  const seconds = Math.floor(diff / 1000)
  const minutes = Math.floor(seconds / 60)
  const hours = Math.floor(minutes / 60)
  const days = Math.floor(hours / 24)

  if (days > 0) return `${days}d ago`
  if (hours > 0) return `${hours}h ago`
  if (minutes > 0) return `${minutes}m ago`
  return 'just now'
}
