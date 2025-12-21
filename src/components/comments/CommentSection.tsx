import { useState, useEffect, useCallback, useMemo } from 'react'
import { useAuth } from '@/contexts/AuthContext'
import { CommentForm } from './CommentForm'
import { CommentThread } from './CommentThread'
import {
  fetchComments,
  createComment,
  updateComment,
  deleteComment,
  voteComment,
  buildCommentTree,
} from '@/lib/comments'
import type { Comment } from '@/types/comment'
import { MessageSquare, RefreshCw, ArrowUpDown } from 'lucide-react'
import { Button } from '@/components/ui/button'

type SortOrder = 'newest' | 'top'

interface CommentSectionProps {
  proofId: string
  lineNumber: number
}

// Sort comments recursively
function sortComments(comments: Comment[], order: SortOrder): Comment[] {
  const sorted = [...comments].sort((a, b) => {
    if (order === 'top') {
      return b.score - a.score
    }
    // newest first
    return b.createdAt - a.createdAt
  })

  return sorted.map((comment) => ({
    ...comment,
    children: comment.children ? sortComments(comment.children, order) : undefined,
  }))
}

export function CommentSection({ proofId, lineNumber }: CommentSectionProps) {
  const { isAuthenticated } = useAuth()
  const [comments, setComments] = useState<Comment[]>([])
  const [isLoading, setIsLoading] = useState(true)
  const [error, setError] = useState<string | null>(null)
  const [sortOrder, setSortOrder] = useState<SortOrder>('newest')

  const loadComments = useCallback(async () => {
    setIsLoading(true)
    setError(null)
    try {
      const data = await fetchComments(proofId, lineNumber)
      setComments(data)
    } catch (err) {
      setError(err instanceof Error ? err.message : 'Failed to load comments')
    } finally {
      setIsLoading(false)
    }
  }, [proofId, lineNumber])

  useEffect(() => {
    loadComments()
  }, [loadComments])

  const tree = useMemo(() => {
    const built = buildCommentTree(comments)
    return sortComments(built, sortOrder)
  }, [comments, sortOrder])

  const handleCreate = async (content: string) => {
    const newComment = await createComment(proofId, lineNumber, content)
    setComments((prev) => [...prev, newComment])
  }

  const handleReply = async (parentId: string, content: string) => {
    const newComment = await createComment(proofId, lineNumber, content, parentId)
    setComments((prev) => [...prev, newComment])
  }

  const handleUpdate = async (commentId: string, content: string) => {
    const updated = await updateComment(commentId, content)
    setComments((prev) =>
      prev.map((c) => (c.id === commentId ? { ...c, ...updated } : c))
    )
  }

  const handleDelete = async (commentId: string) => {
    await deleteComment(commentId)
    setComments((prev) => prev.filter((c) => c.id !== commentId))
  }

  const handleVote = async (commentId: string, value: 1 | -1 | 0) => {
    // Optimistic update
    setComments((prev) =>
      prev.map((c) => {
        if (c.id !== commentId) return c
        const oldVote = c.userVote ?? 0
        const newVote = value === 0 ? null : value
        const scoreDelta = (value === 0 ? 0 : value) - oldVote
        return {
          ...c,
          score: c.score + scoreDelta,
          userVote: newVote,
        }
      })
    )

    try {
      const result = await voteComment(commentId, value)
      // Sync with server response
      setComments((prev) =>
        prev.map((c) =>
          c.id === commentId
            ? { ...c, score: result.score, userVote: result.userVote }
            : c
        )
      )
    } catch (err) {
      // Revert on error
      loadComments()
    }
  }

  if (isLoading) {
    return (
      <div className="p-4 flex items-center justify-center text-muted-foreground">
        <RefreshCw className="h-4 w-4 animate-spin mr-2" />
        Loading comments...
      </div>
    )
  }

  if (error) {
    return (
      <div className="p-4">
        <p className="text-sm text-red-400 mb-2">{error}</p>
        <Button variant="ghost" size="sm" onClick={loadComments}>
          <RefreshCw className="h-4 w-4 mr-2" />
          Retry
        </Button>
      </div>
    )
  }

  return (
    <div className="p-4">
      {/* New comment form */}
      {isAuthenticated ? (
        <div className="mb-4">
          <CommentForm onSubmit={handleCreate} placeholder="Add a comment about this line..." />
        </div>
      ) : (
        <div className="mb-4 p-3 bg-muted/30 rounded-md text-center">
          <p className="text-sm text-muted-foreground">
            Sign in to join the discussion
          </p>
        </div>
      )}

      {/* Sort and Comments */}
      {tree.length > 0 ? (
        <>
          <div className="flex items-center gap-2 mb-3">
            <ArrowUpDown className="h-3 w-3 text-muted-foreground" />
            <select
              value={sortOrder}
              onChange={(e) => setSortOrder(e.target.value as SortOrder)}
              className="text-xs bg-transparent border border-border rounded px-2 py-1 text-foreground focus:outline-none focus:ring-1 focus:ring-ring"
            >
              <option value="newest">Newest</option>
              <option value="top">Top</option>
            </select>
          </div>
          <CommentThread
            comments={tree}
            onReply={handleReply}
            onUpdate={handleUpdate}
            onDelete={handleDelete}
            onVote={handleVote}
          />
        </>
      ) : (
        <div className="text-center py-8 text-muted-foreground">
          <MessageSquare className="h-8 w-8 mx-auto mb-2 opacity-30" />
          <p className="text-sm">No comments yet</p>
          <p className="text-xs mt-1">Be the first to discuss this line</p>
        </div>
      )}

      {/* Refresh button */}
      <div className="mt-4 pt-4 border-t border-border">
        <Button variant="ghost" size="sm" onClick={loadComments} className="w-full">
          <RefreshCw className="h-4 w-4 mr-2" />
          Refresh comments
        </Button>
      </div>
    </div>
  )
}
