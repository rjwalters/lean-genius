import { useState, useEffect, useCallback, useMemo } from 'react'
import { useAuth } from '@/contexts/AuthContext'
import { CommentForm } from './CommentForm'
import { CommentThread } from './CommentThread'
import {
  fetchComments,
  createComment,
  updateComment,
  deleteComment,
  buildCommentTree,
} from '@/lib/comments'
import type { Comment } from '@/types/comment'
import { MessageSquare, RefreshCw } from 'lucide-react'
import { Button } from '@/components/ui/button'

interface CommentSectionProps {
  proofId: string
  lineNumber: number
}

export function CommentSection({ proofId, lineNumber }: CommentSectionProps) {
  const { isAuthenticated } = useAuth()
  const [comments, setComments] = useState<Comment[]>([])
  const [isLoading, setIsLoading] = useState(true)
  const [error, setError] = useState<string | null>(null)

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

  const tree = useMemo(() => buildCommentTree(comments), [comments])

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

      {/* Comments */}
      {tree.length > 0 ? (
        <CommentThread
          comments={tree}
          onReply={handleReply}
          onUpdate={handleUpdate}
          onDelete={handleDelete}
        />
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
