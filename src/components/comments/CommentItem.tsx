import { useState } from 'react'
import { useAuth } from '@/contexts/AuthContext'
import { MathText } from '@/components/ui/math'
import { CommentForm } from './CommentForm'
import { VoteButtons } from './VoteButtons'
import { formatRelativeTime } from '@/lib/comments'
import type { Comment } from '@/types/comment'
import { MessageSquare, Pencil, Trash2, ChevronDown, ChevronRight } from 'lucide-react'

interface CommentItemProps {
  comment: Comment
  onReply: (parentId: string, content: string) => Promise<void>
  onUpdate: (commentId: string, content: string) => Promise<void>
  onDelete: (commentId: string) => Promise<void>
  onVote: (commentId: string, value: 1 | -1 | 0) => Promise<void>
}

const COLLAPSE_THRESHOLD = -5

export function CommentItem({ comment, onReply, onUpdate, onDelete, onVote }: CommentItemProps) {
  const { user, isAuthenticated } = useAuth()
  const [showReplyForm, setShowReplyForm] = useState(false)
  const [showEditForm, setShowEditForm] = useState(false)
  const [isDeleting, setIsDeleting] = useState(false)
  const [isCollapsed, setIsCollapsed] = useState(comment.score <= COLLAPSE_THRESHOLD)

  const isOwner = user?.id === comment.author.id

  const handleReply = async (content: string) => {
    await onReply(comment.id, content)
    setShowReplyForm(false)
  }

  const handleEdit = async (content: string) => {
    await onUpdate(comment.id, content)
    setShowEditForm(false)
  }

  const handleDelete = async () => {
    if (!confirm('Are you sure you want to delete this comment?')) return
    setIsDeleting(true)
    try {
      await onDelete(comment.id)
    } finally {
      setIsDeleting(false)
    }
  }

  const handleVote = (value: 1 | -1 | 0) => {
    onVote(comment.id, value)
  }

  // Collapsed view for heavily downvoted comments
  if (isCollapsed) {
    return (
      <div className="py-2">
        <button
          onClick={() => setIsCollapsed(false)}
          className="flex items-center gap-1 text-xs text-muted-foreground hover:text-foreground transition-colors"
        >
          <ChevronRight className="h-3 w-3" />
          <span className="italic">Comment hidden due to low score ({comment.score})</span>
          <span className="ml-1">— click to expand</span>
        </button>
      </div>
    )
  }

  return (
    <div className="py-2">
      <div className="flex">
        {/* Vote buttons on the left */}
        <VoteButtons
          score={comment.score}
          userVote={comment.userVote}
          onVote={handleVote}
          disabled={!isAuthenticated}
        />

        {/* Comment content */}
        <div className="flex-1 min-w-0">
          <div className="flex items-center gap-2 text-xs">
            <span className="font-medium text-foreground">{comment.author.username}</span>
            <span className="text-muted-foreground">·</span>
            <span className="text-muted-foreground">{formatRelativeTime(comment.createdAt)}</span>
            {comment.updatedAt > comment.createdAt && (
              <>
                <span className="text-muted-foreground">·</span>
                <span className="text-muted-foreground italic">edited</span>
              </>
            )}
            {comment.score <= COLLAPSE_THRESHOLD && (
              <button
                onClick={() => setIsCollapsed(true)}
                className="flex items-center gap-0.5 text-muted-foreground hover:text-foreground transition-colors"
              >
                <ChevronDown className="h-3 w-3" />
                <span>collapse</span>
              </button>
            )}
          </div>

          {showEditForm ? (
            <div className="mt-2">
              <CommentForm
                onSubmit={handleEdit}
                onCancel={() => setShowEditForm(false)}
                initialValue={comment.content}
                submitLabel="Save"
              />
            </div>
          ) : (
            <div className="mt-1 text-sm leading-relaxed">
              <MathText>{comment.content}</MathText>
            </div>
          )}

          {!showEditForm && (
            <div className="flex items-center gap-4 mt-2">
              {isAuthenticated && (
                <button
                  onClick={() => setShowReplyForm(!showReplyForm)}
                  className="flex items-center gap-1 text-xs text-muted-foreground hover:text-foreground transition-colors"
                >
                  <MessageSquare className="h-3 w-3" />
                  Reply
                </button>
              )}
              {isOwner && (
                <>
                  <button
                    onClick={() => setShowEditForm(true)}
                    className="flex items-center gap-1 text-xs text-muted-foreground hover:text-foreground transition-colors"
                  >
                    <Pencil className="h-3 w-3" />
                    Edit
                  </button>
                  <button
                    onClick={handleDelete}
                    disabled={isDeleting}
                    className="flex items-center gap-1 text-xs text-muted-foreground hover:text-red-400 transition-colors"
                  >
                    <Trash2 className="h-3 w-3" />
                    {isDeleting ? 'Deleting...' : 'Delete'}
                  </button>
                </>
              )}
            </div>
          )}

          {showReplyForm && (
            <div className="mt-3 ml-4 pl-4 border-l-2 border-border">
              <CommentForm
                onSubmit={handleReply}
                onCancel={() => setShowReplyForm(false)}
                placeholder="Write a reply..."
                submitLabel="Reply"
              />
            </div>
          )}
        </div>
      </div>
    </div>
  )
}
