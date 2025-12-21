import { CommentItem } from './CommentItem'
import type { Comment } from '@/types/comment'
import { cn } from '@/lib/utils'

interface CommentThreadProps {
  comments: Comment[]
  depth?: number
  onReply: (parentId: string, content: string) => Promise<void>
  onUpdate: (commentId: string, content: string) => Promise<void>
  onDelete: (commentId: string) => Promise<void>
  onVote: (commentId: string, value: 1 | -1 | 0) => Promise<void>
}

export function CommentThread({
  comments,
  depth = 0,
  onReply,
  onUpdate,
  onDelete,
  onVote,
}: CommentThreadProps) {
  if (comments.length === 0) return null

  return (
    <div
      className={cn(
        'space-y-1',
        depth > 0 && 'ml-4 pl-4 border-l-2 border-border/50'
      )}
    >
      {comments.map((comment) => (
        <div key={comment.id}>
          <CommentItem
            comment={comment}
            onReply={onReply}
            onUpdate={onUpdate}
            onDelete={onDelete}
            onVote={onVote}
          />
          {comment.children && comment.children.length > 0 && (
            <CommentThread
              comments={comment.children}
              depth={depth + 1}
              onReply={onReply}
              onUpdate={onUpdate}
              onDelete={onDelete}
              onVote={onVote}
            />
          )}
        </div>
      ))}
    </div>
  )
}
