export interface Comment {
  id: string
  proofId: string
  lineNumber: number
  parentId: string | null
  content: string
  createdAt: number
  updatedAt: number
  author: {
    id: string
    username: string
  }
  // Voting
  score: number
  userVote: 1 | -1 | null
  // Built client-side for rendering thread tree
  children?: Comment[]
}

export interface CommentCounts {
  [lineNumber: number]: number
}
