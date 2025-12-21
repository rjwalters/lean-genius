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
  // Built client-side for rendering thread tree
  children?: Comment[]
}

export interface CommentCounts {
  [lineNumber: number]: number
}
