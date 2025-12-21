import { sqliteTable, text, integer, index, uniqueIndex, primaryKey } from 'drizzle-orm/sqlite-core'
import { relations, sql } from 'drizzle-orm'

// =============================================================================
// Users Table
// =============================================================================

export const users = sqliteTable('users', {
  id: text('id').primaryKey(),
  email: text('email').unique().notNull(),
  passwordHash: text('password_hash'), // nullable for OAuth-only users
  username: text('username').notNull(),
  usernameChangedAt: integer('username_changed_at'), // For 30-day cooldown
  // OAuth fields
  oauthProvider: text('oauth_provider'), // 'google' | null
  oauthId: text('oauth_id'), // Provider's user ID
  // Timestamps
  createdAt: integer('created_at').notNull(),
  lastLogin: integer('last_login').notNull(),
  updatedAt: integer('updated_at').notNull(),
}, (table) => [
  index('idx_users_email').on(table.email),
  index('idx_users_oauth').on(table.oauthProvider, table.oauthId),
  uniqueIndex('idx_users_username_lower').on(sql`LOWER(${table.username})`),
])

export const usersRelations = relations(users, ({ many }) => ({
  sessions: many(sessionTokens),
  comments: many(comments),
}))

// =============================================================================
// Session Tokens Table
// =============================================================================

export const sessionTokens = sqliteTable('session_tokens', {
  id: text('id').primaryKey(),
  userId: text('user_id').notNull().references(() => users.id, { onDelete: 'cascade' }),
  expiresAt: integer('expires_at').notNull(),
  createdAt: integer('created_at').notNull(),
}, (table) => [
  index('idx_session_tokens_user').on(table.userId),
  index('idx_session_tokens_expires').on(table.expiresAt),
])

export const sessionTokensRelations = relations(sessionTokens, ({ one }) => ({
  user: one(users, {
    fields: [sessionTokens.userId],
    references: [users.id],
  }),
}))

// =============================================================================
// Comments Table (Reddit-style threaded comments on proof lines)
// =============================================================================

export const comments = sqliteTable('comments', {
  id: text('id').primaryKey(),
  proofId: text('proof_id').notNull(),
  lineNumber: integer('line_number').notNull(),
  parentId: text('parent_id'), // NULL for root comments, references comments.id for replies
  userId: text('user_id').notNull().references(() => users.id, { onDelete: 'cascade' }),
  content: text('content').notNull(), // Supports $LaTeX$ via MathText
  createdAt: integer('created_at').notNull(),
  updatedAt: integer('updated_at').notNull(),
  deletedAt: integer('deleted_at'), // Soft delete
}, (table) => [
  index('idx_comments_proof_line').on(table.proofId, table.lineNumber),
  index('idx_comments_parent').on(table.parentId),
  index('idx_comments_user').on(table.userId),
  index('idx_comments_created').on(table.createdAt),
])

export const commentsRelations = relations(comments, ({ one, many }) => ({
  user: one(users, {
    fields: [comments.userId],
    references: [users.id],
  }),
  parent: one(comments, {
    fields: [comments.parentId],
    references: [comments.id],
    relationName: 'replies',
  }),
  replies: many(comments, { relationName: 'replies' }),
  votes: many(commentVotes),
}))

// =============================================================================
// Comment Votes Table (Upvotes/Downvotes)
// =============================================================================

export const commentVotes = sqliteTable('comment_votes', {
  commentId: text('comment_id').notNull().references(() => comments.id, { onDelete: 'cascade' }),
  userId: text('user_id').notNull().references(() => users.id, { onDelete: 'cascade' }),
  value: integer('value').notNull(), // 1 for upvote, -1 for downvote
  createdAt: integer('created_at').notNull(),
}, (table) => [
  primaryKey({ columns: [table.commentId, table.userId] }),
  index('idx_votes_comment').on(table.commentId),
  index('idx_votes_user').on(table.userId),
])

export const commentVotesRelations = relations(commentVotes, ({ one }) => ({
  comment: one(comments, {
    fields: [commentVotes.commentId],
    references: [comments.id],
  }),
  user: one(users, {
    fields: [commentVotes.userId],
    references: [users.id],
  }),
}))
