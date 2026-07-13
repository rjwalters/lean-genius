PRAGMA foreign_keys=OFF;--> statement-breakpoint
CREATE TABLE `__new_comments` (
	`id` text PRIMARY KEY NOT NULL,
	`proof_id` text NOT NULL,
	`annotation_id` text,
	`line_number` integer,
	`parent_id` text,
	`user_id` text NOT NULL,
	`content` text NOT NULL,
	`created_at` integer NOT NULL,
	`updated_at` integer NOT NULL,
	`deleted_at` integer,
	FOREIGN KEY (`user_id`) REFERENCES `users`(`id`) ON UPDATE no action ON DELETE cascade
);
--> statement-breakpoint
INSERT INTO `__new_comments`("id", "proof_id", "annotation_id", "line_number", "parent_id", "user_id", "content", "created_at", "updated_at", "deleted_at") SELECT "id", "proof_id", "annotation_id", "line_number", "parent_id", "user_id", "content", "created_at", "updated_at", "deleted_at" FROM `comments`;--> statement-breakpoint
DROP TABLE `comments`;--> statement-breakpoint
ALTER TABLE `__new_comments` RENAME TO `comments`;--> statement-breakpoint
PRAGMA foreign_keys=ON;--> statement-breakpoint
CREATE INDEX `idx_comments_proof_line` ON `comments` (`proof_id`,`line_number`);--> statement-breakpoint
CREATE INDEX `idx_comments_annotation` ON `comments` (`annotation_id`);--> statement-breakpoint
CREATE INDEX `idx_comments_parent` ON `comments` (`parent_id`);--> statement-breakpoint
CREATE INDEX `idx_comments_user` ON `comments` (`user_id`);--> statement-breakpoint
CREATE INDEX `idx_comments_created` ON `comments` (`created_at`);