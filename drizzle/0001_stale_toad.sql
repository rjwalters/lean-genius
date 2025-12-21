PRAGMA foreign_keys=OFF;--> statement-breakpoint
CREATE TABLE `__new_users` (
	`id` text PRIMARY KEY NOT NULL,
	`email` text NOT NULL,
	`password_hash` text,
	`username` text NOT NULL,
	`oauth_provider` text,
	`oauth_id` text,
	`created_at` integer NOT NULL,
	`last_login` integer NOT NULL,
	`updated_at` integer NOT NULL
);
--> statement-breakpoint
INSERT INTO `__new_users`("id", "email", "password_hash", "username", "oauth_provider", "oauth_id", "created_at", "last_login", "updated_at") SELECT "id", "email", "password_hash", "username", "oauth_provider", "oauth_id", "created_at", "last_login", "updated_at" FROM `users`;--> statement-breakpoint
DROP TABLE `users`;--> statement-breakpoint
ALTER TABLE `__new_users` RENAME TO `users`;--> statement-breakpoint
PRAGMA foreign_keys=ON;--> statement-breakpoint
CREATE UNIQUE INDEX `users_email_unique` ON `users` (`email`);--> statement-breakpoint
CREATE INDEX `idx_users_email` ON `users` (`email`);--> statement-breakpoint
CREATE INDEX `idx_users_oauth` ON `users` (`oauth_provider`,`oauth_id`);--> statement-breakpoint
CREATE UNIQUE INDEX `idx_users_username_lower` ON `users` (LOWER(`username`));