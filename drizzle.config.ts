import type { Config } from 'drizzle-kit'

export default {
  schema: './shared/db/schema.ts',
  out: './drizzle',
  dialect: 'sqlite',
} satisfies Config
