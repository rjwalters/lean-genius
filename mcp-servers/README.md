# mcp-servers/

MCP (Model Context Protocol) servers developed in this repo. There is one:

- `aristotle/` — Node/TypeScript server (`@modelcontextprotocol/sdk`) exposing
  Harmonic Aristotle proof search as tools (`aristotle_prove`, `aristotle_submit`,
  `aristotle_status`, `aristotle_retrieve`, …). It shells out to
  `uvx --from aristotlelib aristotle`. Build with `pnpm install && pnpm build` inside
  the directory; details and tool list in `aristotle/README.md`.

Registration: the repo's `.mcp.json` does **not** currently register this server
(it registers only `squad`, from a separate checkout). The active Aristotle path for
agents is the CLI pipeline in `scripts/aristotle/` documented in
`research/ARISTOTLE-WORKFLOW.md`; the MCP route was dropped in issue #38098 after
Harmonic's API cut-over. To try the server anyway, add it to `.mcp.json`
(project scope) or `~/.claude.json` (user scope) as shown in `aristotle/README.md`.
