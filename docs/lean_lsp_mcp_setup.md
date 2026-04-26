# lean-lsp-mcp setup for pythia

This is the developer setup guide for running `oOo0oOo/lean-lsp-mcp` against
this repository. Once configured, an MCP-aware client (Claude Code, Cursor,
VSCode) gets sub-second LSP feedback (`lean_goal`, `lean_diagnostic_messages`)
and can run `lean_multi_attempt` on candidate tactic scripts in parallel.

This is the **prerequisite layer** for `pythia`,
`pythia_grind`, `pythia_aesop`, `concentration_search`
, and the `pythia.fleet.LeanProver` multi-agent closer.
Without LSP the cycle engine reduces to manual `lake build` (30-60s/edit),
which is too slow for the autoformalization-class workflows.

## Quick start

### 1. Install `uv`

```bash
curl -LsSf https://astral.sh/uv/install.sh | sh
```

Verify: `uvx --version` should print 0.5+.

### 2. Run `lake build` once in the repo

The MCP server uses `lake serve`; cold-starting `lake serve` against a
non-built repo can time out the MCP client. Pre-warming with `lake build`
makes startup <5s.

```bash
cd /path/to/pythia
lake exe cache get   # pull Mathlib oleans (first time)
lake build           # warm full build
```

Confirm the WaldIdentity + SPRT modules build:

```bash
lake build Pythia.WaldIdentity Pythia.SPRT
```

### 3. Smoke-test the server

```bash
echo '{"jsonrpc":"2.0","id":1,"method":"initialize",
       "params":{"protocolVersion":"2024-11-05","capabilities":{},
                  "clientInfo":{"name":"smoke","version":"0"}}}' \
  | uvx lean-lsp-mcp
```

You should see a JSON-RPC response with `serverInfo.name = "Lean LSP"` and
`serverInfo.version = 1.27.0` or higher. The server prints `Session ending` on
stderr after the smoke test exits — that's normal.

### 4. Configure your client

#### Claude Code

Add to `.claude/settings.json` or the user-level `~/.claude/settings.json`:

```json
{
  "mcpServers": {
    "lean-lsp": {
      "command": "uvx",
      "args": ["lean-lsp-mcp"]
    }
  }
}
```

The MCP server is invoked from the project root; ensure your Claude Code
session's working directory is the pythia checkout.

#### VSCode / Cursor

Setup wizard: `Ctrl+Shift+P → "MCP: Add Server..." → "Command (stdio)" →
"uvx lean-lsp-mcp"`.

### 5. (Recommended) Install `ripgrep`

Several tools (`lean_local_search`, `lean_verify` source scanning) use
`ripgrep` for speed:

```bash
sudo apt install ripgrep    # Ubuntu/Debian
brew install ripgrep        # macOS
```

## Tool catalog (1.27.0)

### Core LSP — used by `pythia` Phase 1

| Tool | What it does |
|------|--------------|
| `lean_goal(file, line)` | Live proof state at position |
| `lean_diagnostic_messages(file)` | Compiler errors/warnings |
| `lean_hover_info(file, line, col)` | Type signature + docs |
| `lean_completions(file, line, col)` | IDE-style completions |

### Tactic exploration — used by `pythia` Phase 2

| Tool | What it does |
|------|--------------|
| `lean_multi_attempt(file, line, snippets=[...])` | Test multiple tactics in parallel; ~5× speed in REPL mode |
| `lean_run_code` | Run a standalone Lean snippet |
| `lean_code_actions(file, line)` | Resolve `simp?` / `exact?` / `apply?` "Try this" |
| `lean_verify(name)` | Axiom check + source scan; required at Phase 4 (Review) |

### Search — used by `concentration_search` and Phase 1 oracle

| Tool | Rate limit (external) | Use |
|------|----------------------|-----|
| `lean_local_search(query)` | none | First fallback — search this repo + Mathlib oleans |
| `lean_leansearch(query)` | 3 / 30s | Natural-language to Mathlib name |
| `lean_loogle(pattern)` | 3 / 30s | Type-pattern search (e.g. `\|- _ ≤ exp _`) |
| `lean_leanfinder(query)` | 10 / 30s | Goal-aware semantic search |
| `lean_state_search(goal)` | 3 / 30s | Goal → closing lemmas |
| `lean_hammer_premise(file, line, col)` | 3 / 30s | Premises to feed `simp` / `aesop` / `grind` |

### Build / introspection

| Tool | What it does |
|------|--------------|
| `lean_build` | Rebuild + restart LSP (slow) |
| `lean_file_outline(file)` | Token-efficient file skeleton |
| `lean_declaration_file(name)` | Source of a declaration (large output) |
| `lean_profile_proof(name)` | Profile a theorem; tactic hotspots |

## Self-hosting (follow-up)

External rate limits (3-10 / 30s on most search tools) will throttle the
multi-agent fleet once we exceed ~6 concurrent children. Mitigation:

| Tool | Self-host how |
|------|---------------|
| `lean_loogle` | `LEAN_LOOGLE_LOCAL=true` after one-time ~10min build |
| `lean_leanfinder` | `LEAN_LEANFINDER_URL=<our-instance>` (HF model + Flask) |
| `lean_hammer_premise` | `LEAN_HAMMER_URL=<our-instance>` (premise-search.com is the reference impl) |

REPL mode for `lean_multi_attempt` (~5× speedup):

```bash
export LEAN_REPL=true
```

The `repl` package needs to be pinned to the same Lean version as
pythia (currently 4.28.0 per Mathlib parity).

## Troubleshooting

### `uvx lean-lsp-mcp` hangs on first run

First invocation downloads ~5 MiB of dependencies (cryptography, pydantic-core, pygments). Subsequent runs use the uv cache.

### MCP client times out

Pre-warm with `lake build`. Some clients have an MCP startup timeout in the 30-60s range; cold `lake serve` can exceed it.

### "no goals" vs `lean_goal` returning nothing

`"no goals"` literally means the proof is complete at that position — that's success, not an error.

### Search returns `[]` with `isError: false`

That means the search ran but found no results. Try a different query shape (NL → leansearch; type pattern → loogle; semantic → leanfinder).

## References

- [oOo0oOo/lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) — upstream
- — this ticket (pythia integration + self-hosting)
- — pythia.fleet.LeanProver (uses lean-lsp-mcp as substrate)
- — `pythia` (cycle engine built on top)
- `cameronfreer/lean4-skills` — the cycle-engine model we adopt
