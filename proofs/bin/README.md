# Safety Wrappers for Lean Build Tools

This directory contains wrapper scripts that intercept dangerous commands and redirect to safe alternatives.

## Why This Exists

**Problem**: Lean tactics like `grind` can consume 100GB+ memory in seconds, crashing the host system before any external monitoring can detect and react.

**Solution**: Intercept `lake build` commands and redirect to Docker-based builds that enforce hard memory limits via Linux cgroups.

## How It Works

When `proofs/bin` is in your PATH (before `~/.elan/bin`), the `lake` wrapper script intercepts commands:

| Command | Action |
|---------|--------|
| `lake build` | **BLOCKED** - prints safe alternative |
| `lake env` | Passed through to real lake |
| `lake clean` | Passed through to real lake |
| `lake update` | Passed through to real lake |
| `lake --version` | Passed through to real lake |

## Activation

### Option 1: direnv (recommended)

If you use [direnv](https://direnv.net/), the project's `.envrc` automatically adds this to your PATH:

```bash
# Already in .envrc:
export PATH="$PWD/proofs/bin:$PATH"
```

Just run `direnv allow` in the project root.

### Option 2: Manual activation

Source the activation script:

```bash
source ./proofs/scripts/activate-safety.sh
```

Or add to your shell profile:

```bash
# In ~/.bashrc or ~/.zshrc
export PATH="/path/to/lean-genius/proofs/bin:$PATH"
```

## Bypass (Use With Extreme Caution)

If you absolutely must run `lake build` directly (e.g., debugging Docker issues), you can bypass the safety wrapper:

```bash
LAKE_UNSAFE=1 lake build Proofs.YourProof
```

**WARNING**: This can crash your system if the build consumes excessive memory.

## Safe Alternative

Always prefer the Docker wrapper:

```bash
# Build specific target (recommended)
./proofs/scripts/docker-build.sh Proofs.YourProof

# Build all
./proofs/scripts/docker-build.sh

# With custom limits
LEAN_MEMORY_LIMIT=8192 ./proofs/scripts/docker-build.sh   # 8GB limit
LEAN_BUILD_TIMEOUT=30m ./proofs/scripts/docker-build.sh   # 30min timeout
```

## Files

- `lake` - Wrapper script that intercepts `lake build`
- `README.md` - This documentation
