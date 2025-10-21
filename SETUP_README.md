# Setup Instructions

## Quick Setup (Recommended)

If you have sudo access:

```bash
./setup.sh
```

This will:
1. Install elan (Lean version manager)
2. Install the correct Lean toolchain (v4.22.0-rc2)
3. Download cached build artifacts

## Manual Setup (Without sudo)

If you don't have sudo access or prefer manual installation:

### 1. Install elan manually

```bash
# Download and install elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Add to PATH (add this to your ~/.bashrc or ~/.zshrc)
export PATH="$HOME/.elan/bin:$PATH"
```

### 2. Install Lean toolchain

```bash
elan toolchain install leanprover/lean4:v4.22.0-rc2
elan override set leanprover/lean4:v4.22.0-rc2
```

### 3. Download cache

```bash
lake exe cache get
```

If cache download fails, you can skip it - the project will just take longer to build.

## Running Tests

Once setup is complete:

```bash
# Quick test run
./test.sh

# Or manually:
lake build
lake test

# Full project check (includes smoke tests)
./scripts/check.sh
```

## Verifying Installation

Check that everything is installed correctly:

```bash
# Check elan
elan --version

# Check current toolchain
elan show

# Should show: leanprover/lean4:v4.22.0-rc2

# Check lake (Lean build tool)
lake --version
```

## Troubleshooting

### "elan: command not found"

Make sure elan is in your PATH:
```bash
export PATH="$HOME/.elan/bin:$PATH"
```

### "lake: command not found"

Elan should have installed lake automatically. Try:
```bash
elan toolchain install leanprover/lean4:v4.22.0-rc2
```

### Cache download fails

This is not critical. The project will build from scratch:
```bash
lake build  # Will take longer but will work
```

### Permission denied when running setup.sh

Make sure the script is executable:
```bash
chmod +x setup.sh
```

### Build errors

Try cleaning and rebuilding:
```bash
lake clean
lake build
```

## Docker Alternative

If you prefer using Docker:

```bash
# Build Docker image with Lean
docker build -t p-np2 .

# Run tests in container
docker run --rm p-np2 lake test
```

(Note: Dockerfile not included yet, but can be added if needed)

## CI/CD

The project can be tested in CI using the setup script:

```yaml
# Example GitHub Actions workflow
- name: Setup Lean
  run: ./setup.sh

- name: Build
  run: lake build

- name: Test
  run: lake test
```

## Next Steps

After successful setup, see:
- `DEVELOPMENT.md` - Development guide
- `pnp3/Docs/PLAN.md` - Project plan and architecture
- `README.md` - Project overview
