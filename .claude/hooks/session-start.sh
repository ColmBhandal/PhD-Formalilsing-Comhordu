#!/bin/bash
# Gives a Claude Code cloud session the Rocq 9.2.0 toolchain before it starts.
#
# Cloud sessions have no Docker daemon and can't reach opam's repository, so
# helper-scripts/install_rocq.sh fetches the CI image's Rocq straight from Docker Hub. It does
# nothing when Rocq is already there, which it is once the environment has been cached. The
# hook then puts Rocq on the PATH for the session. On a developer machine it does nothing; see
# README.md for the other ways to install Rocq.
set -uo pipefail

if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

if "$CLAUDE_PROJECT_DIR/helper-scripts/install_rocq.sh"; then
  echo 'export PATH="/home/rocq/.opam/4.14.2+flambda/bin:$PATH"' >> "$CLAUDE_ENV_FILE"
else
  echo "install_rocq.sh failed: Rocq isn't installed. See helper-scripts/README.md." >&2
fi
exit 0
