#!/bin/bash
# Move challenge_02/library into its own repository (osick/eqtheory),
# keeping the library's commit history. Run from the SAIR-callenges root
# after the library commit has been made.
#
#   scripts/export_to_repo.sh /path/to/new/clone-of-eqtheory
#
# Steps performed:
#   1. `git subtree split` extracts the history of challenge_02/library
#      into a branch `eqtheory-export` (paths rewritten to the root).
#   2. That branch is pulled into the target clone's `main`.
# Afterwards, in the target clone: review, `git push -u origin main`,
# then tag the first release (docs/releasing.md).
set -euo pipefail
target=${1:?target clone directory}
src=$(git rev-parse --show-toplevel)
cd "$src"
git subtree split --prefix=challenge_02/library -b eqtheory-export
cd "$target"
git pull --allow-unrelated-histories "$src" eqtheory-export
echo "history imported into $target — review with 'git log --stat', then push and tag"
