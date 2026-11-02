#!/usr/bin/env bash
# Builds fast_abbrev_printing before a release (SKILL isabelle-patch-feature, 3.4 step 4): the
# sessions of tools/required_sessions.txt, with -d for the shared golden harness and the tests.
# Run in the package directory fast_abbrev_printing/, with ISABELLE set to the isabelle to build
# with; extra arguments go to build.
set -euo pipefail
"$ISABELLE" build -b "$@" -d ../golden -d tests $(grep -v '^[[:space:]]*#' tools/required_sessions.txt)
