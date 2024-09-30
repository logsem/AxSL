#!/bin/bash
# based on a script from the RefinedC project:
# https://gitlab.mpi-sws.org/iris/refinedc/-/blob/master/tools/coqc_timing.sh?ref_type=heads

set -e

# Wrapper for coqc that is used when running the perf script in the CI.
# Variable TIMECMD is expected to contain an absolute path to the perf script.
# If TIMECMD is not set (or empty), fallback to just calling coqc.
# we need to use opam exec -- coqc to get the coqc installed by opam, not this script
# If PROFILE is set, generate a profile in the $PROFILE file (relative to the root of the repo).

## use time if available
if env time echo >/dev/null 2>/dev/null; then
   export TIMECMD="time"
fi

# This file is in "_build/default/tools"
REPO_DIR="$(dirname $(readlink -f $0))/../../"

opam exec -- ${TIMECMD} coqc "$@"
