#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <6759885+hyperpolymath@users.noreply.github.com>
#
# Type-check every Idris2 module in the repository.
#
# This script is the single source of truth for "does the Idris2 in this repo
# compile?".  Both CI (.github/workflows/idris2-proof.yml) and the Justfile
# (`just proof-check-idris2`) call it, so a green local run and a green CI run
# mean the same thing.
#
# It exists because four separate holes let non-compiling Idris2 sit in this
# repo for months while every status file recorded it as proved:
#
#   1. The old `just proof-check-idris2` recipe did `exit 0` when idris2 was
#      absent ("SKIP: idris2 not installed").  idris2 was absent, so the recipe
#      was green -- it reported success *because* the tool was missing.
#   2. The old recipe invoked `idris2 --check <full/path/To/Mod.idr>`.  Idris2
#      derives the expected module name from the path it is handed, so every
#      module failed on a name mismatch rather than on its real errors -- and
#      ABI/Foreign.idr, which genuinely compiles, was reported FAIL while the
#      broken ABI/Compliance.idr was reported OK.  Its verdict was inverted on
#      both cases that could discriminate.
#   3. The CI gate installed idris2 correctly but was path-filtered to
#      a-sounder-constitution/formal/ alone.  research/ and verification/ were
#      never checked by anything.
#   4. `idris2 --check` itself exits 0 on a missing import (see check_module),
#      so even a correct invocation checking the exit code alone is unsound.
#
# They share one shape: a check that cannot fail.  That is not a weak check, it
# is a null check that emits reassuring text -- and every status file downstream
# inherits the false confidence.  If you extend this script, the test to apply
# is not "does it pass?" but "have I watched it fail?".
#
# Three rules follow, and they are the point of this file:
#
#   * A missing toolchain is a FAILURE, never a skip.  "I could not check this"
#     must never render as "this is fine".
#   * Every module is checked from its own source root (see MANIFEST).
#   * A module that is not in the MANIFEST is an error.  New Idris2 anywhere in
#     the tree is gated by default; you cannot add an unchecked proof.
#
# Exit codes: 0 = all gated modules check and all quarantined modules still
# fail as expected; 1 = otherwise.

set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
ROOT="$PWD"

# --- MANIFEST -----------------------------------------------------------------
# Format: <source-root>|<module-path-relative-to-root>|<gated|quarantine>|<note>
#
# source-root is the directory Idris2 must be invoked from, chosen so that the
# module's declared name matches its path (module ABI.Foreign lives at
# <root>/ABI/Foreign.idr).  Getting this wrong is hole #2 above.
#
# gated      -- must type-check.  A failure fails this script and CI.
# quarantine -- known-broken, tracked in STATE.a2ml.  Must CONTINUE to fail; if
#               one starts passing the script fails and tells you to promote it,
#               so the list cannot silently rot into a permanent excuse.
MANIFEST=(
  "a-sounder-constitution/formal|Constitution.idr|gated|constitutional certificate; the original #45 gate"
  "research/level-candidates/L11-modal-box|Modal.idr|gated|L11 sketch; compiles only since the %hide Prelude.dup fix"
  "research/level-candidates/L11-modal-box|DupForcesOmega.idr|gated|machine-checks that ungraded dup pins r = omega"
  "research/tropical|TropicalKleene.idr|quarantine|costMatAddZeroL uses 'rewrite h' with no 'in', then 'exact', which is not Idris2 syntax at all -- Idris1/tactic-era code that has never compiled"
  "src/interface|Abi/Types.idr|gated|ABI interface"
  "src/interface|Abi/Layout.idr|gated|ABI interface"
  "src/interface|Abi/Foreign.idr|gated|ABI interface"
  "verification/proofs/idris2|ABI/Foreign.idr|gated|the one verification/ module that compiles; real content, not a stub"
  "verification/proofs/idris2|Types.idr|quarantine|Idris1-era template, never compiled. LTE needs Data.Nat, but that only unmasks the real bug: {auto 0 inBounds} is erased yet projected into a value position. Not a one-line fix"
  "verification/proofs/idris2|ABI/Platform.idr|quarantine|LTE needs Data.Nat; then Undefined name lteRefl"
  "verification/proofs/idris2|ABI/Layout.idr|quarantine|NonZero/modNatNZ need Data.Nat; then a genuine unification failure (S ?x vs f .fieldAlignment)"
  "verification/proofs/idris2|ABI/Pointers.idr|quarantine|.nonNull declared at quantity 0 (erased) yet projected into a value position, plus a unification failure. Design decision needed, not a typo"
  "verification/proofs/idris2|ABI/Compliance.idr|quarantine|depends on quarantined ABI.Layout / ABI.Platform"
)

# --- toolchain: absent means FAIL, never skip ---------------------------------
if ! command -v idris2 >/dev/null 2>&1; then
  cat >&2 <<'EOF'
FAIL: idris2 not found on PATH.

This is deliberately fatal.  The previous version of this check did `exit 0`
here with "SKIP: idris2 not installed", which meant every proof in this repo
reported green on machines where nothing could check them.  An unrunnable gate
that reports success is worse than no gate: it manufactures false confidence.

Install Idris2 0.7.0, or run this in CI where the workflow installs it.
EOF
  exit 1
fi

echo "=== Idris2 proof check ==="
idris2 --version
echo

# --- verdict ------------------------------------------------------------------
# `idris2 --check` EXITS 0 ON A MISSING IMPORT while printing "Error: Module X
# not found" (verified against Idris2 0.7.0: type errors, parse errors and
# module-name mismatches all exit 1, but a missing import exits 0).  Testing $?
# alone is therefore unsound -- it silently passes a module whose imports do not
# resolve.  We require BOTH a zero exit AND no "Error:" in the output.
check_module() {
  local root="$1" rel="$2" out rc
  set +e
  out="$(cd "$ROOT/$root" && idris2 --check "$rel" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -eq 0 ] && ! grep -q '^Error:' <<<"$out"; then
    LAST_OUT=""
    return 0
  fi
  LAST_OUT="$out"
  return 1
}

fails=0
unexpected_pass=0

for entry in "${MANIFEST[@]}"; do
  IFS='|' read -r root rel status note <<<"$entry"
  printf '  %-28s %-22s ' "$root" "$rel"

  if check_module "$root" "$rel"; then
    if [ "$status" = "gated" ]; then
      echo "PASS"
    else
      echo "PASS -- UNEXPECTED"
      echo "      This module is marked 'quarantine' but now type-checks."
      echo "      Promote it to 'gated' in the MANIFEST and update STATE.a2ml."
      unexpected_pass=$((unexpected_pass + 1))
    fi
  else
    if [ "$status" = "gated" ]; then
      echo "FAIL"
      printf '%s\n' "${LAST_OUT//$'\n'/$'\n        '}" | sed '1s/^/        /'
      fails=$((fails + 1))
    else
      echo "fail (quarantined, expected)"
      echo "        reason: $note"
    fi
  fi
done

# --- no unlisted Idris2 anywhere in the tree ----------------------------------
# The anti-recurrence rule.  Modal.idr, TropicalKleene.idr and the whole of
# verification/proofs/idris2/ went unchecked for months because nothing forced
# them onto anyone's list.  A module absent from the MANIFEST is an error, so
# new Idris2 is gated by default rather than by remembering.
echo
echo "=== manifest coverage ==="
listed="$(for e in "${MANIFEST[@]}"; do IFS='|' read -r r m _ _ <<<"$e"; echo "$r/$m"; done | sort)"
found="$(find . -name '*.idr' -not -path './.git/*' -not -path '*/build/*' \
          | sed 's|^\./||' | sort)"
unlisted="$(comm -13 <(echo "$listed") <(echo "$found") || true)"
missing="$(comm -23 <(echo "$listed") <(echo "$found") || true)"

if [ -n "$unlisted" ]; then
  echo "FAIL: Idris2 modules present on disk but absent from the MANIFEST:"
  printf '  %s\n' "${unlisted//$'\n'/$'\n  '}"
  echo
  echo "  Every .idr in this repo must be listed in scripts/check-idris2-proofs.sh,"
  echo "  as 'gated' (it must compile) or 'quarantine' (known-broken, tracked)."
  echo "  This rule is why the next Modal.idr cannot go unnoticed for three months."
  fails=$((fails + 1))
fi

if [ -n "$missing" ]; then
  echo "FAIL: MANIFEST lists modules that do not exist (stale entries):"
  printf '  %s\n' "${missing//$'\n'/$'\n  '}"
  fails=$((fails + 1))
fi

[ -z "$unlisted$missing" ] && echo "  all $(echo "$found" | wc -l | tr -d ' ') .idr files accounted for"

echo
if [ "$fails" -gt 0 ] || [ "$unexpected_pass" -gt 0 ]; then
  echo "RESULT: FAIL ($fails failure(s), $unexpected_pass unexpected pass(es))"
  exit 1
fi
echo "RESULT: PASS -- all gated modules type-check; quarantined modules still fail as recorded"
