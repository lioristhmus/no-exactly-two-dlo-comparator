#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" -ne 1 ]]; then
  echo "usage: $0 /absolute/path/to/tools/bin" >&2
  exit 2
fi
if [[ "$(uname -s)" != "Linux" ]]; then
  echo "security-grade Comparator execution requires Linux and real Landrun" >&2
  exit 2
fi
if [[ "$(id -u)" -eq 0 ]]; then
  echo "refusing to run Comparator as root" >&2
  exit 2
fi

tools_bin="$1"
if [[ "$tools_bin" != /* ]]; then
  echo "tools bin directory must be an absolute path" >&2
  exit 2
fi
for executable in comparator lean4export landrun; do
  if [[ ! -x "$tools_bin/$executable" ]]; then
    echo "missing executable: $tools_bin/$executable" >&2
    exit 2
  fi
done
if ! command -v systemd-run >/dev/null 2>&1; then
  echo "systemd-run is required for Comparator's current Landrun guard" >&2
  exit 2
fi
if ! systemctl --user show-environment >/dev/null 2>&1; then
  echo "no usable user systemd manager; see README.md for initialization" >&2
  exit 2
fi
python_bin="$(command -v python3 || true)"
if [[ -z "$python_bin" ]]; then
  echo "python3 is required for the AF_UNIX hardening preflight" >&2
  exit 2
fi

script_dir="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
project_dir="$(CDPATH= cd -- "$script_dir/.." && pwd -P)"
export PATH="$tools_bin:$PATH"

systemd_args=(
  --property=RestrictAddressFamilies=~AF_UNIX
  --user
  --wait
  --collect
  --quiet
)

# First prove that the transient user service can run, then prove that the
# current Comparator hardening really denies creation of AF_UNIX sockets.
systemd-run "${systemd_args[@]}" --pipe -- /usr/bin/true >/dev/null
if ! systemd-run "${systemd_args[@]}" --pipe -- "$python_bin" -c \
    'import errno, socket, sys
inet = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
inet.close()
try:
    socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
except OSError as error:
    if error.errno in {errno.EAFNOSUPPORT, errno.EPERM, errno.EACCES}:
        sys.exit(0)
    raise
sys.exit(1)' >/dev/null; then
  echo "AF_UNIX hardening preflight failed: AF_INET must work and AF_UNIX must be denied" >&2
  exit 1
fi

if [[ -t 0 && -t 1 ]]; then
  systemd_args+=(--pty)
else
  systemd_args+=(--pipe)
fi

systemd-run "${systemd_args[@]}" \
  -E PATH="$PATH" \
  -E HOME="$HOME" \
  -E COMPARATOR_BIN="$tools_bin/comparator" \
  -E COMPARATOR_CONFIG="$project_dir/config.json" \
  --working-directory "$project_dir" \
  -- bash -c 'lake env "$COMPARATOR_BIN" "$COMPARATOR_CONFIG"'
