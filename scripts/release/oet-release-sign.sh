#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=lib.sh
source "$script_dir/lib.sh"

usage() {
  cat <<'USAGE'
Usage:
  oet-release-sign.sh --tag TAG [--identity EMAIL]

Signs RELEASE-MANIFEST.txt with Sigstore keyless device flow. Cosign prints a
URL; keep the command running and complete Google login in a browser.
USAGE
}

root="$(oet_repo_root)"
tag=""
identity=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --tag)
      tag="${2:-}"
      shift 2
      ;;
    --tag=*)
      tag="${1#--tag=}"
      shift
      ;;
    --identity)
      identity="${2:-}"
      shift 2
      ;;
    --identity=*)
      identity="${1#--identity=}"
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      usage >&2
      exit 2
      ;;
  esac
done

[[ -n "$tag" ]] || { usage >&2; exit 2; }
oet_require_tag "$tag"
identity="${identity:-$(oet_config oet.sigstoreIdentity OET_SIGSTORE_IDENTITY)}"
issuer="$(oet_config oet.sigstoreIssuer OET_SIGSTORE_ISSUER https://accounts.google.com)"
[[ -n "$identity" ]] || oet_die "Configure the signer with: git config --local oet.sigstoreIdentity <email>"
command -v cosign >/dev/null 2>&1 || oet_die "cosign is required"

assets="$(oet_cache_dir "$root" "$tag")/public-release"
manifest="$assets/RELEASE-MANIFEST.txt"
bundle="$assets/RELEASE-MANIFEST.sigstore.json"
checksums="$assets/SHA256SUMS.txt"
[[ -f "$manifest" ]] || oet_die "Missing finalized manifest: $manifest"
[[ ! -e "$bundle" && ! -e "$checksums" ]] || oet_die "Release is already signed or checksummed; finalize again only before publication."

echo "Cosign will print a browser URL. Open it and complete Google login as: $identity"
cosign --timeout 10m sign-blob \
  --yes \
  --fulcio-auth-flow=device \
  --bundle "$bundle" \
  "$manifest"

cosign verify-blob \
  "$manifest" \
  --bundle "$bundle" \
  --certificate-identity "$identity" \
  --certificate-oidc-issuer "$issuer"

python3 - "$assets" "$checksums" <<'PY'
import hashlib
import pathlib
import sys

assets = pathlib.Path(sys.argv[1]).resolve()
checksums = pathlib.Path(sys.argv[2])
files = sorted(
    path for path in assets.rglob("*")
    if path.is_file() and path.relative_to(assets).as_posix() != "SHA256SUMS.txt"
)
checksums.write_text(
    "\n".join(
        f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.relative_to(assets).as_posix()}"
        for path in files
    ) + "\n",
    encoding="utf-8",
)
PY

(cd "$assets" && shasum -a 256 -c SHA256SUMS.txt)
echo "Signed and checksummed release assets: $assets"
