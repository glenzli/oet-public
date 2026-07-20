#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=lib.sh
source "$script_dir/lib.sh"

usage() {
  cat <<'USAGE'
Usage:
  oet-release-finalize.sh --tag TAG

Creates the immutable public-source archive and RELEASE-MANIFEST.txt after the
public tag has been fixed. It does not sign, checksum, push, or upload.
USAGE
}

root="$(oet_repo_root)"
tag=""
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
git -C "$root" rev-parse --verify --quiet "refs/tags/$tag^{commit}" >/dev/null || oet_die "Missing public tag: $tag"
[[ -z "$(git -C "$root" status --porcelain)" ]] || oet_die "oet-public must be clean before finalizing release assets."

cache="$(oet_cache_dir "$root" "$tag")"
assets="$cache/public-release"
handoff="$cache/handoff-metadata.json"
public_metadata="$cache/public-metadata.json"
[[ -d "$assets" ]] || oet_die "Missing release cache: $assets"
[[ -f "$handoff" ]] || oet_die "Missing handoff metadata"
[[ -f "$public_metadata" ]] || oet_die "Missing public metadata; run oet-release-tag.sh first"

source_commit="$(oet_json_value "$handoff" private_source_commit)"
source_repository="$(oet_json_value "$handoff" private_source_repository)"
doi="$(oet_json_value "$handoff" version_doi)"
public_commit="$(git -C "$root" rev-parse "$tag^{commit}")"
recorded_public_commit="$(oet_json_value "$public_metadata" public_commit)"
[[ "$public_commit" == "$recorded_public_commit" ]] || oet_die "Public tag no longer matches imported release metadata"

rm -f \
  "$assets/RELEASE-MANIFEST.txt" \
  "$assets/RELEASE-MANIFEST.bundle" \
  "$assets/RELEASE-MANIFEST.sigstore.json" \
  "$assets/SHA256SUMS.txt" \
  "$assets/$tag-public-source.tar.gz"

git -C "$root" archive \
  --format=tar.gz \
  --prefix="$tag-public-source/" \
  --output="$assets/$tag-public-source.tar.gz" \
  "$tag"

python3 - "$assets" "$tag" "$source_commit" "$source_repository" "$public_commit" "$doi" <<'PY'
import datetime
import hashlib
import pathlib
import sys

assets = pathlib.Path(sys.argv[1]).resolve()
tag, source_commit, source_repository, public_commit, doi = sys.argv[2:7]
manifest = assets / "RELEASE-MANIFEST.txt"
excluded = {
    "RELEASE-MANIFEST.txt",
    "RELEASE-MANIFEST.bundle",
    "RELEASE-MANIFEST.sigstore.json",
    "SHA256SUMS.txt",
}
files = sorted(
    path for path in assets.rglob("*")
    if path.is_file() and path.relative_to(assets).as_posix() not in excluded
)
if not files:
    raise SystemExit(f"No release assets found in {assets}")

lines = [
    "# OET RELEASE MANIFEST",
    f"# Generated: {datetime.datetime.now(datetime.timezone.utc).isoformat()}",
    f"# Release tag: {tag}",
    f"# Version DOI: {doi}",
    f"# Private source commit: {source_commit}",
    f"# Private source repository: {source_repository}",
    f"# Public repository commit: {public_commit}",
    "# Scope: release assets in this directory, excluding release witness files.",
    "# Hash algorithms: SHA-256, SHA-512, BLAKE2b.",
    "",
]
for path in files:
    data = path.read_bytes()
    rel = path.relative_to(assets).as_posix()
    lines.extend([
        f"## {rel}",
        f"SHA-256:  {hashlib.sha256(data).hexdigest()}",
        f"SHA-512:  {hashlib.sha512(data).hexdigest()}",
        f"BLAKE2b:  {hashlib.blake2b(data).hexdigest()}",
        "",
    ])
manifest.write_text("\n".join(lines), encoding="utf-8")
PY

echo "Final release manifest created: $assets/RELEASE-MANIFEST.txt"
echo "Sign it interactively with:"
echo "scripts/release/oet-release-sign.sh --tag $tag"
