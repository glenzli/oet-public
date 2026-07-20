#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=lib.sh
source "$script_dir/lib.sh"

usage() {
  cat <<'USAGE'
Usage:
  oet-release-tag.sh --tag TAG

Commits the imported public snapshot and creates a signed local public tag.
Nothing is pushed and no platform Release is created.
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
cache="$(oet_cache_dir "$root" "$tag")"
metadata="$cache/handoff-metadata.json"
[[ -f "$metadata" ]] || oet_die "Missing imported handoff metadata: $metadata"
[[ "$(oet_json_value "$metadata" release_tag)" == "$tag" ]] || oet_die "Handoff tag mismatch"
if git -C "$root" rev-parse --verify --quiet "refs/tags/$tag" >/dev/null; then
  oet_die "Public tag already exists: $tag"
fi
if [[ -z "$(git -C "$root" status --porcelain)" ]]; then
  oet_die "No imported public changes are available to commit."
fi

git -C "$root" add -A
git -C "$root" commit -S -m "Publish $tag public snapshot"
git -C "$root" tag -s "$tag" -m "OET public release $tag"

public_commit="$(git -C "$root" rev-parse "$tag^{commit}")"
python3 - "$cache/public-metadata.json" "$tag" "$public_commit" <<'PY'
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
payload = {
    "schema": "oet-public-release/v1",
    "release_tag": sys.argv[2],
    "public_commit": sys.argv[3],
}
path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
PY

echo "Created signed public tag $tag at $public_commit"
echo "Nothing has been pushed. Finalize the release witness next:"
echo "scripts/release/oet-release-finalize.sh --tag $tag"
