#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=lib.sh
source "$script_dir/lib.sh"

usage() {
  cat <<'USAGE'
Usage:
  oet-release-import.sh --from HANDOFF_DIR [--tag TAG]
  oet-release-import.sh --tag TAG

Path resolution, in order:
  1. --from HANDOFF_DIR
  2. OET_RELEASE_HANDOFF
  3. <oet.privateRepo>/the-operator-evolution-theory/release/dist/<tag>

Configure a movable local private repository path with:
  git config --local oet.privateRepo /absolute/path/to/formal-math
USAGE
}

root="$(oet_repo_root)"
from=""
tag=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --from)
      from="${2:-}"
      shift 2
      ;;
    --from=*)
      from="${1#--from=}"
      shift
      ;;
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

if [[ -z "$from" ]]; then
  from="${OET_RELEASE_HANDOFF:-}"
fi
if [[ -z "$from" && -n "$tag" ]]; then
  private_repo="$(oet_config oet.privateRepo OET_PRIVATE_REPO)"
  if [[ -n "$private_repo" ]]; then
    from="$private_repo/the-operator-evolution-theory/release/dist/$tag"
  fi
fi
if [[ -z "$from" ]]; then
  usage >&2
  exit 2
fi

from="$(cd "$from" 2>/dev/null && pwd)" || oet_die "Handoff directory does not exist: $from"
metadata="$from/handoff-metadata.json"
[[ -f "$metadata" ]] || oet_die "Missing handoff metadata: $metadata"
[[ "$(oet_json_value "$metadata" schema)" == "oet-release-handoff/v1" ]] || oet_die "Unsupported handoff metadata schema"
handoff_tag="$(oet_json_value "$metadata" release_tag)"
if [[ -n "$tag" && "$tag" != "$handoff_tag" ]]; then
  oet_die "Requested tag $tag does not match handoff tag $handoff_tag"
fi
tag="$handoff_tag"
oet_require_tag "$tag"

[[ -d "$from/public-repo" ]] || oet_die "Missing public-repo/ in handoff"
[[ -d "$from/public-release" ]] || oet_die "Missing public-release/ in handoff"
release_env="$from/public-release/release-metadata.env"
[[ -f "$release_env" ]] || oet_die "Missing release metadata: $release_env"
[[ "$(oet_env_value "$release_env" OET_RELEASE_TAG)" == "$tag" ]] || oet_die "Release metadata tag mismatch"
[[ "$(oet_env_value "$release_env" OET_DOI)" == "$(oet_json_value "$metadata" version_doi)" ]] || oet_die "Release metadata DOI mismatch"
[[ "$(oet_env_value "$release_env" OET_GIT_COMMIT)" == "$(oet_json_value "$metadata" private_source_commit)" ]] || oet_die "Release metadata private commit mismatch"
if git -C "$root" rev-parse --verify --quiet HEAD >/dev/null; then
  if [[ -n "$(git -C "$root" status --porcelain)" ]]; then
    oet_die "oet-public must be clean before importing a release handoff."
  fi
else
  echo "Bootstrapping the first public commit from an empty repository."
fi
if git -C "$root" rev-parse --verify --quiet "refs/tags/$tag" >/dev/null; then
  oet_die "Public tag already exists: $tag"
fi

generated_root_files=(
  AI-PARTICIPATION-SUMMARY.md
  AI-PARTICIPATION.md
  AI_ATTRIBUTION_NOTICE.md
  AI_ATTRIBUTION_NOTICE.zh-CN.md
  CITATION.cff
  CITATION.md
  CITATION.zh-CN.md
  LICENSE
  LICENSE.zh-CN.md
  NOTICE.md
  NOTICE.zh-CN.md
  README.md
)
for name in "${generated_root_files[@]}"; do
  if [[ -f "$from/public-repo/$name" ]]; then
    cp "$from/public-repo/$name" "$root/$name"
  else
    rm -f "$root/$name"
  fi
done
oet_apply_concept_doi "$root"

mkdir -p "$root/the-operator-evolution-theory"
rsync -a --delete \
  "$from/public-repo/the-operator-evolution-theory/" \
  "$root/the-operator-evolution-theory/"

cache="$(oet_cache_dir "$root" "$tag")"
[[ ! -e "$cache" ]] || oet_die "Release cache already exists: $cache"
mkdir -p "$cache/public-release"
rsync -a "$from/public-release/" "$cache/public-release/"
cp "$metadata" "$cache/handoff-metadata.json"
rm -f \
  "$cache/public-release/RELEASE-MANIFEST.txt" \
  "$cache/public-release/RELEASE-MANIFEST.bundle" \
  "$cache/public-release/RELEASE-MANIFEST.sigstore.json" \
  "$cache/public-release/SHA256SUMS.txt"

echo "Imported OET release handoff: $tag"
echo "Public tree: $root"
echo "Release cache: $cache"
echo
echo "Review the public diff, then run:"
echo "scripts/release/oet-release-tag.sh --tag $tag"
