#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=lib.sh
source "$script_dir/lib.sh"

usage() {
  cat <<'USAGE'
Usage:
  oet-release-publish-github.sh --tag TAG [--assets-dir DIR] [--remote NAME] [--repo OWNER/REPO] [--dry-run]

Mirrors the already frozen public tag and assets to GitHub. It can be run long
after GitLab/Zenodo publication and never rebuilds release files.
USAGE
}

root="$(oet_repo_root)"
tag=""
remote=""
project=""
assets_override=""
dry_run=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --tag) tag="${2:-}"; shift 2 ;;
    --tag=*) tag="${1#--tag=}"; shift ;;
    --remote) remote="${2:-}"; shift 2 ;;
    --remote=*) remote="${1#--remote=}"; shift ;;
    --repo) project="${2:-}"; shift 2 ;;
    --repo=*) project="${1#--repo=}"; shift ;;
    --assets-dir) assets_override="${2:-}"; shift 2 ;;
    --assets-dir=*) assets_override="${1#--assets-dir=}"; shift ;;
    --dry-run) dry_run=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) usage >&2; exit 2 ;;
  esac
done

[[ -n "$tag" ]] || { usage >&2; exit 2; }
oet_require_tag "$tag"
remote="${remote:-$(oet_config oet.githubRemote OET_GITHUB_REMOTE github)}"
project="${project:-$(oet_config oet.githubProject OET_GITHUB_PROJECT)}"
assets="${assets_override:-$(oet_cache_dir "$root" "$tag")/public-release}"
assets="$(cd "$assets" 2>/dev/null && pwd)" || oet_die "Release asset directory does not exist: $assets"
oet_verify_release "$root" "$assets"
oet_verify_tag_binding "$root" "$assets" "$tag"
[[ -z "$(git -C "$root" status --porcelain)" ]] || oet_die "oet-public must be clean before publication."
command -v gh >/dev/null 2>&1 || oet_die "gh is required"

branch="$(git -C "$root" branch --show-current)"
if [[ "$dry_run" -eq 1 ]]; then
  echo "+ git push $remote $branch refs/tags/$tag"
  echo "+ gh release create $tag <frozen assets> --notes-file RELEASE-NOTES.md"
  exit 0
fi

git -C "$root" push "$remote" "$branch" "refs/tags/$tag"
release_args=(release create "$tag" --title "$tag" --notes-file "$assets/RELEASE-NOTES.md")
if [[ "$tag" == *-rc.* ]]; then
  release_args+=(--prerelease)
fi
if [[ -n "$project" ]]; then
  release_args+=(--repo "$project")
fi
while IFS= read -r -d '' path; do
  release_args+=("$path")
done < <(find "$assets" -type f -print0)
gh "${release_args[@]}"

echo "GitHub release published: $tag"
