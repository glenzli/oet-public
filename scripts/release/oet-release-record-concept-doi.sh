#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=lib.sh
source "$script_dir/lib.sh"

usage() {
  cat <<'USAGE'
Usage:
  oet-release-record-concept-doi.sh --doi 10.5281/zenodo.xxxxxxx

Records the Zenodo concept DOI after the first publication and updates the
public README. Commit this as a post-release main-branch change; do not move the
already published release tag.
USAGE
}

root="$(oet_repo_root)"
doi=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --doi) doi="${2:-}"; shift 2 ;;
    --doi=*) doi="${1#--doi=}"; shift ;;
    -h|--help) usage; exit 0 ;;
    *) usage >&2; exit 2 ;;
  esac
done

doi="${doi#https://doi.org/}"
doi_pattern='^10\.[0-9]{4,9}/[-._;()/:A-Za-z0-9]+$'
[[ "$doi" =~ $doi_pattern ]] || oet_die "Invalid concept DOI: $doi"
mkdir -p "$root/release"
printf '%s\n' "$doi" > "$root/release/concept-doi.txt"
oet_apply_concept_doi "$root"

echo "Recorded concept DOI: $doi"
echo "Review and commit the README and release/concept-doi.txt on the public main branch."
