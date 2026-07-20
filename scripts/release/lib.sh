#!/usr/bin/env bash

oet_die() {
  echo "$*" >&2
  exit 1
}

oet_repo_root() {
  local lib_dir
  lib_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  git -C "$lib_dir/../.." rev-parse --show-toplevel 2>/dev/null || oet_die "Cannot locate the oet-public repository."
}

oet_require_tag() {
  local tag="$1"
  if [[ ! "$tag" =~ ^oet-vols-01(-([0-9]{2}))?-(rc\.[0-9]+|v[0-9]+\.[0-9]+\.[0-9]+)$ ]]; then
    oet_die "Invalid OET release tag: $tag"
  fi
}

oet_json_value() {
  local path="$1"
  local key="$2"
  python3 - "$path" "$key" <<'PY'
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
key = sys.argv[2]
try:
    value = json.loads(path.read_text(encoding="utf-8"))[key]
except (FileNotFoundError, KeyError, json.JSONDecodeError) as exc:
    print(f"Cannot read {key!r} from {path}: {exc}", file=sys.stderr)
    raise SystemExit(1)
print(value)
PY
}

oet_env_value() {
  local path="$1"
  local key="$2"
  python3 - "$path" "$key" <<'PY'
import pathlib
import shlex
import sys

path = pathlib.Path(sys.argv[1])
key = sys.argv[2]
try:
    lines = path.read_text(encoding="utf-8").splitlines()
except FileNotFoundError as exc:
    print(exc, file=sys.stderr)
    raise SystemExit(1)
for line in lines:
    if not line.startswith(key + "="):
        continue
    value = line.split("=", 1)[1]
    parsed = shlex.split(value)
    print(parsed[0] if parsed else "")
    break
else:
    print(f"Missing {key} in {path}", file=sys.stderr)
    raise SystemExit(1)
PY
}

oet_config() {
  local key="$1"
  local env_name="$2"
  local fallback="${3:-}"
  local root
  local value="${!env_name:-}"
  root="$(oet_repo_root)"
  if [[ -z "$value" ]]; then
    value="$(git -C "$root" config --local --get "$key" 2>/dev/null || true)"
  fi
  printf '%s' "${value:-$fallback}"
}

oet_cache_dir() {
  local root="$1"
  local tag="$2"
  printf '%s/release/cache/%s' "$root" "$tag"
}

oet_require_release_files() {
  local assets="$1"
  [[ -d "$assets" ]] || oet_die "Missing release assets: $assets"
  [[ -f "$assets/RELEASE-MANIFEST.txt" ]] || oet_die "Missing RELEASE-MANIFEST.txt"
  [[ -f "$assets/RELEASE-MANIFEST.sigstore.json" ]] || oet_die "Missing RELEASE-MANIFEST.sigstore.json"
  [[ -f "$assets/SHA256SUMS.txt" ]] || oet_die "Missing SHA256SUMS.txt"
  [[ -f "$assets/RELEASE-NOTES.md" ]] || oet_die "Missing RELEASE-NOTES.md"
}

oet_verify_release() {
  local root="$1"
  local assets="$2"
  local identity issuer

  oet_require_release_files "$assets"
  identity="$(oet_config oet.sigstoreIdentity OET_SIGSTORE_IDENTITY)"
  issuer="$(oet_config oet.sigstoreIssuer OET_SIGSTORE_ISSUER https://accounts.google.com)"
  [[ -n "$identity" ]] || oet_die "Configure the expected signer with: git config --local oet.sigstoreIdentity <email>"

  python3 - "$assets" <<'PY'
import pathlib
import sys

assets = pathlib.Path(sys.argv[1]).resolve()
listed = set()
for line in (assets / "SHA256SUMS.txt").read_text(encoding="utf-8").splitlines():
    _, rel = line.split("  ", 1)
    listed.add(rel)
actual = {
    path.relative_to(assets).as_posix()
    for path in assets.rglob("*")
    if path.is_file() and path.relative_to(assets).as_posix() != "SHA256SUMS.txt"
}
if listed != actual:
    print("SHA256SUMS.txt does not describe the exact release asset set.", file=sys.stderr)
    print(f"Missing from checksum: {sorted(actual - listed)}", file=sys.stderr)
    print(f"Missing from directory: {sorted(listed - actual)}", file=sys.stderr)
    raise SystemExit(1)
PY
  (cd "$assets" && shasum -a 256 -c SHA256SUMS.txt)
  cosign verify-blob \
    "$assets/RELEASE-MANIFEST.txt" \
    --bundle "$assets/RELEASE-MANIFEST.sigstore.json" \
    --certificate-identity "$identity" \
    --certificate-oidc-issuer "$issuer"
}

oet_verify_tag_binding() {
  local root="$1"
  local assets="$2"
  local tag="$3"
  local public_commit

  git -C "$root" rev-parse --verify --quiet "refs/tags/$tag^{commit}" >/dev/null || oet_die "Missing public tag: $tag"
  git -C "$root" verify-tag "$tag" >/dev/null 2>&1 || oet_die "Public tag signature verification failed: $tag"
  public_commit="$(git -C "$root" rev-parse "$tag^{commit}")"
  grep -Fqx "# Release tag: $tag" "$assets/RELEASE-MANIFEST.txt" || oet_die "Release manifest tag mismatch"
  grep -Fqx "# Public repository commit: $public_commit" "$assets/RELEASE-MANIFEST.txt" || oet_die "Release manifest public commit mismatch"
}

oet_apply_concept_doi() {
  local root="$1"
  local concept_file="$root/release/concept-doi.txt"
  local readme="$root/README.md"
  [[ -f "$concept_file" && -f "$readme" ]] || return 0
  python3 - "$readme" "$concept_file" <<'PY'
import pathlib
import re
import sys

readme = pathlib.Path(sys.argv[1])
concept_file = pathlib.Path(sys.argv[2])
doi = concept_file.read_text(encoding="utf-8").strip()
if not doi:
    raise SystemExit("Empty concept DOI")
text = readme.read_text(encoding="utf-8")
text = re.sub(
    r"\n?<!-- OET-CONCEPT-DOI:START -->.*?<!-- OET-CONCEPT-DOI:END -->\n?",
    "\n",
    text,
    flags=re.S,
).rstrip()
block = (
    "\n\n<!-- OET-CONCEPT-DOI:START -->\n"
    f"- All versions DOI: [https://doi.org/{doi}](https://doi.org/{doi})\n"
    "<!-- OET-CONCEPT-DOI:END -->\n"
)
readme.write_text(text + block, encoding="utf-8")
PY
}
