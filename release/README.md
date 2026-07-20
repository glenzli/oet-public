# OET Public Release Workflow

This repository owns public commits, public tags, Sigstore release witnesses,
and GitLab/GitHub Releases. The private authoring repository only produces a
validated release handoff.

## Local configuration

Local paths are never committed or hardcoded. Configure the private repository
location in this clone:

```bash
git config --local oet.privateRepo /absolute/path/to/formal-math
git config --local oet.sigstoreIdentity name@example.com
git config --local oet.sigstoreIssuer https://accounts.google.com
git config --local oet.gitlabRemote origin
```

The import command also accepts `--from /any/path/to/handoff`, so the handoff
may be moved, renamed, or copied from another machine. Command-line arguments
override environment variables, which override local Git configuration.

When GitHub publication becomes available, configure its public remote:

```bash
git remote add github git@github.com:OWNER/oet-public.git
git config --local oet.githubRemote github
git config --local oet.githubProject OWNER/oet-public
```

## Per-release procedure

After the private repository has created its signed source tag and prepared a
handoff with a reserved Zenodo version DOI:

```bash
scripts/release/oet-release-import.sh --tag oet-vols-01-rc.1
```

Review the imported public tree, then commit and tag it locally:

```bash
scripts/release/oet-release-tag.sh --tag oet-vols-01-rc.1
```

Create the public-source archive and final manifest:

```bash
scripts/release/oet-release-finalize.sh --tag oet-vols-01-rc.1
```

Sign the manifest. Cosign prints a URL; keep the command running and complete
Google login in a browser:

```bash
scripts/release/oet-release-sign.sh --tag oet-vols-01-rc.1
```

Upload the frozen files under `release/cache/<tag>/public-release/` to the
Zenodo draft. After final review, publish the Zenodo record, then push the
public source and create the GitLab Release:

```bash
scripts/release/oet-release-publish-gitlab.sh --tag oet-vols-01-rc.1
```

Verify the DOI and GitLab downloads against `SHA256SUMS.txt`. GitHub can later
receive the same tag and byte-identical assets without rebuilding:

```bash
scripts/release/oet-release-publish-github.sh --tag oet-vols-01-rc.1
```

If the local cache has been removed, download the exact Zenodo asset set and
pass its directory explicitly:

```bash
scripts/release/oet-release-publish-github.sh \
  --tag oet-vols-01-rc.1 \
  --assets-dir /path/to/downloaded/zenodo-assets
```

The PDF and release citation files contain the version DOI. The concept DOI is
maintained on the OET work page and public repository entry points, not inside
version-specific PDF files.

After the first Zenodo publication, record its concept DOI on the public main
branch without moving the published tag:

```bash
scripts/release/oet-release-record-concept-doi.sh \
  --doi 10.5281/zenodo.xxxxxxx
```

Commit `release/concept-doi.txt` and the updated `README.md`. Later release
imports preserve this file and add the all-versions DOI to generated README
snapshots automatically.
