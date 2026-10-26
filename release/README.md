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

Review the imported public tree and build its exported Lean project. Commit the
reviewed snapshot through the managed direct-commit workflow with Git signing
enabled, then create its signed local tag:

```bash
scripts/release/oet-release-tag.sh --tag oet-vols-01-rc.1 --commit HEAD
```

The tag command never stages or commits files. It requires a clean working tree
and a verifiable signed commit at HEAD. Pass the managed commit hash instead of
`HEAD` to bind the operation to that exact reviewed snapshot. Existing tags are
never replaced.

Create the public-source archive and final manifest:

```bash
scripts/release/oet-release-finalize.sh --tag oet-vols-01-rc.1
```

Sign the manifest. By default Cosign uses browser login with a local callback;
keep the command running and complete Google login in the browser:

```bash
scripts/release/oet-release-sign.sh --tag oet-vols-01-rc.1
```

If the local callback is unavailable, explicitly select `--auth-flow device`.
The same setting can be supplied through `OET_SIGSTORE_AUTH_FLOW` or
`git config --local oet.sigstoreAuthFlow normal`. The signer identity and issuer
are verified regardless of the authentication flow.

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
