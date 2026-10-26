"""Isolated release-boundary tests; signing and remote services are simulated."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


SOURCE = Path(__file__).resolve().parents[1]
REAL_GIT = shutil.which("git")
TAG = "oet-vols-01-v1.0.0"


class ReleaseToolsTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="oet-release-tools-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.scripts = self.root / "scripts/release"
        self.scripts.mkdir(parents=True)
        for name in ("lib.sh", "oet-release-tag.sh", "oet-release-sign.sh"):
            shutil.copy2(SOURCE / name, self.scripts / name)
        self.env = {k: v for k, v in os.environ.items() if not k.startswith("OET_")}
        self.env.update(GIT_CONFIG_GLOBAL="/dev/null", GIT_CONFIG_NOSYSTEM="1")
        self.git("init", "-q")
        self.git("config", "user.name", "Release Test")
        self.git("config", "user.email", "release@example.invalid")
        (self.root / ".gitignore").write_text("release/cache/\nbin/\n*.log\n")
        self.git("add", ".")
        self.git("commit", "-qm", "fixture snapshot")
        self.head = self.git("rev-parse", "HEAD").stdout.strip()
        self.assets = self.root / f"release/cache/{TAG}/public-release"
        self.assets.mkdir(parents=True)
        (self.assets.parent / "handoff-metadata.json").write_text(json.dumps({"release_tag": TAG}))
        (self.assets / "RELEASE-MANIFEST.txt").write_text("release manifest fixture\n")
        self.bin = self.root / "bin"
        self.bin.mkdir()
        self.env.update(PATH=str(self.bin) + os.pathsep + self.env["PATH"],
                        REAL_GIT=REAL_GIT, TOOL_LOG=str(self.root / "tools.log"))
        self.executable("git", '''#!/usr/bin/env python3
import json, os, subprocess, sys
args = sys.argv[1:]
with open(os.environ["TOOL_LOG"], "a") as f: f.write(json.dumps(["git"] + args) + "\\n")
command = args[2] if args[:1] == ["-C"] else args[0]
if command == "verify-commit" and os.environ.get("SIMULATE_SIGNED_COMMIT") == "1":
    sys.exit(0)
if command == "tag" and "-s" in args:
    args[args.index("-s")] = "-a"  # No real signing in tests.
sys.exit(subprocess.call([os.environ["REAL_GIT"]] + args))
''')
        self.executable("cosign", '''#!/usr/bin/env python3
import json, os, pathlib, sys
args = sys.argv[1:]
with open(os.environ["TOOL_LOG"], "a") as f: f.write(json.dumps(["cosign"] + args) + "\\n")
if "sign-blob" in args:
    pathlib.Path(args[args.index("--bundle") + 1]).write_text('{"test_fixture":true}\\n')
if "verify-blob" in args and os.environ.get("SIMULATE_VERIFY_FAILURE") == "1":
    sys.exit(1)
''')
        self.env["OET_SIGSTORE_IDENTITY"] = "release@example.invalid"

    def git(self, *args):
        return subprocess.run([REAL_GIT, "-C", str(self.root), *args], env=self.env,
                              text=True, capture_output=True, check=True)

    def executable(self, name, source):
        path = self.bin / name
        path.write_text(source)
        path.chmod(0o755)

    def run_tool(self, name, *args):
        return subprocess.run(["bash", str(self.scripts / name), "--tag", TAG, *args],
                              cwd=self.root, env=self.env, text=True, capture_output=True)

    def calls(self):
        path = self.root / "tools.log"
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def assert_no_tag(self):
        self.assertEqual(self.git("tag", "--list").stdout.strip(), "")
        self.assertFalse((self.assets.parent / "public-metadata.json").exists())

    def test_tag_uses_committed_head_without_staging_or_committing(self):
        self.env["SIMULATE_SIGNED_COMMIT"] = "1"
        result = self.run_tool("oet-release-tag.sh", "--commit", self.head)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.git("rev-parse", "HEAD").stdout.strip(), self.head)
        metadata = json.loads((self.assets.parent / "public-metadata.json").read_text())
        self.assertEqual(metadata["public_commit"], self.head)
        self.assertEqual(self.git("rev-parse", TAG + "^{commit}").stdout.strip(), self.head)
        commands = [call[3] for call in self.calls() if call[:2] == ["git", "-C"]]
        self.assertNotIn("add", commands)
        self.assertNotIn("commit", commands)
        self.assertIn("verify-commit", commands)
        self.assertTrue(any("-s" in call and self.head in call for call in self.calls()))

    def test_tag_rejects_uncommitted_changes(self):
        (self.root / "unreviewed.md").write_text("uncommitted\n")
        result = self.run_tool("oet-release-tag.sh")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("must be clean", result.stderr)
        self.assert_no_tag()

    def test_tag_rejects_unsigned_commit(self):
        result = self.run_tool("oet-release-tag.sh")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("signature verification failed", result.stderr)
        self.assert_no_tag()

    def test_tag_rejects_commit_other_than_head(self):
        (self.root / "next.md").write_text("next\n")
        self.git("add", "next.md")
        self.git("commit", "-qm", "next snapshot")
        result = self.run_tool("oet-release-tag.sh", "--commit", self.head)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("does not match HEAD", result.stderr)
        self.assert_no_tag()

    def test_existing_tag_is_not_replaced(self):
        self.git("tag", TAG)
        result = self.run_tool("oet-release-tag.sh")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("already exists", result.stderr)
        self.assertEqual(self.git("rev-parse", TAG).stdout.strip(), self.head)

    def test_default_callback_and_exact_verification_precede_checksums(self):
        result = self.run_tool("oet-release-sign.sh")
        self.assertEqual(result.returncode, 0, result.stderr)
        calls = [call for call in self.calls() if call[0] == "cosign"]
        self.assertIn("--fulcio-auth-flow=normal", calls[0])
        self.assertEqual(calls[1][1], "verify-blob")
        self.assertEqual(calls[1][calls[1].index("--certificate-identity") + 1], "release@example.invalid")
        self.assertEqual(calls[1][calls[1].index("--certificate-oidc-issuer") + 1], "https://accounts.google.com")
        for line in (self.assets / "SHA256SUMS.txt").read_text().splitlines():
            digest, name = line.split("  ", 1)
            self.assertEqual(digest, hashlib.sha256((self.assets / name).read_bytes()).hexdigest())

    def test_flow_precedence_cli_over_env_over_config(self):
        self.git("config", "oet.sigstoreAuthFlow", "device")
        self.env["OET_SIGSTORE_AUTH_FLOW"] = "normal"
        result = self.run_tool("oet-release-sign.sh", "--auth-flow=device")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("--fulcio-auth-flow=device", next(c for c in self.calls() if c[0] == "cosign"))

    def test_flow_can_be_selected_from_local_config(self):
        self.git("config", "oet.sigstoreAuthFlow", "device")
        result = self.run_tool("oet-release-sign.sh")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("--fulcio-auth-flow=device", next(c for c in self.calls() if c[0] == "cosign"))

    def test_environment_flow_overrides_local_config(self):
        self.git("config", "oet.sigstoreAuthFlow", "device")
        self.env["OET_SIGSTORE_AUTH_FLOW"] = "normal"
        result = self.run_tool("oet-release-sign.sh")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("--fulcio-auth-flow=normal", next(c for c in self.calls() if c[0] == "cosign"))

    def test_invalid_flow_stops_before_signing(self):
        result = self.run_tool("oet-release-sign.sh", "--auth-flow", "unsupported")
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(any(c[0] == "cosign" for c in self.calls()))
        self.assertFalse((self.assets / "RELEASE-MANIFEST.sigstore.json").exists())

    def test_failed_verification_never_produces_checksums(self):
        self.env["SIMULATE_VERIFY_FAILURE"] = "1"
        result = self.run_tool("oet-release-sign.sh")
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse((self.assets / "SHA256SUMS.txt").exists())


if __name__ == "__main__":
    unittest.main()
