# Source attribution and publication scope

The original OpenAI Lean development is from https://github.com/openai/math,
commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Its Apache-2.0 license is
retained in licenses/LICENSE.OpenAI-Lean and formalization/OAI/LICENSE.
The vendored OAI modules are exact Git blobs from that commit. Dependency
compatibility patches are also copied from that pinned upstream release.

ZetaZeroFree is an adapted development prepared for the user's project with
OpenAI Codex. In particular, Moments/Unconditional.lean reorganizes and adapts
upstream intermediate proofs into a new namespace. It replaces the
beta-dependent prime input with a genuine contour-at-one estimate and carries
the finite descent to an unconditional endpoint. Per-declaration source
contexts and changes are in evidence/current-provenance.json. The local
source files are preserved exactly as verified; this notice accompanies them.
The upstream terminal 7/8 theorem is not a proof dependency of the new result.

The manuscript is by Hailey Collet (HaileyCollet@gmail.com), developed with
assistance from OpenAI's GPT-6 Pro. Hailey explicitly confirmed this authorship
and requested publication of the Markdown, TeX and rendered PDF. The published
revision adds the author, contact address and assistance credit; the mathematical
text is unchanged. The original supplied-document hashes are retained in
evidence/current-provenance.json and manuscript/rendered-documents.json.

The two predecessor PDFs are included only in the separate reviewer-materials
directory of the outer ZIP, not in this proof overlay. The retained upstream
license does not assign a new license to these manuscripts.

Other packages are fetched at the supplied lockfile pins. Their own licenses
remain in their source repositories; their sources and binaries are not
redistributed here. This package contains no formal registration, maintainer
approval, signed verification receipt or claim to a new numerical record.
