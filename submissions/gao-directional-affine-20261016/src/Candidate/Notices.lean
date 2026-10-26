/-
Combined detector-affine and asymmetric marked-count research source.

This private integration adapts the detector-affine construction of DaysSky
(PR 56, commit 67edfb7a1161008b37ff32aadec35cecaa711731) to the
asymmetric marked counting and coupled radical allocation of timbalud
(PR 50, commit 8cb265dc; the exact source pin is retained in the build receipt).
The integration and new endpoint selection are by Zhongpai Gao with AI assistance.
No completed endpoint or independent verification is asserted by this notice.

The following predecessor notice is retained verbatim as a historical notice;
its statements about unchanged proof declarations refer to that predecessor's
packaging, not to the present combined source. Original Hailey Collet, OpenAI,
Akash Levy and all other predecessor attributions remain in their modules and
in the retained notices below. DaysSky disclosed Claude assistance.
-/

/-
Attribution and license for detector-affine-c0125154.
Original supporting material: https://github.com/DaysSky/QuasiRiemannTracker/tree/a0efd9ee546b417de650f36bc8403f781706a94e/proofs/detector-affine-c0125154

The import paths use the repository OpenAI baseline. The proof declarations
are unchanged by this layout update. The following texts are retained verbatim.

--- LICENSE ---
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

--- NOTICE.md ---
This submission is a modification of the Cycle61 submission (`cycle61-c0125139`, Copyright 2026 Hailey Collet, Apache-2.0). New material in this submission is offered under Apache-2.0.

Cycle61 itself reuses and adapts Apache-2.0 material from OpenAI/math, Akash Levy's weighted-numerator development, the earlier AI-assisted QRH developments directed by Hailey Collet, and Zhongpai Gao's local refinement. Their notices are retained unchanged under `licenses/`, with Cycle61's own notice and provenance statement (`licenses/cycle61-NOTICE.md`, `licenses/cycle61-PROVENANCE.md`).

Changed Cycle61 bundles keep their original headers and `BEGIN/END ORIGINAL` section markers. PROVENANCE.md lists every changed or added file. All other bundles are byte-identical to `submissions/cycle61-c0125139`.

--- PROVENANCE.md ---
# Authorship and source attribution

**AI disclosure:** DaysSky with Claude assistance. DaysSky directed this work. The mathematical change, the Lean formalization and the exact certificates were developed with Claude assistance. Model review is not independent kernel verification.

## What is reused

Everything comes from the Cycle61 submission [`cycle61-c0125139`](../cycle61-c0125139/README.md) by Hailey Collet, together with the sources that submission credits:

* OpenAI/math;
* Akash Levy's weighted-numerator proof;
* the earlier Cycle25 QRH work;
* Zhongpai Gao's local refinement.

See [`licenses/cycle61-PROVENANCE.md`](licenses/cycle61-PROVENANCE.md). The key ingredient used here is Cycle61's initial affine moment (Theorem 2.2, `Cycle61Moment.InitialAffineAt`) and its generic paid main and error families. This submission applies them to the detector's dictionary characters.

## What is new

New modules under `submissions/detector-affine-c0125154/src/Candidate/Affine/`:

| module | content |
|---|---|
| `Arith.lean` | closed forms for the new count; the combination lemma `affine_count_bound` |
| `Certificates.lean` | exact Bernstein certificates on the region |
| `Region.lean` | region consequences of the certificates; `region_compare` |
| `Mesh.lean` | an early copy of Cycle61's chosen geometry mesh (`detectorMesh`) |
| `Count.lean` | `AffineMarkedMoment`; per-fiber affine count; `count_from_raw_moments_both` |
| `Balanced.lean` | `cutoffA`; balanced count for both the old and the new count |
| `SourceCount.lean` | source count at `cutoffA`; `SourceMomentsAtA` |
| `Moments.lean` | `DetectorAffineInput`; per-character source moments |
| `Masked.lean` | monotonicity of `countingR`; masked amplitude class count |
| `Supply.lean` | proof of `DetectorAffineInput` from Cycle61's generic affine machinery |

Changed Cycle61 bundles in `Bundles/`:

| bundle | change |
|---|---|
| B000 | endpoint constants |
| B003 | `CountParameters.affine` |
| B021 | regenerated row certificates; degree-(2,4) basis |
| B022 | region-aware `countingR` (`countingR0` is the old one); row lemmas |
| B023 | `SourceMomentBound` with the affine field; `t_le`; ε ≤ 1/10000 |
| B024, B025 | per-character heights; `commonMesh` includes `detectorMesh` |
| B043 | per-character finite numerator inputs |
| B060 | recomputed endpoint constants |
| B070 | `countingR0` |
| B074, B075 | batches at `cutoffA`; affine source count |
| B076 | masked count through `masked_amplitude_class_count_A` |
| B078 | per-character fixed numerator; `DetectorAffineInput` threaded through the final theorems |
| B192 | supplies `actual_detector_affine_input` |
| B167, B176 | Split, unchanged, for the tracker's 600-second per-module replay limit:<ul><li>`B167` → `B167Part1`–`4`, one per original source section; section 1 is further split at declaration boundaries into `B167Part1A`–`1D`</li><li>`B176` → `B176Part1`–`4`; section 2 is further split into `B176Part2A`–`2C`</li></ul>Every declaration, statement and proof is Cycle61's, in the original order. The pieces repeat their section's namespace, `open` and `variable` preamble. A section's local instance is declared once and re-enabled with `attribute [local instance]`. `B167.lean`, `B176.lean`, `B167Part1.lean` and `B176Part2.lean` are now thin modules importing their last piece. |
| Main.lean | the bound |

Constants that depend on the endpoint were recomputed by `scripts/patch_consts.py`. `arithmetic/rational-check.py` rechecks them.

--- licenses/akashlevy-NOTICE ---
Akash Levy weighted-numerator quasi-Riemann proof, theta = 10499/12000, 2026-10-09.
Author and human contributor: Akash Levy (GitHub: akashlevy).
GPT-6 Astra (Ultra) was used to discover the proof and perform partial formalization; Opus 5.5 Ultracode was used to complete the formalization and submit the result.

This package is a derivative of the Lean development of OpenAI's "The
Quasi-Riemann Hypothesis" in github.com/openai/math at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0). The proof imports that
development through the fork github.com/akashlevy/math at
c388e88e6519d139ad2ca5571ef0c7fbf0e245b5 (branch qrh-23-24-pruned), which is
openai/math fd4aeeb2e with unused declarations pruned in place plus separate
23/24 modules that this proof does not import, and through
Mathlib at d13f23b723b8a846827a245b89c10fc7d3f11612 (Apache-2.0). The other
pinned dependencies are listed in formalization/lake-manifest.json; the fork's
Lean 4.34.1 compatibility patches for PrimeNumberTheoremAnd
c39a751132c88b6e8080b74c74023fd95b3d8be0 and rellich-kondrachov
70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23 (both Apache-2.0) are applied by
formalization/setup.sh. Apart from the adapted modules and the modified
upstream files noted below, no upstream source is redistributed here; setup.sh
and Lake fetch it at the pinned revisions. The license texts of
openai/math, Mathlib, PrimeNumberTheoremAnd and rellich-kondrachov are
retained in third-party-notices/. UPSTREAM-NOTICE is the tracker's supplied
notice.

New and adapted material: the 228 Lean modules in formalization/WeightedQRH/
(48 of them adaptations of openai/math fd4aeeb2e modules, each marked as
adapted in its header), the Lake workspace files and scripts in
formalization/, the manuscript in manuscript/, the exponent certificate and
the recorded check reports in evidence/. Modified upstream files:
formalization/ComparatorChallenges/WeightedQRHDirichlet.lean and
WeightedQRHHecke.lean are OpenAI's upstream DirichletSevenEighths and
HeckeSevenEighths Comparator challenges (openai/math fd4aeeb2e) with only the
theorem name and the constant changed (WeightedQRHZeta.lean is new), and
evidence/kernels/src/Challenge.lean is the tracker's fixed three-target
template (public/proofs/palomar-20261009/qrh/src/Challenge.lean) with only its
rational literal changed. All of it is licensed under Apache-2.0 (LICENSE);
the adapted and modified files also remain subject to the Apache-2.0 terms
and notices of their sources (third-party-notices/openai-math-LICENSE.txt,
UPSTREAM-NOTICE).

The recorded checks used, without redistributing them, the official Lean
v4.35.0-rc2 release (lake comparator, leanchecker, nanoda_bin, con-ron), Lean
4.34.1, lean4export 076e8e57707e813375e8f9da8bf989799ace9680 and the Lean FRO
Comparator d03acab154d269c06e60e4de7e4cc85deebff94b, under their own licenses.
No upstream author or project, checker project, Palomar, or the tracker's
maintainers is represented as endorsing this result.

--- licenses/cycle25-NOTICE.md ---
# Source notices

Copyright 2026 Hailey Collet. New manuscript and formalization material are
licensed under Apache-2.0. See `LICENSE` and `PROVENANCE.md`.

The vendored `formalization/OAI/` source is the exact import closure from
[OpenAI/math](https://github.com/openai/math) at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. It retains its upstream authorship
and Apache-2.0 license. The source inventory records each included module.
The new proof uses that development's original 7/8 nonvanishing theorem as
a weaker initialization, as well as its analytic and arithmetic foundations.

The `Cycle25` development adapts the numerator inversion, conductor allocation,
coefficient estimates and contour assembly of Akash Levy's
[weighted-numerator proof](https://github.com/akashlevy/QuasiRiemannTracker/tree/2fd60c0926b66ea18d7436f5ed55250fd006ab5d/proofs/akashlevy-20261009-weighted-numerator),
revision `2fd60c0926b66ea18d7436f5ed55250fd006ab5d`, and generalizes the moment,
counting and geometric estimates to the quartic endpoint. That source's
license and notice are retained in `licenses/`; its notice describes the
original upstream package. Its previous final nonvanishing theorem is not
used to establish the new endpoint.

The three `ZetaZeroFree/Analytic/Moments/` modules are reused from Hailey
Collet's [4/33 formalization](https://github.com/GTimG/QuasiRiemannTracker/pull/8).
They reorganize and adapt intermediate OpenAI proofs to establish an
unconditional moving-radical moment. The earlier 4/33 nonvanishing theorem
is not a dependency of this submission.

Mathlib, PrimeNumberTheoremAnd, rellich-kondrachov and the remaining Lake
dependencies retain their own authorship and licenses. Their exact revisions
and the required compatibility patches are recorded with the build recipe.
The patches retain the original licenses; only files needed by this proof's
import closure are included.

Lean, Comparator, NanoDa, con-ron, lean4export and the Palomar verification
helpers are used under their respective licenses. Their binaries are not
redistributed. No upstream project or maintainer endorsement is implied.

--- licenses/cycle61-NOTICE.md ---
Copyright 2026 Hailey Collet. New manuscript and formalization material are licensed under Apache-2.0.

This submission reuses and adapts Apache-2.0 material from OpenAI/math, Akash Levy's weighted-numerator development, the earlier AI-assisted QRH developments directed by Hailey Collet, and Zhongpai Gao's local refinement. See PROVENANCE.md for exact revisions and scope. Original source comments and the notices under licenses/ remain intact.

The candidate modules are a packaging transformation of the frozen used local source closure. They retain the mathematical declaration namespaces. Their import remapping, scope isolation and explicit name qualifications are recorded separately. Their final verification requires the fresh transformed replay described in Verification.md. Unbundled original files remain in original-sources.tar.gz.

--- licenses/cycle61-PROVENANCE.md ---
# Authorship and source attribution

Hailey Collet (HaileyCollet@gmail.com) is the sole human author. The manuscript and new formalization material are offered under Apache-2.0; reused work retains its original authorship, notices and licenses.

I initiated and directed the research program, selected targets and sources, proposed questions and approaches, reconciled assumptions, and decided what to retain and combine. I brought Gao's refinement into the program and asked for its contribution to remain explicit. These are contributions to research direction and source integration; they do not attribute the detailed mathematical derivations to me personally. In particular, I did not personally derive or write the earlier 4/33 proof.

Detailed derivations and substantial drafting were produced with AI assistance, mainly GPT6-Pro and non-Pro Astra, with contributions from GPT 6.1 Sol, Grok 4.7 and Gemini 3.1 Pro. Codex also assisted with the Lean formalization and integration. Some research prompts were AI-written and selected or adapted by me. This describes the tools used across the research program, rather than assigning particular notes or lemmas to a model. Model review is not independent kernel verification.

## Used mathematical sources

- **OpenAI/math**, revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`: the original seven-eighths initialization, Hecke and Dirichlet definitions, and analytic and arithmetic framework. All 2,923 protected OAI source files in the used closure match that revision. Its Apache-2.0 license is retained.
- **Akash Levy's weighted-numerator proof**, revision `2fd60c0926b66ea18d7436f5ed55250fd006ab5d`, [PR6](https://github.com/GTimG/QuasiRiemannTracker/pull/6): numerator inversion, conductor allocation, coefficient estimates and contour assembly, adapted through the earlier Cycle25 development and in marked Cycle61 files. His final numerical endpoint is not a premise here. His original notice and license are retained unchanged.
- **The earlier AI-assisted QRH work directed by Hailey Collet**, [PR8](https://github.com/GTimG/QuasiRiemannTracker/pull/8) and [PR9](https://github.com/GTimG/QuasiRiemannTracker/pull/9), with the latter pinned at `58344dfdbe756cf2f743da1908ffe0582418cf5b`: completed reflection, variable moments, physical-source and common-profile machinery. Three ZetaZeroFree moment modules and 161 Cycle25 modules are in the local import closure. The older 4/33 and quartic endpoint theorems do not establish this new endpoint.
- **Zhongpai Gao's AI-assisted local refinement**, [PR15](https://github.com/GTimG/QuasiRiemannTracker/pull/15), selected source head `ca182b70ac2aee2d053d679b4ddf1233883f9eef`: local moments, Fourier/source reconstruction and physical bridges. Thirteen LocalMoment modules and adapted Cycle61 components are used. The supplied Apache-2.0 license and notices are retained, including their original descriptions of earlier packages. Those historical notices are read together with the authorship clarification above.

Cycle61 extends the applicable density range and local numerical region, verifies the rational endpoint, and completes the uniform main/error estimates and final assembly. The paper identifies the exact imported statements and their limitations. Source and transformation manifests preserve the used files and their identities. Unused exploratory work and alternative proof versions are not part of this package.

The submission layout was informed by the dependency-ordered bundles with isolated sections in **nielstron's [PR26](https://github.com/GTimG/QuasiRiemannTracker/pull/26)**, inspected at `16ce30342471344c2b2f0d383388e6f9acb9bccf`. This credits the packaging approach. The transformation manifest records the changes applied to Cycle61's used source closure.

Mathlib, PrimeNumberTheoremAnd, rellich-kondrachov and other Lake dependencies retain their own authorship and licenses. The standard tracker pins and compatibility patches govern those dependencies. Lean, Comparator, NanoDa, con-ron, lean4export and Palomar retain their own licenses; their binaries are not redistributed here. No upstream author, project or maintainer endorsement is implied.

--- licenses/gao-NOTICE.md ---
# Candidate source notice

New local-source argument and exact certificates prepared for Zhongpai Gao,
with AI assistance, 2026. Distributed under Apache-2.0.

The seven-eighths theorem and analytic/arithmetic framework are OpenAI inputs.
The weighted numerator is Akash Levy's input. The variable moment and quartic
source architecture are Hailey Collet's input. Mathematical reuse and exact
source pins are stated in the candidate. Original work retains its authorship;
see UPSTREAM_NOTICE.md. No maintainer or external reviewer endorsement is claimed.

--- licenses/gao-UPSTREAM_NOTICE.md ---
# Source notices

The notice below is retained from the pinned Cycle25 upstream package.
Its references to the "new manuscript", vendored sources, and package paths
describe that upstream package. Authorship of this local-moment revision is
stated separately in `NOTICE.md` and the manuscript; no upstream authorship
or endorsement of this revision is implied.

Copyright 2026 Hailey Collet. New manuscript and formalization material are
licensed under Apache-2.0. See `LICENSE` and `PROVENANCE.md`.

The vendored `formalization/OAI/` source is the exact import closure from
[OpenAI/math](https://github.com/openai/math) at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. It retains its upstream authorship
and Apache-2.0 license. The source inventory records each included module.
The new proof uses that development's original 7/8 nonvanishing theorem as
a weaker initialization, as well as its analytic and arithmetic foundations.

The `Cycle25` development adapts the numerator inversion, conductor allocation,
coefficient estimates and contour assembly of Akash Levy's
[weighted-numerator proof](https://github.com/akashlevy/QuasiRiemannTracker/tree/2fd60c0926b66ea18d7436f5ed55250fd006ab5d/proofs/akashlevy-20261009-weighted-numerator),
revision `2fd60c0926b66ea18d7436f5ed55250fd006ab5d`, and generalizes the moment,
counting and geometric estimates to the quartic endpoint. That source's
license and notice are retained in `licenses/`; its notice describes the
original upstream package. Its previous final nonvanishing theorem is not
used to establish the new endpoint.

The three `ZetaZeroFree/Analytic/Moments/` modules are reused from Hailey
Collet's [4/33 formalization](https://github.com/GTimG/QuasiRiemannTracker/pull/8).
They reorganize and adapt intermediate OpenAI proofs to establish an
unconditional moving-radical moment. The earlier 4/33 nonvanishing theorem
is not a dependency of this submission.

Mathlib, PrimeNumberTheoremAnd, rellich-kondrachov and the remaining Lake
dependencies retain their own authorship and licenses. Their exact revisions
and the required compatibility patches are recorded with the build recipe.
The patches retain the original licenses; only files needed by this proof's
import closure are included.

Lean, Comparator, NanoDa, con-ron, lean4export and the Palomar verification
helpers are used under their respective licenses. Their binaries are not
redistributed. No upstream project or maintainer endorsement is implied.

-/
