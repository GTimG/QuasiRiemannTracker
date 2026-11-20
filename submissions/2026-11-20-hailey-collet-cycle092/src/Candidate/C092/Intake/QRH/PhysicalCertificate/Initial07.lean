/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.PhysicalCertificate
import Candidate.C092.Intake.QRH.PhysicalCertificate.InitialBasic

/-! Actual initial-return partition. Positive stored direct margins do not assert pointwise price soundness. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QRH.PhysicalCertificate

open QRH.Coverage

/-- Actual original-cell 7 partition subtree with 9 terminal regions. -/
noncomputable def initialTree07 : InitialTree := (.uSplit (33 / 128) (.vSplit (7 / 32) (.uSplit (15 / 64) (.vSplit (3 / 16) (.direct ⟨⟨(3 / 16), (9 / 32), (1 / 8), (3 / 16)⟩, "original_saved", 431060847849⟩) (.direct ⟨⟨(3 / 16), (15 / 64), (3 / 16), (1 / 4)⟩, "original_saved", 697769600285⟩)) (.vSplit (3 / 16) (.direct ⟨⟨(3 / 16), (9 / 32), (1 / 8), (3 / 16)⟩, "original_saved", 431060847849⟩) (.direct ⟨⟨(15 / 64), (9 / 32), (3 / 16), (7 / 32)⟩, "original_saved", 277893199985⟩))) (.uSplit (15 / 64) (.direct ⟨⟨(3 / 16), (15 / 64), (3 / 16), (1 / 4)⟩, "original_saved", 697769600285⟩) (.direct ⟨⟨(15 / 64), (33 / 128), (7 / 32), (1 / 4)⟩, "fixed_interior_detector", 944229954218⟩))) (.vSplit (7 / 32) (.vSplit (3 / 16) (.direct ⟨⟨(3 / 16), (9 / 32), (1 / 8), (3 / 16)⟩, "original_saved", 431060847849⟩) (.direct ⟨⟨(15 / 64), (9 / 32), (3 / 16), (7 / 32)⟩, "original_saved", 277893199985⟩)) (.direct ⟨⟨(33 / 128), (9 / 32), (7 / 32), (1 / 4)⟩, "original_saved", 44574258566⟩)))

/-- Kernel-checked geometry, original-cell provenance, and positive stored direct margins for initialTree07. -/
theorem initialTree07_checked : initialTree07.check 7 qForest ⟨(3 / 16), (9 / 32), (1 / 8), (1 / 4)⟩ = true := by
  decide +kernel

end QRH.PhysicalCertificate
