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

/-- Actual original-cell 43 partition subtree with 8 terminal regions. -/
noncomputable def initialTree43 : InitialTree := (.vSplit (1023 / 2048) (.uSplit (3483 / 8192) (.vSplit (2045 / 4096) (.central 1640) (.central 1641)) (.vSplit (2045 / 4096) (.central 1644) (.central 1645))) (.uSplit (3483 / 8192) (.vSplit (2047 / 4096) (.central 1642) (.central 1643)) (.vSplit (2047 / 4096) (.central 1646) (.central 1647))))

/-- Kernel-checked geometry, original-cell provenance, and positive stored direct margins for initialTree43. -/
theorem initialTree43_checked : initialTree43.check 43 qForest ⟨(435 / 1024), (1743 / 4096), (511 / 1024), (1 / 2)⟩ = true := by
  decide +kernel

end QRH.PhysicalCertificate
