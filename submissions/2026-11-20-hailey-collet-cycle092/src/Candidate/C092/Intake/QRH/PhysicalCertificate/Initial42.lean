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

/-- Actual original-cell 42 partition subtree with 12 terminal regions. -/
noncomputable def initialTree42 : InitialTree := (.vSplit (1021 / 2048) (.uSplit (109 / 256) (.uSplit (871 / 2048) (.vSplit (2041 / 4096) (.central 1628) (.central 1629)) (.vSplit (2041 / 4096) (.central 1632) (.central 1633))) (.vSplit (2041 / 4096) (.central 1636) (.central 1637))) (.uSplit (109 / 256) (.uSplit (871 / 2048) (.vSplit (2043 / 4096) (.central 1630) (.central 1631)) (.vSplit (2043 / 4096) (.central 1634) (.central 1635))) (.vSplit (2043 / 4096) (.central 1638) (.central 1639))))

/-- Kernel-checked geometry, original-cell provenance, and positive stored direct margins for initialTree42. -/
theorem initialTree42_checked : initialTree42.check 42 qForest ⟨(435 / 1024), (873 / 2048), (255 / 512), (511 / 1024)⟩ = true := by
  decide +kernel

end QRH.PhysicalCertificate
