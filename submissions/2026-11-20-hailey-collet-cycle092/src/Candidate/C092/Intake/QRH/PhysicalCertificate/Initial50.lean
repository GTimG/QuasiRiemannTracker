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

/-- Actual original-cell 50 partition subtree with 2 terminal regions. -/
noncomputable def initialTree50 : InitialTree := (.vSplit (2047 / 4096) (.central 1657) (.central 1658))

/-- Kernel-checked geometry, original-cell provenance, and positive stored direct margins for initialTree50. -/
theorem initialTree50_checked : initialTree50.check 50 qForest ⟨(3489 / 8192), (873 / 2048), (1023 / 2048), (1 / 2)⟩ = true := by
  decide +kernel

end QRH.PhysicalCertificate
