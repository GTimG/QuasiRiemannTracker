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

/-- Actual original-cell 45 partition subtree with 1 terminal regions. -/
noncomputable def initialTree45 : InitialTree := (.central 1652)

/-- Kernel-checked geometry, original-cell provenance, and positive stored direct margins for initialTree45. -/
theorem initialTree45_checked : initialTree45.check 45 qForest ⟨(1743 / 4096), (3489 / 8192), (1023 / 2048), (2047 / 4096)⟩ = true := by
  decide +kernel

end QRH.PhysicalCertificate
