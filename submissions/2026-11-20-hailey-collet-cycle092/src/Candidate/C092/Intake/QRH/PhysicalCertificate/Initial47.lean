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

/-- Actual original-cell 47 partition subtree with 1 terminal regions. -/
noncomputable def initialTree47 : InitialTree := (.central 1654)

/-- Kernel-checked geometry, original-cell provenance, and positive stored direct margins for initialTree47. -/
theorem initialTree47_checked : initialTree47.check 47 qForest ⟨(6975 / 16384), (3489 / 8192), (2047 / 4096), (4095 / 8192)⟩ = true := by
  decide +kernel

end QRH.PhysicalCertificate
