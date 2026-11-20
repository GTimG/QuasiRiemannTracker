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

/-- Actual original-cell 20 partition subtree with 1 terminal regions. -/
noncomputable def initialTree20 : InitialTree := (.direct ⟨⟨(9 / 32), (3 / 8), (3 / 8), (7 / 16)⟩, "native_current_exact", 190208209839⟩)

/-- Kernel-checked geometry, original-cell provenance, and positive stored direct margins for initialTree20. -/
theorem initialTree20_checked : initialTree20.check 20 qForest ⟨(9 / 32), (3 / 8), (3 / 8), (7 / 16)⟩ = true := by
  decide +kernel

end QRH.PhysicalCertificate
