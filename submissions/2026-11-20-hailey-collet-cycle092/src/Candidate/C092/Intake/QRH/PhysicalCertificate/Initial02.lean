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

/-- Actual original-cell 2 partition subtree with 1 terminal regions. -/
noncomputable def initialTree02 : InitialTree := (.direct ⟨⟨(3 / 8), (3 / 4), 0, (1 / 2)⟩, "original_saved", 2527657452649⟩)

/-- Kernel-checked geometry, original-cell provenance, and positive stored direct margins for initialTree02. -/
theorem initialTree02_checked : initialTree02.check 2 qForest ⟨(3 / 8), (3 / 4), 0, (1 / 2)⟩ = true := by
  decide +kernel

end QRH.PhysicalCertificate
