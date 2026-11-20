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

/-- Actual original-cell 56 partition subtree with 1 terminal regions. -/
noncomputable def initialTree56 : InitialTree := (.direct ⟨⟨(9 / 16), (3 / 4), (1 / 4), (1 / 2)⟩, "original_saved", 764973185650⟩)

/-- Kernel-checked geometry, original-cell provenance, and positive stored direct margins for initialTree56. -/
theorem initialTree56_checked : initialTree56.check 56 qForest ⟨(9 / 16), (3 / 4), (1 / 4), (1 / 2)⟩ = true := by
  decide +kernel

end QRH.PhysicalCertificate
