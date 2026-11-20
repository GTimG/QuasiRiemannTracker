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

/-- Actual original-cell 12 partition subtree with 1 terminal regions. -/
noncomputable def initialTree12 : InitialTree := (.direct ⟨⟨(15 / 64), (9 / 32), (1 / 4), (5 / 16)⟩, "fixed_interior_detector", 39447489693⟩)

/-- Kernel-checked geometry, original-cell provenance, and positive stored direct margins for initialTree12. -/
theorem initialTree12_checked : initialTree12.check 12 qForest ⟨(15 / 64), (9 / 32), (1 / 4), (5 / 16)⟩ = true := by
  decide +kernel

end QRH.PhysicalCertificate
