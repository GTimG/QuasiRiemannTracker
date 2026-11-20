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

/-- Actual original-cell 14 partition subtree with 1 terminal regions. -/
noncomputable def initialTree14 : InitialTree := (.direct ⟨⟨(15 / 64), (9 / 32), (5 / 16), (3 / 8)⟩, "native_current_exact", 1143574992983⟩)

/-- Kernel-checked geometry, original-cell provenance, and positive stored direct margins for initialTree14. -/
theorem initialTree14_checked : initialTree14.check 14 qForest ⟨(15 / 64), (9 / 32), (5 / 16), (3 / 8)⟩ = true := by
  decide +kernel

end QRH.PhysicalCertificate
