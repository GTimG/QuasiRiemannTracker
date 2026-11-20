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

/-- Actual original-cell 25 partition subtree with 1 terminal regions. -/
noncomputable def initialTree25 : InitialTree := (.direct ⟨⟨(45 / 128), (93 / 256), (31 / 64), (1 / 2)⟩, "E49_top", 250129939704⟩)

/-- Kernel-checked geometry, original-cell provenance, and positive stored direct margins for initialTree25. -/
theorem initialTree25_checked : initialTree25.check 25 qForest ⟨(45 / 128), (93 / 256), (31 / 64), (1 / 2)⟩ = true := by
  decide +kernel

end QRH.PhysicalCertificate
