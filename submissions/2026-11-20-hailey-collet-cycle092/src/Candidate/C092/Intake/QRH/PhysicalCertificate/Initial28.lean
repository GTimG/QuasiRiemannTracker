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

/-- Actual original-cell 28 partition subtree with 1 terminal regions. -/
noncomputable def initialTree28 : InitialTree := (.direct ⟨⟨(93 / 256), (189 / 512), (63 / 128), (1 / 2)⟩, "E49_top", 202660004383⟩)

/-- Kernel-checked geometry, original-cell provenance, and positive stored direct margins for initialTree28. -/
theorem initialTree28_checked : initialTree28.check 28 qForest ⟨(93 / 256), (189 / 512), (63 / 128), (1 / 2)⟩ = true := by
  decide +kernel

end QRH.PhysicalCertificate
