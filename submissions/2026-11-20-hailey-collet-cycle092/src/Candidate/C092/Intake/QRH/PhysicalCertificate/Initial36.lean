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

/-- Actual original-cell 36 partition subtree with 1 terminal regions. -/
noncomputable def initialTree36 : InitialTree := (.direct ⟨⟨(27 / 64), (15 / 32), (7 / 16), (15 / 32)⟩, "native_current_exact", 136500237936⟩)

/-- Kernel-checked geometry, original-cell provenance, and positive stored direct margins for initialTree36. -/
theorem initialTree36_checked : initialTree36.check 36 qForest ⟨(27 / 64), (15 / 32), (7 / 16), (15 / 32)⟩ = true := by
  decide +kernel

end QRH.PhysicalCertificate
