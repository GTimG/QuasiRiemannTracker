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

/-- Actual original-cell 6 partition subtree with 2 terminal regions. -/
noncomputable def initialTree06 : InitialTree := (.uSplit (9 / 32) (.direct ⟨⟨(3 / 16), (9 / 32), 0, (1 / 8)⟩, "original_saved", 901695403678⟩) (.direct ⟨⟨(9 / 32), (3 / 8), 0, (1 / 8)⟩, "original_saved", 1176827858839⟩))

/-- Kernel-checked geometry, original-cell provenance, and positive stored direct margins for initialTree06. -/
theorem initialTree06_checked : initialTree06.check 6 qForest ⟨(3 / 16), (3 / 8), 0, (1 / 8)⟩ = true := by
  decide +kernel

end QRH.PhysicalCertificate
