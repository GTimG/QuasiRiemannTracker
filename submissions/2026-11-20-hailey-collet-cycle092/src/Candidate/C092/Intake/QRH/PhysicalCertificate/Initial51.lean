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

/-- Actual original-cell 51 partition subtree with 24 terminal regions. -/
noncomputable def initialTree51 : InitialTree := (.vSplit (511 / 1024) (.vSplit (1021 / 2048) (.uSplit (875 / 2048) (.uSplit (437 / 1024) (.vSplit (2041 / 4096) (.central 1659) (.central 1660)) (.vSplit (2041 / 4096) (.central 1667) (.central 1668))) (.vSplit (2041 / 4096) (.central 1675) (.central 1676))) (.uSplit (875 / 2048) (.uSplit (437 / 1024) (.vSplit (2043 / 4096) (.central 1661) (.central 1662)) (.vSplit (2043 / 4096) (.central 1669) (.central 1670))) (.vSplit (2043 / 4096) (.central 1677) (.central 1678)))) (.vSplit (1023 / 2048) (.uSplit (875 / 2048) (.uSplit (437 / 1024) (.vSplit (2045 / 4096) (.central 1663) (.central 1664)) (.vSplit (2045 / 4096) (.central 1671) (.central 1672))) (.vSplit (2045 / 4096) (.central 1679) (.central 1680))) (.uSplit (875 / 2048) (.uSplit (437 / 1024) (.vSplit (2047 / 4096) (.central 1665) (.central 1666)) (.vSplit (2047 / 4096) (.central 1673) (.central 1674))) (.vSplit (2047 / 4096) (.central 1681) (.central 1682)))))

/-- Kernel-checked geometry, original-cell provenance, and positive stored direct margins for initialTree51. -/
theorem initialTree51_checked : initialTree51.check 51 qForest ⟨(873 / 2048), (219 / 512), (255 / 512), (1 / 2)⟩ = true := by
  decide +kernel

end QRH.PhysicalCertificate
