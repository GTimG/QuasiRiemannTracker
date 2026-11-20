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

/-- Actual original-cell 41 partition subtree with 48 terminal regions. -/
noncomputable def initialTree41 : InitialTree := (.vSplit (509 / 1024) (.uSplit (873 / 2048) (.vSplit (1017 / 2048) (.uSplit (109 / 256) (.uSplit (871 / 2048) (.vSplit (2033 / 4096) (.central 1580) (.central 1581)) (.vSplit (2033 / 4096) (.central 1588) (.central 1589))) (.vSplit (2033 / 4096) (.central 1596) (.central 1597))) (.uSplit (109 / 256) (.uSplit (871 / 2048) (.vSplit (2035 / 4096) (.central 1582) (.central 1583)) (.vSplit (2035 / 4096) (.central 1590) (.central 1591))) (.vSplit (2035 / 4096) (.central 1598) (.central 1599)))) (.vSplit (1017 / 2048) (.uSplit (875 / 2048) (.uSplit (437 / 1024) (.vSplit (2033 / 4096) (.central 1604) (.central 1605)) (.vSplit (2033 / 4096) (.central 1612) (.central 1613))) (.vSplit (2033 / 4096) (.central 1620) (.central 1621))) (.uSplit (875 / 2048) (.uSplit (437 / 1024) (.vSplit (2035 / 4096) (.central 1606) (.central 1607)) (.vSplit (2035 / 4096) (.central 1614) (.central 1615))) (.vSplit (2035 / 4096) (.central 1622) (.central 1623))))) (.uSplit (873 / 2048) (.vSplit (1019 / 2048) (.uSplit (109 / 256) (.uSplit (871 / 2048) (.vSplit (2037 / 4096) (.central 1584) (.central 1585)) (.vSplit (2037 / 4096) (.central 1592) (.central 1593))) (.vSplit (2037 / 4096) (.central 1600) (.central 1601))) (.uSplit (109 / 256) (.uSplit (871 / 2048) (.vSplit (2039 / 4096) (.central 1586) (.central 1587)) (.vSplit (2039 / 4096) (.central 1594) (.central 1595))) (.vSplit (2039 / 4096) (.central 1602) (.central 1603)))) (.vSplit (1019 / 2048) (.uSplit (875 / 2048) (.uSplit (437 / 1024) (.vSplit (2037 / 4096) (.central 1608) (.central 1609)) (.vSplit (2037 / 4096) (.central 1616) (.central 1617))) (.vSplit (2037 / 4096) (.central 1624) (.central 1625))) (.uSplit (875 / 2048) (.uSplit (437 / 1024) (.vSplit (2039 / 4096) (.central 1610) (.central 1611)) (.vSplit (2039 / 4096) (.central 1618) (.central 1619))) (.vSplit (2039 / 4096) (.central 1626) (.central 1627))))))

/-- Kernel-checked geometry, original-cell provenance, and positive stored direct margins for initialTree41. -/
theorem initialTree41_checked : initialTree41.check 41 qForest ⟨(435 / 1024), (219 / 512), (127 / 256), (255 / 512)⟩ = true := by
  decide +kernel

end QRH.PhysicalCertificate
