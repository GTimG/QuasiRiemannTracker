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

/-- Actual original-cell 40 partition subtree with 96 terminal regions. -/
noncomputable def initialTree40 : InitialTree := (.vSplit (255 / 512) (.vSplit (509 / 1024) (.uSplit (867 / 2048) (.vSplit (1017 / 2048) (.uSplit (433 / 1024) (.uSplit (865 / 2048) (.vSplit (2033 / 4096) (.central 1484) (.central 1485)) (.vSplit (2033 / 4096) (.central 1500) (.central 1501))) (.vSplit (2033 / 4096) (.central 1516) (.central 1517))) (.uSplit (433 / 1024) (.uSplit (865 / 2048) (.vSplit (2035 / 4096) (.central 1486) (.central 1487)) (.vSplit (2035 / 4096) (.central 1502) (.central 1503))) (.vSplit (2035 / 4096) (.central 1518) (.central 1519)))) (.vSplit (1017 / 2048) (.uSplit (869 / 2048) (.uSplit (217 / 512) (.vSplit (2033 / 4096) (.central 1532) (.central 1533)) (.vSplit (2033 / 4096) (.central 1548) (.central 1549))) (.vSplit (2033 / 4096) (.central 1564) (.central 1565))) (.uSplit (869 / 2048) (.uSplit (217 / 512) (.vSplit (2035 / 4096) (.central 1534) (.central 1535)) (.vSplit (2035 / 4096) (.central 1550) (.central 1551))) (.vSplit (2035 / 4096) (.central 1566) (.central 1567))))) (.uSplit (867 / 2048) (.vSplit (1019 / 2048) (.uSplit (433 / 1024) (.uSplit (865 / 2048) (.vSplit (2037 / 4096) (.central 1488) (.central 1489)) (.vSplit (2037 / 4096) (.central 1504) (.central 1505))) (.vSplit (2037 / 4096) (.central 1520) (.central 1521))) (.uSplit (433 / 1024) (.uSplit (865 / 2048) (.vSplit (2039 / 4096) (.central 1490) (.central 1491)) (.vSplit (2039 / 4096) (.central 1506) (.central 1507))) (.vSplit (2039 / 4096) (.central 1522) (.central 1523)))) (.vSplit (1019 / 2048) (.uSplit (869 / 2048) (.uSplit (217 / 512) (.vSplit (2037 / 4096) (.central 1536) (.central 1537)) (.vSplit (2037 / 4096) (.central 1552) (.central 1553))) (.vSplit (2037 / 4096) (.central 1568) (.central 1569))) (.uSplit (869 / 2048) (.uSplit (217 / 512) (.vSplit (2039 / 4096) (.central 1538) (.central 1539)) (.vSplit (2039 / 4096) (.central 1554) (.central 1555))) (.vSplit (2039 / 4096) (.central 1570) (.central 1571)))))) (.vSplit (511 / 1024) (.uSplit (867 / 2048) (.vSplit (1021 / 2048) (.uSplit (433 / 1024) (.uSplit (865 / 2048) (.vSplit (2041 / 4096) (.central 1492) (.central 1493)) (.vSplit (2041 / 4096) (.central 1508) (.central 1509))) (.vSplit (2041 / 4096) (.central 1524) (.central 1525))) (.uSplit (433 / 1024) (.uSplit (865 / 2048) (.vSplit (2043 / 4096) (.central 1494) (.central 1495)) (.vSplit (2043 / 4096) (.central 1510) (.central 1511))) (.vSplit (2043 / 4096) (.central 1526) (.central 1527)))) (.vSplit (1021 / 2048) (.uSplit (869 / 2048) (.uSplit (217 / 512) (.vSplit (2041 / 4096) (.central 1540) (.central 1541)) (.vSplit (2041 / 4096) (.central 1556) (.central 1557))) (.vSplit (2041 / 4096) (.central 1572) (.central 1573))) (.uSplit (869 / 2048) (.uSplit (217 / 512) (.vSplit (2043 / 4096) (.central 1542) (.central 1543)) (.vSplit (2043 / 4096) (.central 1558) (.central 1559))) (.vSplit (2043 / 4096) (.central 1574) (.central 1575))))) (.uSplit (867 / 2048) (.vSplit (1023 / 2048) (.uSplit (433 / 1024) (.uSplit (865 / 2048) (.vSplit (2045 / 4096) (.central 1496) (.central 1497)) (.vSplit (2045 / 4096) (.central 1512) (.central 1513))) (.vSplit (2045 / 4096) (.central 1528) (.central 1529))) (.uSplit (433 / 1024) (.uSplit (865 / 2048) (.vSplit (2047 / 4096) (.central 1498) (.central 1499)) (.vSplit (2047 / 4096) (.central 1514) (.central 1515))) (.vSplit (2047 / 4096) (.central 1530) (.central 1531)))) (.vSplit (1023 / 2048) (.uSplit (869 / 2048) (.uSplit (217 / 512) (.vSplit (2045 / 4096) (.central 1544) (.central 1545)) (.vSplit (2045 / 4096) (.central 1560) (.central 1561))) (.vSplit (2045 / 4096) (.central 1576) (.central 1577))) (.uSplit (869 / 2048) (.uSplit (217 / 512) (.vSplit (2047 / 4096) (.central 1546) (.central 1547)) (.vSplit (2047 / 4096) (.central 1562) (.central 1563))) (.vSplit (2047 / 4096) (.central 1578) (.central 1579)))))))

/-- Kernel-checked geometry, original-cell provenance, and positive stored direct margins for initialTree40. -/
theorem initialTree40_checked : initialTree40.check 40 qForest ⟨(27 / 64), (435 / 1024), (127 / 256), (1 / 2)⟩ = true := by
  decide +kernel

end QRH.PhysicalCertificate
