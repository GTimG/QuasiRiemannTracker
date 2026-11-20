/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.TopBindingCore
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace QRH.Cycle092.Top.Binding
open QRH.Cycle092.TopData QRH.PhysicalCertificate
 theorem group16_boxes : TopData.group16.map Row.box =
    ((actualRecords.drop 4848).take 303).map StoredLeaf.box := by rfl
end QRH.Cycle092.Top.Binding
