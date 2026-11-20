/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.DirectPaired
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace QRH.Cycle092.Direct
open QRH.PhysicalCertificate

theorem pair_initial52Part000 : pairedTreeCheck 3 initial52Part000 = true := by
  decide +kernel

theorem pair_initial52Part001 : pairedTreeCheck 3 initial52Part001 = true := by
  decide +kernel

theorem pair_initialTree52 : pairedTreeCheck 3 initialTree52 = true := by
  simpa only [initialTree52, pairedTreeCheck, pair_initial52Part000, pair_initial52Part001, Bool.and_self]

end QRH.Cycle092.Direct
