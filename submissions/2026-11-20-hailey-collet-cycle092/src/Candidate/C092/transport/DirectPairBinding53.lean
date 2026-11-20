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

theorem pair_initial53Part000 : pairedTreeCheck 3 initial53Part000 = true := by
  decide +kernel

theorem pair_initial53Part001 : pairedTreeCheck 3 initial53Part001 = true := by
  decide +kernel

theorem pair_initial53Part002 : pairedTreeCheck 3 initial53Part002 = true := by
  simpa only [initial53Part002, pairedTreeCheck, pair_initial53Part000, pair_initial53Part001, Bool.and_self]

theorem pair_initial53Part003 : pairedTreeCheck 3 initial53Part003 = true := by
  decide +kernel

theorem pair_initial53Part004 : pairedTreeCheck 3 initial53Part004 = true := by
  decide +kernel

theorem pair_initial53Part005 : pairedTreeCheck 3 initial53Part005 = true := by
  simpa only [initial53Part005, pairedTreeCheck, pair_initial53Part003, pair_initial53Part004, Bool.and_self]

theorem pair_initial53Part006 : pairedTreeCheck 3 initial53Part006 = true := by
  simpa only [initial53Part006, pairedTreeCheck, pair_initial53Part002, pair_initial53Part005, Bool.and_self]

theorem pair_initial53Part007 : pairedTreeCheck 3 initial53Part007 = true := by
  decide +kernel

theorem pair_initial53Part008 : pairedTreeCheck 3 initial53Part008 = true := by
  decide +kernel

theorem pair_initial53Part009 : pairedTreeCheck 3 initial53Part009 = true := by
  simpa only [initial53Part009, pairedTreeCheck, pair_initial53Part007, pair_initial53Part008, Bool.and_self]

theorem pair_initial53Part010 : pairedTreeCheck 3 initial53Part010 = true := by
  decide +kernel

theorem pair_initial53Part011 : pairedTreeCheck 3 initial53Part011 = true := by
  decide +kernel

theorem pair_initial53Part012 : pairedTreeCheck 3 initial53Part012 = true := by
  simpa only [initial53Part012, pairedTreeCheck, pair_initial53Part010, pair_initial53Part011, Bool.and_self]

theorem pair_initial53Part013 : pairedTreeCheck 3 initial53Part013 = true := by
  simpa only [initial53Part013, pairedTreeCheck, pair_initial53Part009, pair_initial53Part012, Bool.and_self]

theorem pair_initialTree53 : pairedTreeCheck 3 initialTree53 = true := by
  simpa only [initialTree53, pairedTreeCheck, pair_initial53Part006, pair_initial53Part013, Bool.and_self]

end QRH.Cycle092.Direct
