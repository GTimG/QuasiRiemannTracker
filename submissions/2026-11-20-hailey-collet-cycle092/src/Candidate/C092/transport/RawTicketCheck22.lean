/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.RawTicketCore
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace QRH.Cycle092.RawTicket
open QRH.Cycle092.TopData
theorem group22_part0_checked : ((group22.drop 0).take 50).all hullCheck = true := by decide +kernel
theorem group22_part1_checked : ((group22.drop 50).take 50).all hullCheck = true := by decide +kernel
theorem group22_part2_checked : ((group22.drop 100).take 50).all hullCheck = true := by decide +kernel
theorem group22_part3_checked : ((group22.drop 150).take 50).all hullCheck = true := by decide +kernel
theorem group22_part4_checked : ((group22.drop 200).take 50).all hullCheck = true := by decide +kernel
theorem group22_part5_checked : ((group22.drop 250).take 50).all hullCheck = true := by decide +kernel
theorem group22_part6_checked : ((group22.drop 300).take 50).all hullCheck = true := by decide +kernel
theorem group22_hull : group22.all hullCheck = true := by
  have he : group22 = ((group22.drop 0).take 50) ++ ((group22.drop 50).take 50) ++ ((group22.drop 100).take 50) ++ ((group22.drop 150).take 50) ++ ((group22.drop 200).take 50) ++ ((group22.drop 250).take 50) ++ ((group22.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append, group22_part0_checked, group22_part1_checked, group22_part2_checked, group22_part3_checked, group22_part4_checked, group22_part5_checked, group22_part6_checked, Bool.and_true]
end QRH.Cycle092.RawTicket
