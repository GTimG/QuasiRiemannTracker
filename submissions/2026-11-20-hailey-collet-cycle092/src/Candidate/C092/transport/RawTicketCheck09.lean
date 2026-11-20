/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.RawTicketCore
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace QRH.Cycle092.RawTicket
open QRH.Cycle092.TopData
theorem group09_part0_checked : ((group09.drop 0).take 50).all hullCheck = true := by decide +kernel
theorem group09_part1_checked : ((group09.drop 50).take 50).all hullCheck = true := by decide +kernel
theorem group09_part2_checked : ((group09.drop 100).take 50).all hullCheck = true := by decide +kernel
theorem group09_part3_checked : ((group09.drop 150).take 50).all hullCheck = true := by decide +kernel
theorem group09_part4_checked : ((group09.drop 200).take 50).all hullCheck = true := by decide +kernel
theorem group09_part5_checked : ((group09.drop 250).take 50).all hullCheck = true := by decide +kernel
theorem group09_part6_checked : ((group09.drop 300).take 50).all hullCheck = true := by decide +kernel
theorem group09_hull : group09.all hullCheck = true := by
  have he : group09 = ((group09.drop 0).take 50) ++ ((group09.drop 50).take 50) ++ ((group09.drop 100).take 50) ++ ((group09.drop 150).take 50) ++ ((group09.drop 200).take 50) ++ ((group09.drop 250).take 50) ++ ((group09.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append, group09_part0_checked, group09_part1_checked, group09_part2_checked, group09_part3_checked, group09_part4_checked, group09_part5_checked, group09_part6_checked, Bool.and_true]
end QRH.Cycle092.RawTicket
