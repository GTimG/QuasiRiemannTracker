/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.RawTicketCore
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace QRH.Cycle092.RawTicket
open QRH.Cycle092.TopData
theorem group00_part0_checked : ((group00.drop 0).take 50).all hullCheck = true := by decide +kernel
theorem group00_part1_checked : ((group00.drop 50).take 50).all hullCheck = true := by decide +kernel
theorem group00_part2_checked : ((group00.drop 100).take 50).all hullCheck = true := by decide +kernel
theorem group00_part3_checked : ((group00.drop 150).take 50).all hullCheck = true := by decide +kernel
theorem group00_part4_checked : ((group00.drop 200).take 50).all hullCheck = true := by decide +kernel
theorem group00_part5_checked : ((group00.drop 250).take 50).all hullCheck = true := by decide +kernel
theorem group00_part6_checked : ((group00.drop 300).take 50).all hullCheck = true := by decide +kernel
theorem group00_hull : group00.all hullCheck = true := by
  have he : group00 = ((group00.drop 0).take 50) ++ ((group00.drop 50).take 50) ++ ((group00.drop 100).take 50) ++ ((group00.drop 150).take 50) ++ ((group00.drop 200).take 50) ++ ((group00.drop 250).take 50) ++ ((group00.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append, group00_part0_checked, group00_part1_checked, group00_part2_checked, group00_part3_checked, group00_part4_checked, group00_part5_checked, group00_part6_checked, Bool.and_true]
end QRH.Cycle092.RawTicket
