/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.RawTicketCore
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace QRH.Cycle092.RawTicket
open QRH.Cycle092.TopData
theorem group27_part0_checked : ((group27.drop 0).take 50).all hullCheck = true := by decide +kernel
theorem group27_part1_checked : ((group27.drop 50).take 50).all hullCheck = true := by decide +kernel
theorem group27_part2_checked : ((group27.drop 100).take 50).all hullCheck = true := by decide +kernel
theorem group27_part3_checked : ((group27.drop 150).take 50).all hullCheck = true := by decide +kernel
theorem group27_part4_checked : ((group27.drop 200).take 50).all hullCheck = true := by decide +kernel
theorem group27_part5_checked : ((group27.drop 250).take 50).all hullCheck = true := by decide +kernel
theorem group27_part6_checked : ((group27.drop 300).take 50).all hullCheck = true := by decide +kernel
theorem group27_hull : group27.all hullCheck = true := by
  have he : group27 = ((group27.drop 0).take 50) ++ ((group27.drop 50).take 50) ++ ((group27.drop 100).take 50) ++ ((group27.drop 150).take 50) ++ ((group27.drop 200).take 50) ++ ((group27.drop 250).take 50) ++ ((group27.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append, group27_part0_checked, group27_part1_checked, group27_part2_checked, group27_part3_checked, group27_part4_checked, group27_part5_checked, group27_part6_checked, Bool.and_true]
end QRH.Cycle092.RawTicket
