/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.RawTicketCore
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace QRH.Cycle092.RawTicket
open QRH.Cycle092.TopData
theorem group30_part0_checked : ((group30.drop 0).take 50).all hullCheck = true := by decide +kernel
theorem group30_part1_checked : ((group30.drop 50).take 50).all hullCheck = true := by decide +kernel
theorem group30_part2_checked : ((group30.drop 100).take 50).all hullCheck = true := by decide +kernel
theorem group30_part3_checked : ((group30.drop 150).take 50).all hullCheck = true := by decide +kernel
theorem group30_part4_checked : ((group30.drop 200).take 50).all hullCheck = true := by decide +kernel
theorem group30_part5_checked : ((group30.drop 250).take 50).all hullCheck = true := by decide +kernel
theorem group30_part6_checked : ((group30.drop 300).take 50).all hullCheck = true := by decide +kernel
theorem group30_hull : group30.all hullCheck = true := by
  have he : group30 = ((group30.drop 0).take 50) ++ ((group30.drop 50).take 50) ++ ((group30.drop 100).take 50) ++ ((group30.drop 150).take 50) ++ ((group30.drop 200).take 50) ++ ((group30.drop 250).take 50) ++ ((group30.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append, group30_part0_checked, group30_part1_checked, group30_part2_checked, group30_part3_checked, group30_part4_checked, group30_part5_checked, group30_part6_checked, Bool.and_true]
end QRH.Cycle092.RawTicket
