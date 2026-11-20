/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.RawTicketCore
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace QRH.Cycle092.RawTicket
open QRH.Cycle092.TopData
theorem group12_part0_checked : ((group12.drop 0).take 50).all hullCheck = true := by decide +kernel
theorem group12_part1_checked : ((group12.drop 50).take 50).all hullCheck = true := by decide +kernel
theorem group12_part2_checked : ((group12.drop 100).take 50).all hullCheck = true := by decide +kernel
theorem group12_part3_checked : ((group12.drop 150).take 50).all hullCheck = true := by decide +kernel
theorem group12_part4_checked : ((group12.drop 200).take 50).all hullCheck = true := by decide +kernel
theorem group12_part5_checked : ((group12.drop 250).take 50).all hullCheck = true := by decide +kernel
theorem group12_part6_checked : ((group12.drop 300).take 50).all hullCheck = true := by decide +kernel
theorem group12_hull : group12.all hullCheck = true := by
  have he : group12 = ((group12.drop 0).take 50) ++ ((group12.drop 50).take 50) ++ ((group12.drop 100).take 50) ++ ((group12.drop 150).take 50) ++ ((group12.drop 200).take 50) ++ ((group12.drop 250).take 50) ++ ((group12.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append, group12_part0_checked, group12_part1_checked, group12_part2_checked, group12_part3_checked, group12_part4_checked, group12_part5_checked, group12_part6_checked, Bool.and_true]
end QRH.Cycle092.RawTicket
