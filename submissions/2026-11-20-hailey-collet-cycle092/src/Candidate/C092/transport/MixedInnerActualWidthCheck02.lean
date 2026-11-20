/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.MixedInnerActualWidthCore
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace QRH.Cycle092.MixedInnerActualWidth
open QRH.Cycle092.TopData
theorem group02_part0_checked : ((group02.drop 0).take 30).all widthCheck = true := by decide +kernel
theorem group02_part1_checked : ((group02.drop 30).take 30).all widthCheck = true := by decide +kernel
theorem group02_part2_checked : ((group02.drop 60).take 30).all widthCheck = true := by decide +kernel
theorem group02_part3_checked : ((group02.drop 90).take 30).all widthCheck = true := by decide +kernel
theorem group02_part4_checked : ((group02.drop 120).take 30).all widthCheck = true := by decide +kernel
theorem group02_part5_checked : ((group02.drop 150).take 30).all widthCheck = true := by decide +kernel
theorem group02_part6_checked : ((group02.drop 180).take 30).all widthCheck = true := by decide +kernel
theorem group02_part7_checked : ((group02.drop 210).take 30).all widthCheck = true := by decide +kernel
theorem group02_part8_checked : ((group02.drop 240).take 30).all widthCheck = true := by decide +kernel
theorem group02_part9_checked : ((group02.drop 270).take 30).all widthCheck = true := by decide +kernel
theorem group02_part10_checked : ((group02.drop 300).take 30).all widthCheck = true := by decide +kernel
theorem group02_width_checked : group02.all widthCheck = true := by
  have he : group02 = ((group02.drop 0).take 30) ++ ((group02.drop 30).take 30) ++ ((group02.drop 60).take 30) ++ ((group02.drop 90).take 30) ++ ((group02.drop 120).take 30) ++ ((group02.drop 150).take 30) ++ ((group02.drop 180).take 30) ++ ((group02.drop 210).take 30) ++ ((group02.drop 240).take 30) ++ ((group02.drop 270).take 30) ++ ((group02.drop 300).take 30) := by rfl
  rw [he]
  simp only [List.all_append, group02_part0_checked, group02_part1_checked, group02_part2_checked, group02_part3_checked, group02_part4_checked, group02_part5_checked, group02_part6_checked, group02_part7_checked, group02_part8_checked, group02_part9_checked, group02_part10_checked, Bool.and_true]
end QRH.Cycle092.MixedInnerActualWidth
