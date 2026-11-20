/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.MixedInnerActualWidthCore
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace QRH.Cycle092.MixedInnerActualWidth
open QRH.Cycle092.TopData
theorem group23_part0_checked : ((group23.drop 0).take 30).all widthCheck = true := by decide +kernel
theorem group23_part1_checked : ((group23.drop 30).take 30).all widthCheck = true := by decide +kernel
theorem group23_part2_checked : ((group23.drop 60).take 30).all widthCheck = true := by decide +kernel
theorem group23_part3_checked : ((group23.drop 90).take 30).all widthCheck = true := by decide +kernel
theorem group23_part4_checked : ((group23.drop 120).take 30).all widthCheck = true := by decide +kernel
theorem group23_part5_checked : ((group23.drop 150).take 30).all widthCheck = true := by decide +kernel
theorem group23_part6_checked : ((group23.drop 180).take 30).all widthCheck = true := by decide +kernel
theorem group23_part7_checked : ((group23.drop 210).take 30).all widthCheck = true := by decide +kernel
theorem group23_part8_checked : ((group23.drop 240).take 30).all widthCheck = true := by decide +kernel
theorem group23_part9_checked : ((group23.drop 270).take 30).all widthCheck = true := by decide +kernel
theorem group23_part10_checked : ((group23.drop 300).take 30).all widthCheck = true := by decide +kernel
theorem group23_width_checked : group23.all widthCheck = true := by
  have he : group23 = ((group23.drop 0).take 30) ++ ((group23.drop 30).take 30) ++ ((group23.drop 60).take 30) ++ ((group23.drop 90).take 30) ++ ((group23.drop 120).take 30) ++ ((group23.drop 150).take 30) ++ ((group23.drop 180).take 30) ++ ((group23.drop 210).take 30) ++ ((group23.drop 240).take 30) ++ ((group23.drop 270).take 30) ++ ((group23.drop 300).take 30) := by rfl
  rw [he]
  simp only [List.all_append, group23_part0_checked, group23_part1_checked, group23_part2_checked, group23_part3_checked, group23_part4_checked, group23_part5_checked, group23_part6_checked, group23_part7_checked, group23_part8_checked, group23_part9_checked, group23_part10_checked, Bool.and_true]
end QRH.Cycle092.MixedInnerActualWidth
