/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.MixedInnerActualWidthCore
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace QRH.Cycle092.MixedInnerActualWidth
open QRH.Cycle092.TopData
theorem group11_part0_checked : ((group11.drop 0).take 30).all widthCheck = true := by decide +kernel
theorem group11_part1_checked : ((group11.drop 30).take 30).all widthCheck = true := by decide +kernel
theorem group11_part2_checked : ((group11.drop 60).take 30).all widthCheck = true := by decide +kernel
theorem group11_part3_checked : ((group11.drop 90).take 30).all widthCheck = true := by decide +kernel
theorem group11_part4_checked : ((group11.drop 120).take 30).all widthCheck = true := by decide +kernel
theorem group11_part5_checked : ((group11.drop 150).take 30).all widthCheck = true := by decide +kernel
theorem group11_part6_checked : ((group11.drop 180).take 30).all widthCheck = true := by decide +kernel
theorem group11_part7_checked : ((group11.drop 210).take 30).all widthCheck = true := by decide +kernel
theorem group11_part8_checked : ((group11.drop 240).take 30).all widthCheck = true := by decide +kernel
theorem group11_part9_checked : ((group11.drop 270).take 30).all widthCheck = true := by decide +kernel
theorem group11_part10_checked : ((group11.drop 300).take 30).all widthCheck = true := by decide +kernel
theorem group11_width_checked : group11.all widthCheck = true := by
  have he : group11 = ((group11.drop 0).take 30) ++ ((group11.drop 30).take 30) ++ ((group11.drop 60).take 30) ++ ((group11.drop 90).take 30) ++ ((group11.drop 120).take 30) ++ ((group11.drop 150).take 30) ++ ((group11.drop 180).take 30) ++ ((group11.drop 210).take 30) ++ ((group11.drop 240).take 30) ++ ((group11.drop 270).take 30) ++ ((group11.drop 300).take 30) := by rfl
  rw [he]
  simp only [List.all_append, group11_part0_checked, group11_part1_checked, group11_part2_checked, group11_part3_checked, group11_part4_checked, group11_part5_checked, group11_part6_checked, group11_part7_checked, group11_part8_checked, group11_part9_checked, group11_part10_checked, Bool.and_true]
end QRH.Cycle092.MixedInnerActualWidth
