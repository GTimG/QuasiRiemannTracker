/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.MixedInnerActualWidthCore
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace QRH.Cycle092.MixedInnerActualWidth
open QRH.Cycle092.TopData
theorem group27_part0_checked : ((group27.drop 0).take 30).all widthCheck = true := by decide +kernel
theorem group27_part1_checked : ((group27.drop 30).take 30).all widthCheck = true := by decide +kernel
theorem group27_part2_checked : ((group27.drop 60).take 30).all widthCheck = true := by decide +kernel
theorem group27_part3_checked : ((group27.drop 90).take 30).all widthCheck = true := by decide +kernel
theorem group27_part4_checked : ((group27.drop 120).take 30).all widthCheck = true := by decide +kernel
theorem group27_part5_checked : ((group27.drop 150).take 30).all widthCheck = true := by decide +kernel
theorem group27_part6_checked : ((group27.drop 180).take 30).all widthCheck = true := by decide +kernel
theorem group27_part7_checked : ((group27.drop 210).take 30).all widthCheck = true := by decide +kernel
theorem group27_part8_checked : ((group27.drop 240).take 30).all widthCheck = true := by decide +kernel
theorem group27_part9_checked : ((group27.drop 270).take 30).all widthCheck = true := by decide +kernel
theorem group27_part10_checked : ((group27.drop 300).take 30).all widthCheck = true := by decide +kernel
theorem group27_width_checked : group27.all widthCheck = true := by
  have he : group27 = ((group27.drop 0).take 30) ++ ((group27.drop 30).take 30) ++ ((group27.drop 60).take 30) ++ ((group27.drop 90).take 30) ++ ((group27.drop 120).take 30) ++ ((group27.drop 150).take 30) ++ ((group27.drop 180).take 30) ++ ((group27.drop 210).take 30) ++ ((group27.drop 240).take 30) ++ ((group27.drop 270).take 30) ++ ((group27.drop 300).take 30) := by rfl
  rw [he]
  simp only [List.all_append, group27_part0_checked, group27_part1_checked, group27_part2_checked, group27_part3_checked, group27_part4_checked, group27_part5_checked, group27_part6_checked, group27_part7_checked, group27_part8_checked, group27_part9_checked, group27_part10_checked, Bool.and_true]
end QRH.Cycle092.MixedInnerActualWidth
