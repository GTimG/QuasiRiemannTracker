/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.MixedInnerActualWidthCore
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace QRH.Cycle092.MixedInnerActualWidth
open QRH.Cycle092.TopData
theorem group17_part0_checked : ((group17.drop 0).take 30).all widthCheck = true := by decide +kernel
theorem group17_part1_checked : ((group17.drop 30).take 30).all widthCheck = true := by decide +kernel
theorem group17_part2_checked : ((group17.drop 60).take 30).all widthCheck = true := by decide +kernel
theorem group17_part3_checked : ((group17.drop 90).take 30).all widthCheck = true := by decide +kernel
theorem group17_part4_checked : ((group17.drop 120).take 30).all widthCheck = true := by decide +kernel
theorem group17_part5_checked : ((group17.drop 150).take 30).all widthCheck = true := by decide +kernel
theorem group17_part6_checked : ((group17.drop 180).take 30).all widthCheck = true := by decide +kernel
theorem group17_part7_checked : ((group17.drop 210).take 30).all widthCheck = true := by decide +kernel
theorem group17_part8_checked : ((group17.drop 240).take 30).all widthCheck = true := by decide +kernel
theorem group17_part9_checked : ((group17.drop 270).take 30).all widthCheck = true := by decide +kernel
theorem group17_part10_checked : ((group17.drop 300).take 30).all widthCheck = true := by decide +kernel
theorem group17_width_checked : group17.all widthCheck = true := by
  have he : group17 = ((group17.drop 0).take 30) ++ ((group17.drop 30).take 30) ++ ((group17.drop 60).take 30) ++ ((group17.drop 90).take 30) ++ ((group17.drop 120).take 30) ++ ((group17.drop 150).take 30) ++ ((group17.drop 180).take 30) ++ ((group17.drop 210).take 30) ++ ((group17.drop 240).take 30) ++ ((group17.drop 270).take 30) ++ ((group17.drop 300).take 30) := by rfl
  rw [he]
  simp only [List.all_append, group17_part0_checked, group17_part1_checked, group17_part2_checked, group17_part3_checked, group17_part4_checked, group17_part5_checked, group17_part6_checked, group17_part7_checked, group17_part8_checked, group17_part9_checked, group17_part10_checked, Bool.and_true]
end QRH.Cycle092.MixedInnerActualWidth
