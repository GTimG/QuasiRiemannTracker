/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.MixedInnerActualWidthCore
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace QRH.Cycle092.MixedInnerActualWidth
open QRH.Cycle092.TopData
theorem group20_part0_checked : ((group20.drop 0).take 30).all widthCheck = true := by decide +kernel
theorem group20_part1_checked : ((group20.drop 30).take 30).all widthCheck = true := by decide +kernel
theorem group20_part2_checked : ((group20.drop 60).take 30).all widthCheck = true := by decide +kernel
theorem group20_part3_checked : ((group20.drop 90).take 30).all widthCheck = true := by decide +kernel
theorem group20_part4_checked : ((group20.drop 120).take 30).all widthCheck = true := by decide +kernel
theorem group20_part5_checked : ((group20.drop 150).take 30).all widthCheck = true := by decide +kernel
theorem group20_part6_checked : ((group20.drop 180).take 30).all widthCheck = true := by decide +kernel
theorem group20_part7_checked : ((group20.drop 210).take 30).all widthCheck = true := by decide +kernel
theorem group20_part8_checked : ((group20.drop 240).take 30).all widthCheck = true := by decide +kernel
theorem group20_part9_checked : ((group20.drop 270).take 30).all widthCheck = true := by decide +kernel
theorem group20_part10_checked : ((group20.drop 300).take 30).all widthCheck = true := by decide +kernel
theorem group20_width_checked : group20.all widthCheck = true := by
  have he : group20 = ((group20.drop 0).take 30) ++ ((group20.drop 30).take 30) ++ ((group20.drop 60).take 30) ++ ((group20.drop 90).take 30) ++ ((group20.drop 120).take 30) ++ ((group20.drop 150).take 30) ++ ((group20.drop 180).take 30) ++ ((group20.drop 210).take 30) ++ ((group20.drop 240).take 30) ++ ((group20.drop 270).take 30) ++ ((group20.drop 300).take 30) := by rfl
  rw [he]
  simp only [List.all_append, group20_part0_checked, group20_part1_checked, group20_part2_checked, group20_part3_checked, group20_part4_checked, group20_part5_checked, group20_part6_checked, group20_part7_checked, group20_part8_checked, group20_part9_checked, group20_part10_checked, Bool.and_true]
end QRH.Cycle092.MixedInnerActualWidth
