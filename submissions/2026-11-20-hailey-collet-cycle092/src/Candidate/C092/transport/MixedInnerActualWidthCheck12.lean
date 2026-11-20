/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.MixedInnerActualWidthCore
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace QRH.Cycle092.MixedInnerActualWidth
open QRH.Cycle092.TopData
theorem group12_part0_checked : ((group12.drop 0).take 30).all widthCheck = true := by decide +kernel
theorem group12_part1_checked : ((group12.drop 30).take 30).all widthCheck = true := by decide +kernel
theorem group12_part2_checked : ((group12.drop 60).take 30).all widthCheck = true := by decide +kernel
theorem group12_part3_checked : ((group12.drop 90).take 30).all widthCheck = true := by decide +kernel
theorem group12_part4_checked : ((group12.drop 120).take 30).all widthCheck = true := by decide +kernel
theorem group12_part5_checked : ((group12.drop 150).take 30).all widthCheck = true := by decide +kernel
theorem group12_part6_checked : ((group12.drop 180).take 30).all widthCheck = true := by decide +kernel
theorem group12_part7_checked : ((group12.drop 210).take 30).all widthCheck = true := by decide +kernel
theorem group12_part8_checked : ((group12.drop 240).take 30).all widthCheck = true := by decide +kernel
theorem group12_part9_checked : ((group12.drop 270).take 30).all widthCheck = true := by decide +kernel
theorem group12_part10_checked : ((group12.drop 300).take 30).all widthCheck = true := by decide +kernel
theorem group12_width_checked : group12.all widthCheck = true := by
  have he : group12 = ((group12.drop 0).take 30) ++ ((group12.drop 30).take 30) ++ ((group12.drop 60).take 30) ++ ((group12.drop 90).take 30) ++ ((group12.drop 120).take 30) ++ ((group12.drop 150).take 30) ++ ((group12.drop 180).take 30) ++ ((group12.drop 210).take 30) ++ ((group12.drop 240).take 30) ++ ((group12.drop 270).take 30) ++ ((group12.drop 300).take 30) := by rfl
  rw [he]
  simp only [List.all_append, group12_part0_checked, group12_part1_checked, group12_part2_checked, group12_part3_checked, group12_part4_checked, group12_part5_checked, group12_part6_checked, group12_part7_checked, group12_part8_checked, group12_part9_checked, group12_part10_checked, Bool.and_true]
end QRH.Cycle092.MixedInnerActualWidth
