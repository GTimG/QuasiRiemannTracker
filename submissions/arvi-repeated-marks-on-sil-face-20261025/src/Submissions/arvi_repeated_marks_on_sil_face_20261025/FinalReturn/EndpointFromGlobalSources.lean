/- Repeated marks, single stage: the final return from the two final global sources.
The natural cap `2β − 1 ≤ naturalK/6 = 3/4` is the baseline's `β ≤ 7/8` (`Graph/NaturalCap.lean`),
so the intermediate return and the bootstrap of Collet's final stage are not used. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.EndpointFromSources
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Graph.NaturalCap
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.RepeatedMarks.Return
open QRH.Record1252270103Return
noncomputable section
open QRH.Record12518109Existence
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily

lemma natural_cap_return : 2*HeckeZeroSupremum.beta-1≤QRH.RepeatedMarks.Return.naturalK/6 := by
 have hi := QRH.RepeatedMarks.beta_le_seven_eighths
 norm_num [QRH.RepeatedMarks.Return.naturalK]
 linarith

theorem beta_of_two_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal) :
 HeckeZeroSupremum.beta≤QRH.RepeatedMarks.Return.theta :=
 Final.beta_of_global_sources hC hP natural_cap_return
end
end QRH.RepeatedMarks.Return
#print axioms QRH.RepeatedMarks.Return.beta_of_two_global_sources
