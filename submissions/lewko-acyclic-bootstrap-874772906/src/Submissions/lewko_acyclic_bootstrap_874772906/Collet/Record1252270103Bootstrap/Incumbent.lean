/- Adapted by Hailey Collet from ArviFoxy's accepted PR67, retaining
OpenAI, Akash Levy, Hailey Collet, Zhongpai Gao, DaysSky and upstream notices.
Apache-2.0. The public head is 0db497edc397d7076b1652b060e49c76b683e901. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Unconditional

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Bootstrap
open OAI.SevenEighths

theorem incumbent_beta : HeckeZeroSupremum.beta ≤ (174963413/200000000 : ℝ) := by
  have h := _root_.Record1252270103Bootstrap.PR67.Cycle63.FinalAssembly.beta_le_theta_of_chosen_affine
    _root_.Record1252270103Bootstrap.PR67.Cycle63.FinalAssembly.detector_affine_input
    _root_.Record1252270103Bootstrap.PR67.Cycle63.FinalAssembly.chosen_affine_input
  exact h.trans_eq (by norm_num [_root_.Record1252270103Bootstrap.PR67.Cycle63.Arithmetic.theta])

end QRH.Record1252270103Bootstrap
#print axioms QRH.Record1252270103Bootstrap.incumbent_beta
