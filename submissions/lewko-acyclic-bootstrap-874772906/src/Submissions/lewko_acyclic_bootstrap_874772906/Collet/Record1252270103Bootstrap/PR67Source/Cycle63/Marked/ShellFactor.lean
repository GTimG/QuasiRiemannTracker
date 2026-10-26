import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section

/-- Scalar multiplication of the retained-source envelope, finite partition
count, and raw density estimate. Only the two scale powers change. -/
theorem marked_shell_scalar_factor
    (Csrc Cpart Cmult Craw Cprofile K R H n X Y Z : ℝ)
    (hsrc : 0≤Csrc)(hpart : 0≤Cpart)(hmult : 0≤Cmult)(hraw : 0≤Craw)
    (hK : 0≤K)(hR : 0≤R)(hH : 1≤H)(hn : 0≤n)(hZ : 0≤Z)
    (hpow : X*Y≤Z) :
    (Csrc*Cprofile^2*K*R*X)*(Cpart*(n*(Cmult*Craw*Y)))≤
      n*(Csrc*Cpart*Cmult*Craw*Cprofile^2*K*H*R*Z) := by
  let factor:=n*(Csrc*Cpart*Cmult*Craw*Cprofile^2*K*R)
  have hf : 0≤factor := by dsimp [factor];positivity
  calc
    _=factor*(X*Y) := by dsimp [factor];ring
    _≤factor*Z := mul_le_mul_of_nonneg_left hpow hf
    _≤factor*H*Z := mul_le_mul_of_nonneg_right
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hH hf) hZ
    _=_ := by dsimp [factor];ring

end
end OAI.SevenEighths.Cycle63MarkedPlain

end Record1252270103Bootstrap.PR67
