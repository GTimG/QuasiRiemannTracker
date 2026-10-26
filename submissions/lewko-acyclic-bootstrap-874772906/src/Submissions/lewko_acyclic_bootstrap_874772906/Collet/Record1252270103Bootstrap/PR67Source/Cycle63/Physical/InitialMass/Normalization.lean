import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.TerminalRadius
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceNormalization
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical
open HeckeFamily ActualEisensteinCubic CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstScale
open CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O

lemma outside_power (K V E R Z : ℝ) (hK : 0<K) (hV : 0<V)
    (hE : 0<E) (hR : 0<R) (hZ : 1<Z) :
    K/(V*E*Real.sqrt R)=
      Z^(Real.logb Z K-Real.logb Z V-Real.logb Z E-Real.logb Z R/2) := by
  have hz := zero_lt_one.trans hZ
  have hs : Z^(Real.logb Z R/2)=Real.sqrt R := by
    rw [div_eq_mul_inv,Real.rpow_mul hz.le,Real.rpow_logb hz hZ.ne' hR]
    norm_num [Real.sqrt_eq_rpow]
  rw [Real.rpow_sub hz,Real.rpow_sub hz,Real.rpow_sub hz,
    Real.rpow_logb hz hZ.ne' hK,Real.rpow_logb hz hZ.ne' hV,
    Real.rpow_logb hz hZ.ne' hE,hs]
  ring

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
