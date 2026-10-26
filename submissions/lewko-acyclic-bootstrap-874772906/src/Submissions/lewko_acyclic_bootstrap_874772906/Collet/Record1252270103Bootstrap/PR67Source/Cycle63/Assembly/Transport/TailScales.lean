import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Transport.GeometryFacts
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.TailScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.DyadIntegral
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Weighted.WeightedQRH.HighRows.TailScales
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.Cycle63HighRowFamily
open ProbeHighRowFamily

lemma small_source_scale {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(Cycle63.Arithmetic.ell:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(Cycle63.Arithmetic.x:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(Cycle63.Arithmetic.y:ℝ))^((1/2:ℝ)-1))=Z^(β-(4+Cycle63.Transport.b)/6-(Cycle63.Arithmetic.y/2-Cycle63.Arithmetic.h*(17/50-1/6))+8*e) := by
  rw [OAI.SevenEighths.WeightedHighRowFamily.physical_scale_power Z hZ,hlength]
  congr 1
  rw [Cycle63.Assembly.row_endpoint, Cycle63.Transport.b]
  linarith [Cycle63.Arithmetic.x_add_y]

lemma large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(Cycle63.Arithmetic.ell:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(Cycle63.Arithmetic.x:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(Cycle63.Arithmetic.y:ℝ))^((2:ℝ)-1))=
      Z^((1+Cycle63.Arithmetic.x/2+Cycle63.Arithmetic.y)+(Cycle63.Arithmetic.h:ℝ)*b) := by
  rw [OAI.SevenEighths.WeightedHighRowFamily.physical_scale_power Z hZ,hlength]
  congr 1
  rw [Cycle63.Assembly.row_endpoint]
  ring

end SevenEighths.Cycle63HighRowFamily
end

end OAI

end Record1252270103Bootstrap.PR67
