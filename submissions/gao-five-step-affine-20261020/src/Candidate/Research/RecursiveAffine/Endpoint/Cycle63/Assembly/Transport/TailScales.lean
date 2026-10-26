/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Assembly.Transport.GeometryFacts
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.TailScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.DyadIntegral
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Arithmetic.Constants
import Submissions.akashlevy_20261009_weighted_numerator.WeightedQRH.HighRows.TailScales

noncomputable local instance endpointFixedLedger_Candidate_Cycle63_Assembly_Transport_TailScales : Cycle63.AffineLedger := Cycle153.Root.rootLedger

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.Cycle153EndpointHighRowFamily
open ProbeHighRowFamily

lemma small_source_scale {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(Cycle153Endpoint.Arithmetic.ell:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(Cycle153Endpoint.Arithmetic.x:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(Cycle153Endpoint.Arithmetic.y:ℝ))^((1/2:ℝ)-1))=Z^(β-(4+Cycle153Endpoint.Transport.b)/6-(Cycle153Endpoint.Arithmetic.y/2-Cycle153Endpoint.Arithmetic.h*(17/50-1/6))+8*e) := by
  rw [OAI.SevenEighths.WeightedHighRowFamily.physical_scale_power Z hZ,hlength]
  congr 1
  rw [Cycle153Endpoint.Assembly.row_endpoint, Cycle153Endpoint.Transport.b]
  linarith [Cycle153Endpoint.Arithmetic.x_add_y]

lemma large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(Cycle153Endpoint.Arithmetic.ell:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(Cycle153Endpoint.Arithmetic.x:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(Cycle153Endpoint.Arithmetic.y:ℝ))^((2:ℝ)-1))=
      Z^((1+Cycle153Endpoint.Arithmetic.x/2+Cycle153Endpoint.Arithmetic.y)+(Cycle153Endpoint.Arithmetic.h:ℝ)*b) := by
  rw [OAI.SevenEighths.WeightedHighRowFamily.physical_scale_power Z hZ,hlength]
  congr 1
  rw [Cycle153Endpoint.Assembly.row_endpoint]
  ring

end SevenEighths.Cycle153EndpointHighRowFamily
end

end OAI
