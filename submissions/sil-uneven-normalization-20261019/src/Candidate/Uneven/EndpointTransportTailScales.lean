/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
import Candidate.Uneven.EndpointProbeGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.TailScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.DyadIntegral
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.UnevenEndpointPhysicalHighRowFamily
variable [config : _root_.OAI.SevenEighths.UnevenEndpoint.Configuration]
open ProbeHighRowFamily

lemma selected_scale_power {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ) (r : ℝ) :
    (∏i,(Z^(length i))^r)=Z^((∑i,length i)*r) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [Finset.sum_mul,Real.rpow_sum_of_pos hZ]

lemma physical_scale_power {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (lx ly σ υ r : ℝ) :
    (∏i,(Z^(length i))^r)*((Z^lx)^(1/2-r)*Z^(σ+r-1)*(Z^ly)^(υ-1))=
      Z^(σ-1+lx/2+ly*(υ-1)+(1-lx+∑i,length i)*r) := by
  rw [selected_scale_power Z hZ]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma small_source_scale {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(UnevenEndpointPhysical.Arithmetic.ell:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(UnevenEndpointPhysical.Arithmetic.x:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(UnevenEndpointPhysical.Arithmetic.y:ℝ))^((1/2:ℝ)-1))=Z^(β-(4+UnevenEndpointPhysical.Transport.b)/6-(UnevenEndpointPhysical.Arithmetic.y/2-UnevenEndpointPhysical.Arithmetic.h*(17/50-1/6))+8*e) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  rw [UnevenEndpointPhysical.Assembly.row_endpoint, UnevenEndpointPhysical.Transport.b]
  linarith [UnevenEndpointPhysical.Arithmetic.x_add_y]

lemma large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(UnevenEndpointPhysical.Arithmetic.ell:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(UnevenEndpointPhysical.Arithmetic.x:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(UnevenEndpointPhysical.Arithmetic.y:ℝ))^((2:ℝ)-1))=
      Z^((1+UnevenEndpointPhysical.Arithmetic.x/2+UnevenEndpointPhysical.Arithmetic.y)+(UnevenEndpointPhysical.Arithmetic.h:ℝ)*b) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  rw [UnevenEndpointPhysical.Assembly.row_endpoint]
  ring

end SevenEighths.UnevenEndpointPhysicalHighRowFamily
end

end OAI

