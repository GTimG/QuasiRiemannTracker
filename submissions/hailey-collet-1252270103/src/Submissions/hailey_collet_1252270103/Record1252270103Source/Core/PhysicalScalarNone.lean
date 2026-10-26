/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The inherited natural detector uses the exact three original gain branches. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.PhysicalScalar
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.PhysicalScalar
noncomputable section
open Record1252270103Finite Record1252270103StepScalar High

def naturalFacet (ν S F : ℝ) : Fin 3→ℝ :=
  ![Record12518109Gain.phi ν*S,
    Record12518109Gain.coeffA ν*S+Record12518109Gain.coeffB ν*F,
    Record12518109Gain.coeffC ν*F]
def naturalFactor (ν : ℝ) : Fin 3→ℝ := ![1,115-54*ν,185-138*ν]
def naturalDenominator (ν : ℝ) (j : Fin 3) : ℝ := densityDenom ν*naturalFactor ν j

theorem natural_denominator_bounds {ν : ℝ} (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (j : Fin 3) :
    0<naturalDenominator ν j ∧ naturalDenominator ν j≤1392 := by
  have ht : 0<densityDenom ν := by dsimp [densityDenom];linarith
  have htu : densityDenom ν≤12 := by dsimp [densityDenom];linarith
  have hf : 0<naturalFactor ν j ∧ naturalFactor ν j≤116 := by
    fin_cases j <;> norm_num [naturalFactor] <;> constructor <;> linarith
  refine ⟨mul_pos ht hf.1,?_⟩
  exact (mul_le_mul htu hf.2 hf.1.le (by norm_num : (0:ℝ)≤12)).trans_eq (by norm_num)

theorem source_none_facet_identity (n low : Source) (b ν : ℝ)
    (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (j : Fin 3) :
    sourceDensityWidthReal n low none b ν (Fin.castLE (by decide) j)=
      naturalDenominator ν j*(1-sourceBase n low b ν+
        naturalFacet ν (b-2*(n.allowance:ℝ)) (sourceFReal n low b-(n.allowance:ℝ)) j-(n.highFee:ℝ)) := by
  have ht : 15-6*ν≠0 := by linarith
  have ht' : 5-2*ν≠0 := by linarith
  have hd2 : 115-54*ν≠0 := by linarith
  have hd3 : 185-138*ν≠0 := by linarith
  fin_cases j <;>
    norm_num [sourceDensityWidthReal,naturalDenominator,naturalFactor,naturalFacet,
      sourceBase,physicalBase,rho,baseXi,densityDenom,w,
      Record12518109Gain.phi,Record12518109Gain.coeffA,Record12518109Gain.coeffB,
      Record12518109Gain.coeffC] <;> field_simp (discharger := linarith) <;> ring

end
end QRH.Record1252270103Source.PhysicalScalar
#print axioms QRH.Record1252270103Source.PhysicalScalar.source_none_facet_identity
#print axioms QRH.Record1252270103Source.PhysicalScalar.natural_denominator_bounds
