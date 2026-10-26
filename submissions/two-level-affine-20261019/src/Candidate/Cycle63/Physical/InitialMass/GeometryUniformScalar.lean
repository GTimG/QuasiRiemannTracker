import Candidate.Cycle63.Physical.InitialMass.GeometryScalarCompensation

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O

/-- Uniform before the moving source and both first-label orientations. -/
def geometrySupportConstant (N : ℕ)(lo a₁ a₂ : ℝ) : ℝ :=
  4/((min 1 lo)^N*a₁*a₂)

lemma geometrySupportConstant_pos (N : ℕ)(lo a₁ a₂ : ℝ)
    (hlo : 0<lo)(ha₁ : 0<a₁)(ha₂ : 0<a₂) :
    0<geometrySupportConstant N lo a₁ a₂ := by
  unfold geometrySupportConstant
  positivity

lemma actual_geometry_support_constant {ι : Type*}[Fintype ι]
    (s : Input ι)(N : ℕ)(lo a₁ a₂ : ℝ)(hn : Fintype.card ι≤N)
    (hlo : 0<lo)(hl : lo≤ s.lower)(ha₁ : 0<a₁)(ha₂ : 0<a₂) :
    0≤4/((∏i,s.lo i)*a₁*a₂) ∧
      4/((∏i,s.lo i)*a₁*a₂)≤geometrySupportConstant N lo a₁ a₂ := by
  have hp : (min 1 lo)^N≤∏i,s.lo i := by
    apply (pow_le_pow_of_le_one (lt_min zero_lt_one hlo).le (min_le_left _ _) hn).trans
    simpa only [Finset.prod_const,Finset.card_univ] using
      Finset.prod_le_prod₀ (s:=Finset.univ) (f:=fun _ : ι=>min 1 lo)
        (g:=fun i=>s.lo i) (fun _ _=>(lt_min zero_lt_one hlo).le)
        (fun i _=>(min_le_right _ _).trans (hl.trans (s.lower_le i)))
  have hpp : 0<∏i,s.lo i := Finset.prod_pos (fun i _=>s.lo_pos i)
  refine ⟨by positivity,?_⟩
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp ha₁.le) ha₂.le

end
end OAI.SevenEighths.Cycle63InitialMass
