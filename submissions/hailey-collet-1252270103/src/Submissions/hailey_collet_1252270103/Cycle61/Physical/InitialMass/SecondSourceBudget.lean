import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondRetainedAssembly

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSecondLocalization CenteredMomentSourceSecondZeroEnergy
open CenteredMomentSupportedTailAggregate EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

/-- The zero-frequency term of the literal source, before normalization. -/
def originalSecondZero {ι : Type*} [Fintype ι] (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ((K:ℂ)*paperRadialFourier W 0)*sourceSecondZero
    (original s R seed).columns (original s R seed).beta s.η s.t

/-- Split the actual normalized source while keeping the retained terms
in one joint sum. Only the zero and discarded branches are bounded
separately by their absolute values. -/
theorem actual_joint_normalized_source_budget {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (slots : Label→Finset α) (s : (l : Label)→Input (slots l))
    (R seed : Label→Ideal O) (W : 𝓢(ℝ,ℂ)) (K Tsec : Label→ℝ) (Z ξ : ℝ)
    (hK : ∀l,0<K l)(weight : Label→ℝ)(hw : ∀l,0≤weight l) :
    (∑l,weight l*normalizedGaussSource (s l) (R l) (seed l) W (K l))≤
      (∑l,(weight l/volume (s l))*(‖originalSecondZero (s l) (R l) (seed l) W (K l)‖+
        ‖secondDiscardedEnergy (s l).η (s l).t (original (s l) (R l) (seed l)).columns
          (original (s l) (R l) (seed l)).beta W (K l) (Tsec l) Z ξ‖))+
      ‖∑l,((weight l/volume (s l):ℝ):ℂ)*secondRetainedEnergy (s l).η (s l).t
        (original (s l) (R l) (seed l)).columns (original (s l) (R l) (seed l)).beta
          W (K l) (Tsec l) Z ξ‖ := by
  let ret := fun l=>secondRetainedEnergy (s l).η (s l).t
    (original (s l) (R l) (seed l)).columns (original (s l) (R l) (seed l)).beta
      W (K l) (Tsec l) Z ξ
  let tail := fun l=>secondDiscardedEnergy (s l).η (s l).t
    (original (s l) (R l) (seed l)).columns (original (s l) (R l) (seed l)).beta
      W (K l) (Tsec l) Z ξ
  let zero := fun l=>originalSecondZero (s l) (R l) (seed l) W (K l)
  let c := fun l=>weight l/volume (s l)
  have hc (l : Label) : 0≤c l := div_nonneg (hw l) (volume_pos (s l)).le
  have he (l : Label) : weight l*normalizedGaussSource (s l) (R l) (seed l) W (K l)=
      c l*(zero l).re+c l*(ret l).re+c l*(tail l).re := by
    unfold normalizedGaussSource
    rw [sourceGaussEnergy_localized _ _ _ _ W (K l) (Tsec l) Z ξ (hK l)]
    simp only [Complex.add_re]
    dsimp only [c,zero,ret,tail,originalSecondZero]
    ring
  have hr : (∑l,c l*(ret l).re)≤‖∑l,(c l:ℂ)*ret l‖ := by
    have heq : (∑l,c l*(ret l).re)=(∑l,(c l:ℂ)*ret l).re := by
      simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [heq]
    exact Complex.re_le_norm _
  have hz : (∑l,(c l*(zero l).re+c l*(tail l).re))≤
      ∑l,c l*(‖zero l‖+‖tail l‖) := by
    apply Finset.sum_le_sum
    intro l hl
    calc
      _≤c l*‖zero l‖+c l*‖tail l‖ := add_le_add
        (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (hc l))
        (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (hc l))
      _=_ := by ring
  simp_rw [he]
  calc
    _=(∑l,(c l*(zero l).re+c l*(tail l).re))+(∑l,c l*(ret l).re) := by
      simp only [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _≤_ := add_le_add hz hr

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_joint_normalized_source_budget
