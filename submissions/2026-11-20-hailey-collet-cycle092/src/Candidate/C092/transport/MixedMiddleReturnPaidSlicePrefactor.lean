/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual native source-count and moment prefactors, with heights kept polynomial. -/
import Candidate.C092.transport.MixedMiddleReturnPaidSliceMoment
import Candidate.C092.transport.PacketJoinPrefactor
set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorRawFiber
open QRH.Cycle092.MixedOffsetCount

def paidCountDegree (K : CountConstants) : ℕ := K.J₀+K.Jr+K.Ji+1
def paidCountConstant (labels : ℕ) (binCap : ℝ) (K : CountConstants) : ℝ :=
  (labels:ℝ)*binCap*192*K.C₀*max 1 K.K₀+192*K.Cr+12*K.Ci*K.Ki+1

/-- The exact original count coefficient is bounded by its actual fixed
source constants, original phase alphabet and dyadic count. -/
theorem paid_count_coefficient (labels bins : ℕ) (binCap : ℝ) (K : CountConstants)
    {U height : ℝ} (hh : 0 ≤ height) (hb : (bins:ℝ) ≤ binCap) :
    max 1 (countCoefficient labels bins U height K.K₀ K.Ki K.C₀ K.Cr K.Ci K.J₀ K.Jr K.Ji) ≤
      paidCountConstant labels binCap K*(1+(dyadicLength U:ℝ)^2)*(1+height)^(paidCountDegree K) := by
  let H := (1+height)^(paidCountDegree K)
  let L := 1+(dyadicLength U:ℝ)^2
  have hbase : 1 ≤ 1+height := by linarith
  have hH : 1 ≤ H := one_le_pow₀ hbase
  have hL : 1 ≤ L := by dsimp [L];nlinarith [sq_nonneg (dyadicLength U:ℝ)]
  have hb0 : 0 ≤ binCap := (Nat.cast_nonneg bins).trans hb
  have h0 : (1+height)*(1+height)^K.J₀ ≤ H := by
    rw [←pow_succ']
    exact pow_le_pow_right₀ hbase (by dsimp [paidCountDegree];omega)
  have hr : (1+height)*(1+height)^K.Jr ≤ H := by
    rw [←pow_succ']
    exact pow_le_pow_right₀ hbase (by dsimp [paidCountDegree];omega)
  have hi : (1+height)*(1+height)^K.Ji ≤ H := by
    rw [←pow_succ']
    exact pow_le_pow_right₀ hbase (by dsimp [paidCountDegree];omega)
  have hp0 := mul_le_mul_of_nonneg_left h0
    (show 0 ≤ (labels:ℝ)*binCap*192*K.C₀*max 1 K.K₀ by positivity [K.C₀_pos.le])
  have hpr := mul_le_mul_of_nonneg_left hr (show 0 ≤ 192*K.Cr by positivity [K.Cr_pos.le])
  have hpi := mul_le_mul_of_nonneg_left hi (show 0 ≤ 12*K.Ci*K.Ki by positivity [K.Ci_pos.le,K.Ki_nonneg])
  have hbins := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (labels:ℝ)*(dyadicLength U:ℝ)^2*192*(1+height)*(K.C₀*(1+height)^K.J₀)*max 1 K.K₀ by positivity [K.C₀_pos.le])
  have hdy := mul_le_mul_of_nonneg_left (show (dyadicLength U:ℝ)^2 ≤ L by dsimp [L];linarith)
    (show 0 ≤ ((labels:ℝ)*binCap*192*K.C₀*max 1 K.K₀)*H by positivity [K.C₀_pos.le,(zero_le_one.trans hH)])
  have hrL := mul_le_mul_of_nonneg_left hL (show 0 ≤ 192*K.Cr*H by positivity [K.Cr_pos.le,(zero_le_one.trans hH)])
  have hiL := mul_le_mul_of_nonneg_left hL (show 0 ≤ 12*K.Ci*K.Ki*H by positivity [K.Ci_pos.le,K.Ki_nonneg,(zero_le_one.trans hH)])
  have hprod : 1 ≤ L*H := one_le_mul_of_one_le_of_one_le hL hH
  have hc : 1 ≤ paidCountConstant labels binCap K := by
    unfold paidCountConstant
    have ha : 0 ≤ (labels:ℝ)*binCap*192*K.C₀*max 1 K.K₀ := by positivity [K.C₀_pos.le]
    have hb' : 0 ≤ 192*K.Cr := by positivity [K.Cr_pos.le]
    have hc' : 0 ≤ 12*K.Ci*K.Ki := by positivity [K.Ci_pos.le,K.Ki_nonneg]
    linarith
  apply max_le
  · exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hc hL) hH
  · unfold countCoefficient fiberConstant
    dsimp only [paidCountConstant]
    have hdy0 := mul_le_mul_of_nonneg_left hp0 (sq_nonneg (dyadicLength U:ℝ))
    nlinarith only [hbins,hdy0,hdy,hpr,hpi,hrL,hiL,hprod]

/-- The native dyadic count is paid uniformly in the genuine row scale. -/
theorem paid_dyadic_uniform {sigma : ℝ} (hs : 0<sigma) :
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,1 ≤ Z ∧ ∀d : ℝ,(1/100:ℝ) ≤ d →
      1+(dyadicLength (Z^d):ℝ)^2 ≤ C*(Z^d)^sigma := by
  obtain ⟨L,hL,hbound⟩ := HeckeDetectorClassBudget.dyadic_cost_eventually sigma hs
  obtain ⟨U0,hU0⟩ := eventually_atTop.mp hbound
  refine ⟨1+L,by linarith,?_⟩
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100)).eventually (eventually_ge_atTop U0),
    eventually_ge_atTop (1:ℝ)] with Z hZ0 hZ
  refine ⟨hZ,?_⟩
  intro d hd
  have hlarge : U0 ≤ Z^d := hZ0.trans (Real.rpow_le_rpow_of_exponent_le hZ hd)
  have hu := hU0 _ hlarge
  have hp : 1 ≤ (Z^d)^sigma := Real.one_le_rpow (Real.one_le_rpow hZ (by linarith)) hs.le
  nlinarith only [hu,hp]

#print axioms paid_count_coefficient
#print axioms paid_dyadic_uniform
end
end QRH.Cycle092.MixedMiddleReturn
