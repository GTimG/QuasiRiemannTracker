/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform costs and active-source radius of the literal canonical initial input.
Only the original slot cardinality and fixed W enter these constants. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.InitialInput
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.Contract
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedExceptionalAllocationCost
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.ForcedCost.CenteredScale
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialPhysical
noncomputable section
open OAI OAI.SevenEighths QRH.Record1252270103Low
open scoped Classical BigOperators ContDiff
open Filter HeckeFamily ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentEnergyBands
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptional
open CenteredMomentOriginalCommonHarmonic CenteredMomentAmplificationChildInput
open CenteredMomentAllocatedDetectorAmplitude Record1252270103Second
local notation "O"=>ActualEisensteinCubic.O

section Initial
variable {ι : Type*} [Fintype ι]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)
variable (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hsW : Function.support W⊆Set.Icc (1:ℝ) 2)
variable (Z : ℝ) (hZ : 0<Z) (η η₀ : Character) (R₀ : Ideal O)
variable (θ : ι→RayQuotient.Characters rayM H) (w v : ι→ℝ) (t : ℝ)
variable (p : Profiles (1/4) (9/4))
variable (X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
variable (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hprod : Y₁*Y₂=X₁*X₂)
local notation "s" => initialInput rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t
  p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod

theorem initial_slot_control_identity :
    slotControl (s).toData=(initialSlotBound W hW hsW)^Fintype.card ι*
      (max 1 (256*initialSlotBound W hW hsW))^Fintype.card ι := by
  change (∏_i:ι,initialSlotBound W hW hsW)*
    (∏_i:ι,max 1 (128*max 0 (2:ℝ)*initialSlotBound W hW hsW))=_
  norm_num [Finset.prod_const]

theorem initial_forced_profile_identity :
    forcedProfileCost (s)=((initialSlotBound W hW hsW)^Fintype.card ι)^2*
      (2:ℝ)^Fintype.card ι := by
  change (∏_i:ι,initialSlotBound W hW hsW)^2*(max 1 (2:ℝ))^Fintype.card ι=_
  norm_num [Finset.prod_const]

/-- Full original cardinality N controls both costs, before all heights,
characters, profiles, widths and scales. No height growth is needed here. -/
theorem initial_cost_bounds (N : ℕ) (hN : Fintype.card ι≤N) :
    slotControl (s).toData≤(initialSlotBound W hW hsW)^N*
      (max 1 (256*initialSlotBound W hW hsW))^N ∧
    forcedProfileCost (s)≤((initialSlotBound W hW hsW)^N)^2*(2:ℝ)^N := by
  have hL:=initialSlotBound_ge_one W hW hsW
  have hpow:=pow_le_pow_right₀ hL hN
  constructor
  · rw [initial_slot_control_identity]
    exact mul_le_mul hpow (pow_le_pow_right₀ (le_max_left _ _) hN)
      (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) (pow_nonneg (zero_le_one.trans hL) _)
  · rw [initial_forced_profile_identity]
    exact mul_le_mul (pow_le_pow_left₀ (pow_nonneg (zero_le_one.trans hL) _) hpow 2)
      (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hN) (by positivity) (sq_nonneg _)

/-- Exact active-source radius; this does not assert a cap on padded pools. -/
theorem initial_source_radius_identity :
    sourceRadius (s)=(2:ℝ)^Fintype.card ι*(9/4)^2*volume (s) := by
  change (∏_i:ι,(2:ℝ))*(9/4)*(9/4)*(X₁*X₂)*(∏i,Z^(w i))=
    (2:ℝ)^Fintype.card ι*(9/4)^2*(X₁*X₂*(∏i,Z^(w i)))
  simp only [Finset.prod_const,Finset.card_univ]
  ring

theorem initial_volume_cap (B lam cap : ℝ) (hZ1 : 1<Z) (hB : B≤1) (hlam : 1≤lam)
    (hw : ∀i,0≤w i)
    (hadm : (globalFace B lam cap).Admissible (length Z X₁) (length Z X₂) (∑i,w i) 1) :
    volume (s)≤Z := by
  have hs : 0≤∑i,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hbudget : length Z X₁+length Z X₂+lam*(∑i,w i)≤B:=by
    simpa only [globalFace,mul_one] using hadm.2.2.2.2.2.2
  have hexp : length Z X₁+length Z X₂+(∑i,w i)≤1:=by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlam) hs]
  exact (initialInput_volume_le_clipped rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t
    p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod hZ1).trans
      (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ1.le hexp)

theorem initial_source_radius_cap (N : ℕ) (hN : Fintype.card ι≤N)
    (B lam cap : ℝ) (hZ1 : 1<Z) (hB : B≤1) (hlam : 1≤lam)
    (hw : ∀i,0≤w i)
    (hadm : (globalFace B lam cap).Admissible (length Z X₁) (length Z X₂) (∑i,w i) 1) :
    sourceRadius (s)≤(2:ℝ)^N*(9/4)^2*Z := by
  rw [initial_source_radius_identity]
  have hn:=pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hN
  have hv:=initial_volume_cap rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod B lam cap hZ1 hB hlam hw hadm
  exact mul_le_mul (mul_le_mul_of_nonneg_right hn (sq_nonneg _)) hv
    (CenteredMomentAmplificationChildInput.volume_pos _).le
    (by positivity)
end Initial

/-- The threshold only depends on original N and the requested positive loss. -/
theorem eventual_radius_absorption (N : ℕ) (loss : ℝ) (hloss : 0<loss) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ (2:ℝ)^N*(9/4)^2*Z≤Z^(1+loss) := by
  have hconst : ∀ᶠZ : ℝ in atTop,(2:ℝ)^N*(9/4)^2≤Z^loss :=
    (tendsto_rpow_atTop hloss).eventually (eventually_ge_atTop _)
  filter_upwards [hconst,eventually_gt_atTop (1:ℝ)] with Z hconst hZ
  refine ⟨hZ,?_⟩
  calc
    _≤Z^loss*Z := mul_le_mul_of_nonneg_right hconst (zero_lt_one.trans hZ).le
    _=Z^(1+loss) := by
      rw [show (1:ℝ)+loss=loss+1 by ring,Real.rpow_add (zero_lt_one.trans hZ),Real.rpow_one]

end
end QRH.Record1252270103Source.InitialPhysical
#print axioms QRH.Record1252270103Source.InitialPhysical.initial_slot_control_identity
#print axioms QRH.Record1252270103Source.InitialPhysical.initial_forced_profile_identity
#print axioms QRH.Record1252270103Source.InitialPhysical.initial_cost_bounds
#print axioms QRH.Record1252270103Source.InitialPhysical.initial_source_radius_identity
#print axioms QRH.Record1252270103Source.InitialPhysical.initial_volume_cap
#print axioms QRH.Record1252270103Source.InitialPhysical.initial_source_radius_cap
#print axioms QRH.Record1252270103Source.InitialPhysical.eventual_radius_absorption
