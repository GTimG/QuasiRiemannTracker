/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The sharp common-allocation payment retains d^(2 alpha)/NC^2, where d is the
actual ordinary factor norm. Original raw scales and frozen profile constants
are used throughout. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedExceptionalAllocationCost
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentAllocatedDetectorAmplitude
open CenteredMomentCommonRawScale CenteredMomentCommonRawCost CenteredMomentAllocationCost
open CenteredMomentCanonicalFirst CenteredMomentFiniteProfileExceptional
open QRH.Record1252270103Source.ForcedCost
open Record1252270103Second
local notation "O"=>ActualEisensteinCubic.O
local notation "frozenCost"=>CenteredMomentCommonExceptionalCost.frozenProfile
variable {ι : Type*} [Fintype ι]
local instance correctedExceptionalSharpDecidable : DecidableEq ι := Classical.decEq _

lemma centered_division_sharp (L d α : ℝ) (hd : 1≤d) (hα : 0≤α) :
    (max 1 (L/d))^(-α)≤d^α*(max 1 L)^(-α) := by
  have hd0 : 0<d := zero_lt_one.trans_le hd
  have hm : 0<max 1 (L/d) := zero_lt_one.trans_le (le_max_left _ _)
  have hM : 0<max 1 L := zero_lt_one.trans_le (le_max_left _ _)
  have hbase : max 1 L≤d*max 1 (L/d) := by
    apply max_le
    · nlinarith [le_max_left (1:ℝ) (L/d)]
    · have h:=mul_le_mul_of_nonneg_left (le_max_right (1:ℝ) (L/d)) hd0.le
      have he : d*(L/d)=L := by field_simp
      simpa only [he] using h
  have hp:=Real.rpow_le_rpow hM.le hbase hα
  rw [Real.mul_rpow hd0.le hm.le] at hp
  rw [Real.rpow_neg hm.le,Real.rpow_neg hM.le]
  have hh : 1/(max 1 (L/d))^α≤d^α/(max 1 L)^α :=
    (div_le_div_iff₀ (Real.rpow_pos_of_pos hm _) (Real.rpow_pos_of_pos hM _)).mpr (by simpa using hp)
  simpa only [one_div,div_eq_mul_inv,one_mul] using hh

lemma frozen_child_volume_sharp (s : Input ι) (X R : Ideal O) (hX : X≠0)
    (B : actualAllocations s.pools X) (τ : Character) (t : ℝ) :
    ‖frozenCoefficient B X R s.ν s.W s.P‖^2*volume (child s X R B τ t)^2≤
      (frozenCost s)^2/(X.absNorm:ℝ)^2*(volume s)^2 := by
  have hN : (0:ℝ)<X.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hX)
  have hb:=alloc_ne s X B
  have hred:=rawReduction_pos B.val hb s.P s.P_pos
  have hprod : finiteTupleProduct B.val=X := (Finset.mem_filter.mp B.property).2
  have hr : volume (child s X R B τ t)*rawReduction B.val s.P=volume s := by
    rw [child_volume_remaining]
    exact raw_scale_identity B.val hb (s.X₁*s.X₂) s.P
  have hvol : volume (child s X R B τ t)=volume s/rawReduction B.val s.P :=
    (eq_div_iff hred.ne').mpr hr
  have hprofile:=CenteredMomentCommonExceptionalCost.frozenProfile_nonneg s
  have hlinear : ‖frozenCoefficient B X R s.ν s.W s.P‖*volume (child s X R B τ t)≤
      frozenCost s/(X.absNorm:ℝ)*volume s := by
    by_cases hz : frozenCoefficient B X R s.ν s.W s.P=0
    · rw [hz,norm_zero,zero_mul]
      exact mul_nonneg (div_nonneg hprofile hN.le) (volume_pos s).le
    · have hn:=(actual_reduction_norm B.val hb X R hprod s.ν s.W s.P s.P_pos
        s.lower s.upper s.lower_pos s.slot_support hz).2
      have hc:=frozenCoefficient_norm B.val X R s.ν s.W s.P s.M s.ν_bound s.W_bound s.M_ge_one
      have hi : (1:ℝ)/rawReduction B.val s.P≤(max 1 s.upper)^Fintype.card ι/(X.absNorm:ℝ) :=
        (div_le_div_iff₀ hred hN).mpr (by simpa using hn)
      have hprod0 : 0≤∏i,s.M i := Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))
      have hh:=mul_le_mul hc hi (by positivity) hprod0
      have hh':=mul_le_mul_of_nonneg_right hh (volume_pos s).le
      rw [hvol]
      unfold CenteredMomentCommonExceptionalCost.frozenProfile
      convert hh' using 1 <;> ring
  have hh:=pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (volume_pos _).le) hlinear 2
  convert hh using 1 <;> ring

lemma child_centered_factor_sharp (s : Input ι) (X R : Ideal O)
    (B : actualAllocations s.pools X) (τ : Character) (t L α A : ℝ) (hα : 0≤α) :
    (A*(max 1 (L/ordinaryNorm B.val))^(-α)*slotControl (child s X R B τ t).toData)^2≤
      (ordinaryNorm B.val)^(2*α)*(A*(max 1 L)^(-α)*slotControl s.toData)^2 := by
  have hp:=centered_division_sharp L (ordinaryNorm B.val) (2*α)
    (ordinaryNorm_ge_one s X B) (by positivity)
  have hc:=pow_le_pow_left₀ (slotControl_nonneg (child s X R B τ t).toData)
    (child_slotControl s X R B τ t) 2
  have hd0 : 0≤ordinaryNorm B.val := zero_le_one.trans (ordinaryNorm_ge_one s X B)
  have hh:=mul_le_mul_of_nonneg_left (mul_le_mul hp hc (sq_nonneg _)
    (mul_nonneg (Real.rpow_nonneg hd0 _) (Real.rpow_nonneg (by positivity) _))) (sq_nonneg A)
  rw [mul_pow,mul_pow,centered_power_square,mul_pow,mul_pow,centered_power_square]
  convert hh using 1 <;> ring

lemma frozen_child_centered_factor_sharp (s : Input ι) (X R : Ideal O) (hX : X≠0)
    (B : actualAllocations s.pools X) (τ : Character) (t L α A : ℝ) (hα : 0≤α) :
    ‖frozenCoefficient B X R s.ν s.W s.P‖^2*
      (A*(max 1 (L/ordinaryNorm B.val))^(-α)*slotControl (child s X R B τ t).toData)^2*
        volume (child s X R B τ t)^2≤
    ((frozenCost s)^2*(ordinaryNorm B.val)^(2*α)/(X.absNorm:ℝ)^2)*
      (A*(max 1 L)^(-α)*slotControl s.toData)^2*(volume s)^2 := by
  have hv:=frozen_child_volume_sharp s X R hX B τ t
  have hf:=child_centered_factor_sharp s X R B τ t L α A hα
  have hh:=mul_le_mul hv hf (sq_nonneg _) (by positivity)
  convert hh using 1 <;> ring

lemma corrected_allocated_weighted_budget_sharp (s : Input ι) (X R : Ideal O) (hX : X≠0)
    (B : actualAllocations s.pools X) (S : Finset (ℕ×ℕ)) (W₁ W₂ Φ : 𝓢(ℝ,ℂ))
    (Q C D seed : Ideal O) (U : Finset (CommonIndex C D))
    (Z ε εL α Lraw Cr Mrow C₀ K₀ : ℝ)
    (hα : 0≤α) (hZ : 0≤Z) (hCr : 0≤Cr) (hK₀ : 0≤K₀) :
    ‖frozenCoefficient B X R s.ν s.W s.P‖^2*
      correctedAllocatedBudget s X R B S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀≤
    ((frozenCost s)^2*(ordinaryNorm B.val)^(2*α)/(X.absNorm:ℝ)^2)*
      correctedExceptionalBudget s S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀ := by
  let A:=C₀*(sourceControl S W₁*sourceControl S W₂)*Z^ε
  let G:=K₀*(seed.absNorm:ℝ)^εL*exceptionalRowCost Q C D U Z Cr Mrow*
    SchwartzMap.seminorm ℝ 0 0 Φ/(seed.absNorm:ℝ)
  have hcost:=exceptionalRowCost_nonneg Q C D U Z Cr Mrow hZ hCr
  have hsemi : 0≤SchwartzMap.seminorm ℝ 0 0 Φ := apply_nonneg _ _
  have hG : 0≤G := by dsimp [G];positivity
  have hf:=frozen_child_centered_factor_sharp s X R hX B s.η 0 Lraw α A hα
  have hp:=child_forcedProfileCost s X R B s.η 0
  have hn : 0≤‖frozenCoefficient B X R s.ν s.W s.P‖^2*
      (A*(max 1 (Lraw/ordinaryNorm B.val))^(-α)*slotControl (child s X R B s.η 0).toData)^2*
        volume (child s X R B s.η 0)^2 := by positivity
  have hh:=mul_le_mul_of_nonneg_left (mul_le_mul hp hf hn (forcedProfileCost_nonneg s)) hG
  unfold correctedAllocatedBudget correctedExceptionalBudget
  dsimp only [A,G] at hh
  convert hh using 1 <;> ring
end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_allocated_weighted_budget_sharp
