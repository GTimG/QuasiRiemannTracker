/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.InitialInputSlot
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.InitialMoment

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonRadialData CenteredMomentPrimeSlot CenteredMomentSourceRectangle
open CenteredMomentSourceMass CenteredMomentFiniteProfileExceptional
open CenteredMomentExceptionalAmplitudePair CenteredMomentEnergyBands
local notation "O" => HeckeFamily.O

theorem initial_plain_zero {a b : ℝ} (p : Profiles a b) (ha : 0<a) (i : Fin 2) :
    p.profile i 0=0 := by
  by_contra hn
  have h := (p.support i hn).1
  linarith

theorem initial_plain_pool_ne (b X Y : ℝ) (I : Ideal O)
    (h : I∈plainSupportPool b X Y) : I≠0 := by
  rcases Finset.mem_union.mp h with h|h
  · exact ((mem_idealBall _ _).mp h).1
  · exact ((mem_idealBall _ _).mp h).1

variable {ι : Type*} [Fintype ι]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)
variable (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hsW : Function.support W⊆Set.Icc (1:ℝ) 2)
variable (Z : ℝ) (hZ : 0<Z) (η η₀ : Character) (R₀ : Ideal O)
variable (θ : ι→RayQuotient.Characters rayM H) (w v : ι→ℝ) (t : ℝ)
variable {a b : ℝ} (p : Profiles a b) (ha : 0<a)
variable (X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
variable (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hprod : Y₁*Y₂=X₁*X₂)

/-- Literal natural initial data as the actual HIGH/common input. Every raw
scale is retained; both finite ordinary pools cover the X and Y profiles. -/
def initialInput : Input ι where
  η:=η
  m:=fixedBadMask*idealGenerator R₀
  A:=1
  t:=t
  slots:=fun i=>primePool rayM H 2 (Z^(w i))
  prime:=fun i I hI=>(Finset.mem_filter.mp hI).2.1
  ν:=fun i I=>idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I
  W:=fun i=>initialSlotProfile W (v i)
  lo:=fun _=>1
  hi:=fun _=>2
  P:=fun i=>Z^(w i)
  lo_pos:=fun _=>by norm_num
  P_pos:=fun _=>Real.rpow_pos_of_pos hZ _
  support:=fun i=>initialSlotProfile_support W hsW (v i)
  W₁:=p.profile 0
  W₂:=p.profile 1
  X₁:=X₁
  X₂:=X₂
  Y₁:=Y₁
  Y₂:=Y₂
  M:=fun _=>initialSlotBound W hW hsW
  M_ge_one:=fun _=>initialSlotBound_ge_one W hW hsW
  coefficient_bound:=by
    intro i I _
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (idealCoeff_norm_le_one _ I)).trans (initialSlotProfile_norm W hW hsW (v i) _)
  b₁:=b
  b₂:=b
  support₁:=fun x hx=>(p.support 0 hx).2
  support₂:=fun x hx=>(p.support 1 hx).2
  X₁_pos:=hX₁
  X₂_pos:=hX₂
  Y₁_pos:=hY₁
  Y₂_pos:=hY₂
  same_product:=hprod
  rows:=∅
  weight:=fun _=>0
  weight_nonneg:=by simp
  plain₁:=plainSupportPool b X₁ Y₁
  plain₂:=plainSupportPool b X₂ Y₂
  plain₁_ne:=initial_plain_pool_ne b X₁ Y₁
  plain₂_ne:=initial_plain_pool_ne b X₂ Y₂
  coverage₁:=plainSupportPool_coverage (p.profile 0) b X₁ Y₁
    (initial_plain_zero p ha 0) (fun x hx=>(p.support 0 hx).2) hX₁ hY₁
  coverage₂:=plainSupportPool_coverage (p.profile 1) b X₂ Y₂
    (initial_plain_zero p ha 1) (fun x hx=>(p.support 1 hx).2) hX₂ hY₂
  ν_bound:=fun i I=>idealCoeff_norm_le_one _ I
  W_bound:=fun i x=>initialSlotProfile_norm W hW hsW (v i) x
  lower:=1
  upper:=2
  lower_pos:=by norm_num
  lower_le:=fun _=>le_rfl
  upper_ge:=fun _=>le_rfl

local notation "s" => initialInput rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t
  p ha X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod

theorem initialInput_fields :
    (s).η=η ∧ (s).m=fixedBadMask*idealGenerator R₀ ∧ (s).A=1 ∧ (s).t=t ∧
      (s).W₁=p.profile 0 ∧ (s).W₂=p.profile 1 ∧
      (s).X₁=X₁ ∧ (s).X₂=X₂ ∧ (s).Y₁=Y₁ ∧ (s).Y₂=Y₂ ∧
      (s).slots=(fun i=>primePool rayM H 2 (Z^(w i))) ∧ (s).P=(fun i=>Z^(w i)) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem initialInput_coefficient (i : ι) (I : Ideal O) :
    (s).ν i I*(s).W i ((I.absNorm:ℝ)/(s).P i)=
      idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (33/50) (v i) I := rfl

theorem initialInput_coefficient_sigma (σ : ι→ℝ)
    (hlo : ∀i,(33/50:ℝ)≤σ i) (hhi : ∀i,σ i≤(33/50:ℝ)) (i : ι) (I : Ideal O) :
    (s).ν i I*(s).W i ((I.absNorm:ℝ)/(s).P i)=
      idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I := by
  rw [initial_sigma_fixed σ hlo hhi]
  rfl

theorem initialInput_volume : volume (s).toData=X₁*X₂*Z^(∑i,w i) := by
  change X₁*X₂*(∏i,Z^(w i))=_
  rw [←Real.rpow_sum_of_pos hZ]

/-- Only the exponent budget clips the ordinary scales. -/
theorem initialInput_volume_le_clipped (hZ1 : 1<Z) :
    volume (s).toData≤Z^(length Z X₁+length Z X₂+∑i,w i) := by
  have hx (X : ℝ) : X≤Z^(length Z X) := by
    rw [length,Real.rpow_logb hZ hZ1.ne' (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  rw [initialInput_volume,Real.rpow_add hZ,Real.rpow_add hZ]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (hx X₁) (hx X₂) hX₂.le (Real.rpow_nonneg hZ.le _))
    (Real.rpow_nonneg hZ.le _)

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.initialInput
#print axioms QRH.Record1252270103Low.initialInput_coefficient_sigma
#print axioms QRH.Record1252270103Low.initialInput_volume_le_clipped
