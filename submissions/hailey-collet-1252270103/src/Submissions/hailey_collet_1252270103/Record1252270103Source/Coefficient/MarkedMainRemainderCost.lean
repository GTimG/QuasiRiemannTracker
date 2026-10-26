/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual selected MAIN zero and tail costs pay both allocation cards,
the frozen coefficient and the child's original plain-profile control. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.MarkedMainRemainderAllocation
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.MarkedMainRemainder
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn
open CenteredMomentSourceInputTailUniform (plainControl plainControl_nonneg)
local notation "O"=>HeckeFamily.O

theorem common_norm_power (x y ε : ℝ) (hx : 0≤x) (hy : 1≤y) (hε : 0≤ε) :
    (x/y)^(1+ε)≤x^(1+ε)/y := by
  have hy0:0<y:=zero_lt_one.trans_le hy
  rw [Real.div_rpow hx hy0.le]
  apply div_le_div_of_nonneg_left (Real.rpow_nonneg hx _) hy0
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hy (show (1:ℝ)≤1+ε by linarith)

/-- Constants are chosen before the source, profiles, selected allocation
and moving characters. The two exact analytic remainder factors stay outside
this finite allocation estimate. -/
theorem selected_allocation_remainder_bounds (N : ℕ) (Cs bs Cann εmass εzero : ℝ)
    (hCs : 1≤Cs) (hbs : 1≤bs) (hCann : 0<Cann) (hmass : 0<εmass) (hzero : 0≤εzero) :
    ∃Czero Ctail : ℝ,0<Czero ∧ 0<Ctail ∧
    ∀{ι : Type*}[Fintype ι](s : Input ι),Fintype.card ι≤N→(∀i,s.M i≤Cs)→s.upper≤bs→
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ))(C R : Ideal O),C≠0→
    ∀(B : actualAllocations s.pools C)(τ : Character)(t : ℝ),
      frozenCoefficient B.val C R s.ν s.W s.P≠0→
      (((actualAllocations s.pools C).card:ℝ)^2*‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*
        (4*plainControl (child s C R B τ t) W₁ W₂)^2*(Cann/(C.absNorm:ℝ))^(1+εzero)≤
          Czero*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*(C.absNorm:ℝ)^(εmass-1)) ∧
      (((actualAllocations s.pools C).card:ℝ)^2*‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*
        (2*plainControl (child s C R B τ t) W₁ W₂)^2*(volume (child s C R B τ t)/volume s)≤
          Ctail*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*(C.absNorm:ℝ)^(εmass-1)) := by
  obtain ⟨D,hD,hcards⟩:=uniform_allocation_card_square N εmass hmass
  let base:=16*D*(Cs^N)^4
  have hbase:0<base := by dsimp only [base];positivity
  refine ⟨base*Cann^(1+εzero),base*bs^N,by positivity,by positivity,?_⟩
  intro ι _ s hN hM hu W₁ W₂ C R hC B τ t hf
  let profile:=SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂
  have hp0:0≤profile := by dsimp only [profile];positivity
  have hNC:(0:ℝ)<C.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hNC1:(1:ℝ)≤C.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hc:=hcards s hN C hC
  have hfr:=pow_le_pow_left₀ (norm_nonneg _)
    (selected_frozen_norm s N Cs hN hCs hM C R B) 2
  have hplain:=selected_child_plain_control s N Cs hN hCs hM C R B τ t W₁ W₂
  have hplain0:=plainControl_nonneg (child s C R B τ t) W₁ W₂
  have hp4:(4*plainControl (child s C R B τ t) W₁ W₂)^2≤16*(Cs^N)^2*profile^2 := by
    have hh:=pow_le_pow_left₀ (mul_nonneg (by norm_num : (0:ℝ)≤4) hplain0)
      (mul_le_mul_of_nonneg_left hplain (by norm_num : (0:ℝ)≤4)) 2
    convert hh using 1 <;> dsimp only [profile] <;> ring
  have hraw:((actualAllocations s.pools C).card:ℝ)^2*‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*
      (4*plainControl (child s C R B τ t) W₁ W₂)^2≤base*profile^2*(C.absNorm:ℝ)^εmass := by
    have h:=mul_le_mul
      (mul_le_mul hc hfr (sq_nonneg _) (mul_nonneg hD.le (Real.rpow_nonneg hNC.le _))) hp4
      (sq_nonneg _) (by positivity)
    convert h using 1 <;> dsimp only [base] <;> ring
  have hp24:(2*plainControl (child s C R B τ t) W₁ W₂)^2≤
      (4*plainControl (child s C R B τ t) W₁ W₂)^2 := by nlinarith [sq_nonneg (plainControl (child s C R B τ t) W₁ W₂)]
  have hraw2:((actualAllocations s.pools C).card:ℝ)^2*‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*
      (2*plainControl (child s C R B τ t) W₁ W₂)^2≤base*profile^2*(C.absNorm:ℝ)^εmass :=
    (mul_le_mul_of_nonneg_left hp24 (mul_nonneg (sq_nonneg _) (sq_nonneg _))).trans hraw
  constructor
  · have hx:=common_norm_power Cann (C.absNorm:ℝ) εzero hCann.le hNC1 hzero
    have h:=mul_le_mul hraw hx (Real.rpow_nonneg (div_nonneg hCann.le hNC.le) _) (by positivity)
    apply h.trans_eq
    rw [Real.rpow_sub hNC,Real.rpow_one]
    dsimp only [profile]
    ring
  · have hv:=selected_child_volume_ratio s N bs hN hbs hu C R hC B τ t hf
    have h:=mul_le_mul hraw2 hv (div_nonneg (volume_pos _).le (volume_pos s).le) (by positivity)
    apply h.trans_eq
    rw [Real.rpow_sub hNC,Real.rpow_one]
    dsimp only [profile]
    ring

end
end QRH.Record1252270103Source.MarkedMainRemainder
#print axioms QRH.Record1252270103Source.MarkedMainRemainder.common_norm_power
#print axioms QRH.Record1252270103Source.MarkedMainRemainder.selected_allocation_remainder_bounds
