/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual selected forced ideal and Newton partition pay the retained-state
puncture once. The fixed R0 threshold precedes every moving selected datum. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.RegularRetainedNaturalState
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.RegularLowCollectedMask
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.RegularSelectedStateCaps
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open Cycle61InitialMass CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open OAI.SevenEighths.Record1252270103Source QRH.Record1252270103Low
open QRH.Record1252270103Source.RegularLowCollectedMask
local notation "O"=>HeckeFamily.O

theorem selected_extra_puncture_cap (P S A:Finset (Ideal O))(depth:ℕ)
    (Z amp:ℝ)(hZ:1≤Z)(hamp:0≤amp)(hS:S⊆P)(hA:A⊆S)(hdepth:S.card≤depth)
    (hp:∀p∈P,p≠0)(hpool:∀p∈P,(p.absNorm:ℝ)≤Z^amp)
    (Cf L:Ideal O)(hL:L≠0)(hCf:Cf∣L^2)(hLcap:(L.absNorm:ℝ)≤Z^(4:ℝ)) :
    let J:=Cf*(newtonDivisorPair S A).1*(newtonDivisorPair S A).2
    J≠0 ∧ (J.absNorm:ℝ)≤Z^(8+(depth:ℝ)*amp) := by
  intro J
  have hZ0:0<Z:=zero_lt_one.trans_le hZ
  have hCf0:Cf≠0:=ne_zero_of_dvd_ne_zero (pow_ne_zero 2 hL) hCf
  have hp0:=newton_pair_nonzero P S A hS hA hp
  have hJ0:J≠0:=by
    dsimp [J]
    rw [mul_assoc]
    exact mul_ne_zero hCf0 hp0
  refine ⟨hJ0,?_⟩
  have hCfn:(Cf.absNorm:ℝ)≤Z^(8:ℝ):=by
    have hh:=(CenteredMomentFirstSourceConductorCaps.divisor_norm_le Cf (L^2) (pow_ne_zero 2 hL) hCf)
    have hpow:(((L^2).absNorm:ℝ))≤Z^(8:ℝ):=by
      rw [map_pow,Nat.cast_pow]
      apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hLcap 2).trans_eq
      rw [←Real.rpow_mul_natCast hZ0.le]
      norm_num
    exact hh.trans hpow
  have hpair:=newton_pair_norm_cap P S A hS hA depth hdepth Z amp hZ hamp hpool
  dsimp [J]
  rw [mul_assoc,map_mul,Nat.cast_mul,Real.rpow_add hZ0]
  exact mul_le_mul hCfn hpair (Nat.cast_nonneg _) (Real.rpow_nonneg hZ0.le _)

theorem eventually_selected_retained_puncture (R₀:Ideal O)(hR₀:R₀≠0)
    (ηR:ℝ)(hηR:0<ηR) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀{α:Type*}[Fintype α][DecidableEq α](d:SecondInputDatum α)(second:Bool)
      (Cfirst Cf L:Ideal O)(Bfirst Bsecond amp:ℝ)(depth:ℕ)(P S A:Finset (Ideal O)),
      d.R=R₀*Cfirst→Cfirst≠0→L≠0→Cf∣L^2→
      (Cfirst.absNorm:ℝ)≤Z^Bfirst→((if second then d.D else d.C).absNorm:ℝ)≤Z^Bsecond→
      (L.absNorm:ℝ)≤Z^(4:ℝ)→S⊆P→A⊆S→S.card≤depth→0≤amp→
      (∀p∈P,p≠0)→(∀p∈P,(p.absNorm:ℝ)≤Z^amp)→
      let J:=Cf*(newtonDivisorPair S A).1*(newtonDivisorPair S A).2
      d.R≠0 ∧ J≠0 ∧ enlargedRetainedPuncture d second J≠0 ∧
        ((enlargedRetainedPuncture d second J).absNorm:ℝ)≤
          Z^(ηR+Bfirst+Bsecond+8+(depth:ℝ)*amp) := by
  filter_upwards [(tendsto_rpow_atTop hηR).eventually (eventually_ge_atTop (R₀.absNorm:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z hRcap hZ
  refine ⟨hZ,?_⟩
  intro α instα instDec d second Cfirst Cf L Bfirst Bsecond amp depth P S A
    hR hCfirst hL hCf hfirst hsecond hLcap hS hA hdepth hamp hp hpool J
  have hZ0:=zero_lt_one.trans hZ
  have hR0:d.R≠0:=by rw [hR];exact mul_ne_zero hR₀ hCfirst
  have hJ:=selected_extra_puncture_cap P S A depth Z amp hZ.le hamp hS hA hdepth hp hpool Cf L hL hCf hLcap
  refine ⟨hR0,hJ.1,enlarged_retained_puncture_ne d second J hR0 hJ.1,?_⟩
  have hRnorm:(d.R.absNorm:ℝ)≤Z^(ηR+Bfirst):=by
    rw [hR,map_mul,Nat.cast_mul,Real.rpow_add hZ0]
    exact mul_le_mul hRcap hfirst (Nat.cast_nonneg _) (Real.rpow_nonneg hZ0.le _)
  have hh:=enlarged_retained_puncture_norm d second J Z (ηR+Bfirst) Bsecond
    (8+(depth:ℝ)*amp) hZ0 hRnorm hsecond hJ.2
  convert hh using 1 <;> congr 1 <;> ring

end
end QRH.Record1252270103Source.RegularSelectedStateCaps
#print axioms QRH.Record1252270103Source.RegularSelectedStateCaps.selected_extra_puncture_cap
#print axioms QRH.Record1252270103Source.RegularSelectedStateCaps.eventually_selected_retained_puncture
