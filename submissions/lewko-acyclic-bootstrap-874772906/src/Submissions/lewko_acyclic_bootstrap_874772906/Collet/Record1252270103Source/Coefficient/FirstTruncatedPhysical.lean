/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual finite absolute first budget discharges the coarse side of the
height extension. The remaining inlet is bounded in both Mellin variables. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.FirstAbsoluteBudgetUniform
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.FirstTruncatedHeights
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.FirstTruncatedHeights
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentSectorLocalization CenteredMomentLogDyadic
open Cycle61InitialMass
open QRH.Record1252270103Source.High.CoupledFirst
local notation "O"=>HeckeFamily.O
local instance firstTruncatedPhysicalDecidable {ι:Type*} : DecidableEq (ι⊕Fin 2):=Classical.decEq _

/-- No all-height budget or physical-mass estimate is assumed. The scalar
profile/bin payment and two-sided balance cap are left in their actual form. -/
theorem actual_physical_from_truncated {ι:Type}[Fintype ι][DecidableEq ι]
    (W:𝓢(ℝ,ℂ))(decay smallDegree N:ℕ)
    (Cs hi whi wlo lo A D B L ξ τ target payment balanceLoss:ℝ)
    (hCs:1≤Cs)(hhi:1≤hi)(hwhi:0≤whi)(hwlo:0<wlo)(hlo:0<lo)
    (hA:0≤A)(hD:0≤D)(hB:0≤B)(hL:0≤L)(hξ:0≤ξ)(hτ:0<τ)
    (hc:HasCompactSupport logAnnulus)(hsm:ContDiff ℝ ∞ logAnnulus) :
    ∃J:ℕ,∃Ccoarse Cphysical:ℝ,0<Ccoarse ∧ 0≤Cphysical ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O)(W₁ W₂:𝓢(ℝ,ℂ))
      (M external Csmall:ℝ)(hK:0<Z^M),
      Fintype.card ι≤N→(∀i,s.M i≤Cs)→(∀i,1≤s.hi i)→(∀i,s.hi i≤hi)→(∀i,1≤s.P i)→
      0≤s.b₁→0≤s.b₂→lo≤s.lower→
      s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀v,‖modifier v‖≤2)→Squarefree seed→seed≠0→
      0<sourceRadius s→sourceRadius s≤Z^B→volume s≤Z^A→(Z^M)⁻¹≤Z^D→
      |Real.logb Z (volume s)|≤B→
      (∀I∈finiteColumns (Fintype.piFinset s.pools),(I.absNorm:ℝ)≤Z^L)→
      1≤external→0≤Csmall→
      ∀E H:ℤ×(Fin 5→ℤ)→ℝ,
      (∀key∈commonGeometryBins s modifier R seed (Z^M) Z ξ,0≤E key)→
      (∀key∈commonGeometryBins s modifier R seed (Z^M) Z ξ,0<H key)→
      (∀key∈commonGeometryBins s modifier R seed (Z^M) Z ξ,
        (SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*volume s≤E key*Z^payment)→
      (∀key∈commonGeometryBins s modifier R seed (Z^M) Z ξ,∀reflected:Bool,
        1≤(if reflected then (H key)⁻¹ else H key)*Z^balanceLoss)→
      TruncatedBudget W s modifier R seed (Z^M) Z ξ M (Real.logb Z (volume s))
        τ target external Csmall hK smallDegree E H→
      physicalMass s modifier R seed (CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator R) 1 W (Z^M) Z ξ≤
        Cphysical*(Csmall+Ccoarse)*external^J*Z^(M+target)*volume s*
          ∑key∈commonGeometryBins s modifier R seed (Z^M) Z ξ,
            E key/(1+dyadicScale key.1)^decay := by
  let absoluteExponent:=10*B+L+2+3*max A D+ξ/2
  obtain ⟨Ccoarse,hCcoarse,hcoarse⟩:=FirstAbsoluteBudget.eventually_balanced_live_budget_absolute
    N Cs hi whi wlo lo A D B L ξ hCs hhi hwhi hwlo hlo hA hD hB hL hξ
  obtain ⟨J,Cphysical,hCphysical,hphysical⟩:=physical_from_truncated_budgets (ι:=ι) W decay smallDegree
    τ (absoluteExponent+payment+balanceLoss) target hτ hc hsm
  refine ⟨J,Ccoarse,Cphysical,hCcoarse,hCphysical,?_⟩
  filter_upwards [hcoarse] with Z hcoarse
  refine ⟨hcoarse.1,?_⟩
  intro s modifier R seed W₁ W₂ M external Csmall hK hN hM hslot0 hslot hP hb₁ hb₂ hlower he₁ he₂
    hs₁ hs₂ hmod hs hs0 hpos hsource hV hKi hlog hpool he hCsmall E H hE hH hpayment hbalance hsmall
  have hZ0:0<Z:=zero_lt_one.trans hcoarse.1
  have hz₁:s.W₁ 0=0:=by
    rw [he₁]
    by_contra hn
    have hh:0∈Function.support (W₁:ℝ→ℂ):=hn
    have :=(hs₁ hh).1
    linarith
  have hz₂:s.W₂ 0=0:=by
    rw [he₂]
    by_contra hn
    have hh:0∈Function.support (W₂:ℝ→ℂ):=hn
    have :=(hs₂ hh).1
    linarith
  apply hphysical s modifier R seed (Z^M) Z ξ B M (Real.logb Z (volume s)) external Csmall Ccoarse
    hK hcoarse.1 hs hz₁ hz₂ hsource he hCsmall hCcoarse.le E H hE hH hsmall
  intro key hk reflected v
  have ha:=hcoarse.2 s modifier R seed W W₁ W₂ M hK hN hM hslot0 hslot hP hb₁ hb₂ hlower
    he₁ he₂ hs₁ hs₂ hmod hs hs0 hpos hsource hV hKi hlog hpool reflected key v
  have hpay:=balance_payment Z (E key) (H key)
    ((SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*volume s)
    payment balanceLoss hZ0 (hE key hk) (hH key hk) (hpayment key hk) reflected (hbalance key hk reflected)
  calc
    _≤Ccoarse*((SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*volume s)*Z^absoluteExponent :=
      ha.trans_eq (by dsimp [absoluteExponent];ring)
    _≤Ccoarse*((if reflected then E key/H key else E key*H key)*Z^(payment+balanceLoss))*Z^absoluteExponent :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpay hCcoarse.le) (Real.rpow_nonneg hZ0.le _)
    _=Ccoarse*(if reflected then E key/H key else E key*H key)*Z^(absoluteExponent+payment+balanceLoss) := by
      rw [show absoluteExponent+payment+balanceLoss=(payment+balanceLoss)+absoluteExponent by ring]
      simp only [Real.rpow_add hZ0]
      ring

end
end QRH.Record1252270103Source.FirstTruncatedHeights
#print axioms QRH.Record1252270103Source.FirstTruncatedHeights.actual_physical_from_truncated
