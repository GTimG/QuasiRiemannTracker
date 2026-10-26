/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The first Mellin height extension preserves both exact bin-balance factors.
Only a bounded-height analytic inlet is used; the coarse input is separate. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalBalancedContraction
import Submissions.hailey_collet_1252270103.Cycle61.Physical.ExternalHeight
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.FirstTruncatedHeights
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentSectorLocalization CenteredMomentLogDyadic
open Cycle61InitialMass
open QRH.Record1252270103Source.High.CoupledFirst
local notation "O"=>HeckeFamily.O

theorem balance_payment (Z E H P payment balanceLoss:ℝ)(hZ:0<Z)(hE:0≤E)(hH:0<H)
    (hP:P≤E*Z^payment)(reflected:Bool)
    (hb:1≤(if reflected then H⁻¹ else H)*Z^balanceLoss) :
    P≤(if reflected then E/H else E*H)*Z^(payment+balanceLoss) := by
  have hpos:0≤E*Z^payment:=mul_nonneg hE (Real.rpow_nonneg hZ.le _)
  have hh:=mul_le_mul_of_nonneg_left hb hpos
  apply hP.trans
  cases reflected <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,mul_one] at hh ⊢ <;>
    rw [Real.rpow_add hZ] <;> simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh

theorem product_height_extension (τ extra target:ℝ)(hτ:0<τ)(smallDegree:ℕ) :
    ∃J:ℕ,∀(f:ℝ→ℝ)(Z external base control Csmall Ccoarse origin:ℝ)(reflected:Bool),
      1≤Z→1≤external→0≤control→0≤Csmall→0≤Ccoarse→
      (∀t u:ℝ,(1+‖t‖)*(1+‖u‖)*external≤Z^τ→
        f (origin+2*Real.pi*(u-(if reflected then -t else t)))≤
          Csmall*control*((1+‖t‖)*(1+‖u‖)*external)^smallDegree*Z^(base+target))→
      (∀v:ℝ,f v≤Ccoarse*control*Z^(base+extra))→
      ∀t u:ℝ,f (origin+2*Real.pi*(u-(if reflected then -t else t)))≤
        ((Csmall+Ccoarse)*control*Z^(base+target)*external^J*(1+‖t‖)^J)*(1+‖u‖)^(2*J) := by
  obtain ⟨J,hJ⟩:=Cycle61.Physical.extend_bounded_height_bound hτ extra target smallDegree 0
  refine ⟨J,?_⟩
  intro f Z external base control Cs Cc origin reflected hZ he hc hs hb hsmall hcoarse t u
  have ht:1≤1+‖t‖:=by linarith [norm_nonneg t]
  have hu:1≤1+‖u‖:=by linarith [norm_nonneg u]
  have htu:1≤(1+‖t‖)*(1+‖u‖):=by nlinarith [mul_nonneg (norm_nonneg t) (norm_nonneg u)]
  have hp:1≤(1+‖t‖)*(1+‖u‖)*external:=htu.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he (by positivity : 0≤(1+‖t‖)*(1+‖u‖)))
  have hh:=hJ Z ((1+‖t‖)*(1+‖u‖)*external) base
    (f (origin+2*Real.pi*(u-(if reflected then -t else t)))) control Cs Cc
    hZ hp hc hs hb (hsmall t u) (by simpa only [pow_zero,mul_one] using hcoarse _)
  rw [mul_pow,mul_pow] at hh
  have hpow:(1+‖u‖)^J≤(1+‖u‖)^(2*J):=pow_le_pow_right₀ hu (by omega)
  calc
    _≤((Cs+Cc)*control*Z^(base+target)*external^J*(1+‖t‖)^J)*(1+‖u‖)^J:=by
      convert hh using 1 <;> ring
    _≤_:=mul_le_mul_of_nonneg_left hpow (by positivity)

/-- The bounded first-budget inlet on the actual two Mellin variables and
one external-height envelope. All original geometry bins remain. -/
def TruncatedBudget {ι:Type*}[Fintype ι][DecidableEq ι]
    (W:𝓢(ℝ,ℂ))(s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O)
    (K Z ξ M A τ target external Cs:ℝ)(hK:0<K)(smallDegree:ℕ)
    (E H:ℤ×(Fin 5→ℤ)→ℝ) : Prop :=
  ∀key∈commonGeometryBins s modifier R seed K Z ξ,∀(reflected:Bool)(t u:ℝ),
    (1+‖t‖)*(1+‖u‖)*external≤Z^τ→
    balancedLiveBudget reflected s modifier R seed K Z ξ M A hK key
      (fun q=>normPhase (coordinateBlock s modifier R seed W K Z ξ q))
      (s.t+2*Real.pi*(u-(if reflected then -t else t)))≤
    Cs*(if reflected then E key/H key else E key*H key)*
      ((1+‖t‖)*(1+‖u‖)*external)^smallDegree*Z^target

/-- The original geometry-bin sum, decay and volume normalization are retained.
Its only analytic premise is the named product-height truncated budget. -/
theorem physical_from_truncated_budgets {ι:Type*}[Fintype ι][DecidableEq ι]
    (W:𝓢(ℝ,ℂ))(decay smallDegree:ℕ)(τ extra target:ℝ)(hτ:0<τ)
    (hc:HasCompactSupport logAnnulus)(hsm:ContDiff ℝ ∞ logAnnulus) :
    ∃J:ℕ,∃C:ℝ,0≤C ∧ ∀(s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O)
      (K Z ξ B M A external Cs Cc:ℝ)(hK:0<K)(hZ:1<Z),
      Squarefree seed→s.W₁ 0=0→s.W₂ 0=0→sourceRadius s≤Z^B→
      1≤external→0≤Cs→0≤Cc→
      ∀E H:ℤ×(Fin 5→ℤ)→ℝ,
      (∀key∈commonGeometryBins s modifier R seed K Z ξ,0≤E key)→
      (∀key∈commonGeometryBins s modifier R seed K Z ξ,0<H key)→
      (∀key∈commonGeometryBins s modifier R seed K Z ξ,∀(reflected:Bool)(t u:ℝ),
        (1+‖t‖)*(1+‖u‖)*external≤Z^τ→
        balancedLiveBudget reflected s modifier R seed K Z ξ M A hK key
          (fun q=>normPhase (coordinateBlock s modifier R seed W K Z ξ q))
          (s.t+2*Real.pi*(u-(if reflected then -t else t)))≤
        Cs*(if reflected then E key/H key else E key*H key)*
          ((1+‖t‖)*(1+‖u‖)*external)^smallDegree*Z^target)→
      (∀key∈commonGeometryBins s modifier R seed K Z ξ,∀(reflected:Bool)(v:ℝ),
        balancedLiveBudget reflected s modifier R seed K Z ξ M A hK key
          (fun q=>normPhase (coordinateBlock s modifier R seed W K Z ξ q)) v≤
        Cc*(if reflected then E key/H key else E key*H key)*Z^extra)→
      physicalMass s modifier R seed (CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator R) 1 W K Z ξ≤
        C*(Cs+Cc)*external^J*Z^(M+target)*volume s*
          ∑key∈commonGeometryBins s modifier R seed K Z ξ,E key/(1+dyadicScale key.1)^decay := by
  obtain ⟨J,hJ⟩:=product_height_extension τ extra target hτ smallDegree
  obtain ⟨C,hC,hphysical⟩:=actual_physical_mass_from_balanced_budgets (ι:=ι) W decay J J hc hsm
  refine ⟨J,C,hC,?_⟩
  intro s modifier R seed K Z ξ B M A external Cs Cc hK hZ hs hz₁ hz₂ hsource he hCs hCc E H hE hH hsmall hcoarse
  have hZ0:0<Z:=zero_lt_one.trans hZ
  let factor:=(Cs+Cc)*external^J*Z^target
  have hf:0≤factor:=by dsimp [factor];positivity
  have hh:=hphysical s modifier R seed K Z ξ B M A hK hZ hs hz₁ hz₂ hsource
    (fun key=>factor*E key) H (fun key hk=>mul_nonneg hf (hE key hk)) hH (by
      intro key hk reflected t u
      have hb:0≤(if reflected then E key/H key else E key*H key):=by
        split_ifs
        · exact div_nonneg (hE key hk) (hH key hk).le
        · exact mul_nonneg (hE key hk) (hH key hk).le
      have hext:=hJ (balancedLiveBudget reflected s modifier R seed K Z ξ M A hK key
        (fun q=>normPhase (coordinateBlock s modifier R seed W K Z ξ q)))
        Z external 0 (if reflected then E key/H key else E key*H key) Cs Cc s.t reflected
        hZ.le he hb hCs hCc
        (by simpa only [zero_add] using hsmall key hk reflected)
        (by simpa only [zero_add] using hcoarse key hk reflected) t u
      apply hext.trans_eq
      dsimp [factor]
      cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true,zero_add] <;> ring)
  apply hh.trans_eq
  rw [Real.rpow_add hZ0]
  simp only [mul_div_assoc,←Finset.mul_sum]
  dsimp [factor]
  ring

end
end QRH.Record1252270103Source.FirstTruncatedHeights
#print axioms QRH.Record1252270103Source.FirstTruncatedHeights.balance_payment
#print axioms QRH.Record1252270103Source.FirstTruncatedHeights.product_height_extension
#print axioms QRH.Record1252270103Source.FirstTruncatedHeights.TruncatedBudget
#print axioms QRH.Record1252270103Source.FirstTruncatedHeights.physical_from_truncated_budgets
