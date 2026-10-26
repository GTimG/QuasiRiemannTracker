/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
An attained weight ceiling is chosen separately on each genuine LOW cell.
Its radial and missing-ideal exponents remain attached to that same cell. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalHighMass
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalModifiedLowPayment
import Submissions.hailey_collet_1252270103.Record1252270103Source.LowErasure.Finite
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve Cycle61InitialMass Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentExceptionalAmplitudePair
open Record12518109Natural CenteredMomentAddedZeroUniform
open LowErasure
local notation "O"=>HeckeFamily.O

/-- This is a scalar maximum inside one nonempty cell, after the common
source constants have been selected. It is never a maximum across radii. -/
theorem low_cell_weight_payment {Row Slot:Type*} (rows:Finset Row) (hne:rows.Nonempty)
    (weight x₀ x₁ radial side:Row→ℝ) (w:Slot→ℝ) (T F:Finset Slot)
    (N:ℕ) (Z factor massLoss q Cslot εlow d M hi Bmissing εmask gapM gapH target extra:ℝ)
    (hZ:1<Z)(hfactor:0≤factor)(hC:1≤Cslot)(hε:0≤εlow)(hd:0≤d)(hm:0≤εmask)
    (hcard:(T\F).card≤N)(hhi:hi≤Bmissing)
    (hw:∀r∈rows,0≤weight r)
    (hweight:∀r∈rows,weight r≤factor*Z^(massLoss+x₀ r-side r))
    (hM:∀r∈rows,M≤radial r+gapM)(hH:∀r∈rows,hi≤x₁ r+gapH)
    (hprice:∀r∈rows,x₀ r+x₁ r+radial r-side r+q*∑j∈T\F,w j≤target) :
    ∃A:ℝ,0≤A ∧ (∀r∈rows,weight r≤A) ∧ (∃r∈rows,A=weight r) ∧
      A*erasurePayment Z q (Cslot*Z^(2*εlow*d)) w T F*Z^(M+hi*(1+εmask)+extra)≤
        factor*Cslot^N*Z^(target+massLoss+gapM+gapH+εmask*Bmissing+2*εlow*d*N+extra) := by
  classical
  obtain ⟨r,hr,hmax⟩:=Finset.exists_max_image rows weight hne
  refine ⟨weight r,hw r hr,hmax,⟨r,hr,rfl⟩,?_⟩
  have hZ0:=zero_lt_one.trans hZ
  have he:erasurePayment Z q (Cslot*Z^(2*εlow*d)) w T F=
      Cslot^(T\F).card*Z^(2*εlow*d*(T\F).card+q*∑j∈T\F,w j) := by
    unfold erasurePayment
    rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,Real.rpow_add hZ0]
    ring
  have hex:massLoss+x₀ r-side r+(2*εlow*d*(T\F).card+q*∑j∈T\F,w j)+
      (M+hi*(1+εmask)+extra)≤
      target+massLoss+gapM+gapH+εmask*Bmissing+2*εlow*d*N+extra := by
    have hc:(T\F).card≤(N:ℝ):=by exact_mod_cast hcard
    have hc':2*εlow*d*(T\F).card≤2*εlow*d*N:=
      mul_le_mul_of_nonneg_left hc (by positivity)
    have hm':εmask*hi≤εmask*Bmissing:=mul_le_mul_of_nonneg_left hhi hm
    linarith only [hprice r hr,hM r hr,hH r hr,hc',hm']
  rw [he]
  calc
    _≤(factor*Z^(massLoss+x₀ r-side r))*
        (Cslot^(T\F).card*Z^(2*εlow*d*(T\F).card+q*∑j∈T\F,w j))*Z^(M+hi*(1+εmask)+extra) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ0.le _)
      exact mul_le_mul_of_nonneg_right (hweight r hr) (by positivity)
    _=(factor*Cslot^(T\F).card)*Z^(massLoss+x₀ r-side r+
        (2*εlow*d*(T\F).card+q*∑j∈T\F,w j)+(M+hi*(1+εmask)+extra)) := by
      simp only [Real.rpow_add hZ0]
      ring
    _≤(factor*Cslot^N)*Z^(target+massLoss+gapM+gapH+εmask*Bmissing+2*εlow*d*N+extra) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC hcard) hfactor)
        (Real.rpow_le_rpow_of_exponent_le hZ.le hex)
        (Real.rpow_nonneg hZ0.le _) (mul_nonneg hfactor (pow_nonneg (by linarith) _))

/-- The actual modified first mass supplies the cell's weight ceiling. The
only price premise is the scalar coordinate inequality, discharged by the
checked LOW node payment. No norm or energy estimate is assumed here. -/
theorem actual_balanced_low_cell_payment {α Row:Type} [Fintype α]
    (reflected:Bool)(s:Input α)(modifier:Tuple α→ℂ)(R seed:Ideal O)
    (W:𝓢(ℝ,ℂ))(D Z ξ B εmass lo ap:ℝ)(N:ℕ)(hZ:1<Z)(hK:0<Z^D)
    (hεmass:0≤εmass)(hN:Fintype.card α≤N)(hlo:0<lo)(hap:0<ap)(hlower:lo≤s.lower)
    (hseed:Squarefree seed)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(hsource:sourceRadius s≤Z^B)
    (hs₁:∀x,s.W₁ x≠0→ap≤x)(hs₂:∀x,s.W₂ x≠0→ap≤x)
    (bin:ℤ×(Fin 5→ℤ))
    (column:Row→FirstColumnIndex (CoupledFirst.geometryFirstSource s modifier R seed (Z^D) Z ξ hK bin))
    (rows:Finset Row)(hne:rows.Nonempty)(x:Row→Fin 4→ℝ)(coeff radial:Row→ℝ)
    (w:α→ℝ)(T F:Finset α)
    (q Cslot εlow d M hi Bmissing εmask gapM gapH target extra:ℝ)
    (hC:1≤Cslot)(hεlow:0≤εlow)(hd:0≤d)(hmask:0≤εmask)
    (hcard:(T\F).card≤N)(hhi:hi≤Bmissing)
    (hcoeff₀:∀r∈rows,0≤coeff r)(hcoeff:∀r∈rows,coeff r≤Z^(x r 0))
    (hM:∀r∈rows,M≤radial r+gapM)(hH:∀r∈rows,hi≤x r 1+gapH)
    (hprice:∀r∈rows,x r 0+x r 1+radial r-
      balancedGeometrySide reflected (Real.logb Z (volume s.toData))
        (CoupledFirst.geometryExponents s modifier R seed (Z^D) Z ξ (column r).1.val)+
          q*∑j∈T\F,w j≤target) :
    ∃A:ℝ,0≤A ∧
      (∀r∈rows,CoupledFirst.balancedFirstHighMass reflected s modifier R seed W D Z ξ εmass hK bin (column r)*coeff r≤A) ∧
      (∃r∈rows,A=CoupledFirst.balancedFirstHighMass reflected s modifier R seed W D Z ξ εmass hK bin (column r)*coeff r) ∧
      A*erasurePayment Z q (Cslot*Z^(2*εlow*d)) w T F*Z^(M+hi*(1+εmask)+extra)≤
        geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Cslot^N*
          Z^(target+B*εmass+gapM+gapH+εmask*Bmissing+2*εlow*d*N+extra) := by
  have hf:0≤geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin := by
    cases reflected <;> simp only [geometryHighFactor]
    · exact mul_nonneg (by positivity) (geometryDCompensator_pos bin).le
    · exact inv_nonneg.mpr (geometryDCompensator_pos bin).le
  apply low_cell_weight_payment rows hne
    (fun r=>CoupledFirst.balancedFirstHighMass reflected s modifier R seed W D Z ξ εmass hK bin (column r)*coeff r)
    (fun r=>x r 0) (fun r=>x r 1) radial
    (fun r=>balancedGeometrySide reflected (Real.logb Z (volume s.toData))
      (CoupledFirst.geometryExponents s modifier R seed (Z^D) Z ξ (column r).1.val))
    w T F N Z (geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin)
    (B*εmass) q Cslot εlow d M hi Bmissing εmask gapM gapH target extra
    hZ hf hC hεlow hd hmask hcard hhi
    (fun r hr=>mul_nonneg (CoupledFirst.balanced_first_high_mass_nonneg ..) (hcoeff₀ r hr))
    ?_ hM hH hprice
  intro r hr
  have hm:=CoupledFirst.actual_balanced_uniform_high_mass reflected N lo ap hlo hap s modifier R seed
    W D Z ξ B εmass hZ hK hεmass hN hlower hseed hz₁ hz₂ hsource hs₁ hs₂ bin (column r)
  have hh:=mul_le_mul hm (hcoeff r hr) (hcoeff₀ r hr) (by positivity)
  apply hh.trans_eq
  rw [Real.rpow_sub (zero_lt_one.trans hZ),Real.rpow_add (zero_lt_one.trans hZ)]
  ring

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.low_cell_weight_payment
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_balanced_low_cell_payment
