/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
H23 Cauchy on one actual frozen row subclass, and the authentic shorter
ordinary upper inherited from the buffered source selected on those rows. -/
import Candidate.C092.transport.MediumInversePriceNative
import Candidate.C092.transport.MediumInversePriceCount
import Candidate.C092.transport.MediumReplaceNative

namespace QRH.Cycle092.MediumInversePrice
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators ContDiff
open Filter Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.MediumWitness QRH.Cycle092.MediumReplace

theorem sqrt_rpow (U x : ℝ) (hU : 0 < U) : Real.sqrt (U^x)=U^(x/2) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hU.le]
  congr 1
  ring

/-- Exact finite Cauchy price. All three estimates concern precisely s.
Repeating a genuine attaining descriptor allows a negative marked debit. -/
theorem same_rows_price {Index : Type*} (s : Finset Index) (A B Q : Index → ℂ)
    (U V ν y e L retained deficit countLoss momentLoss shortLoss Cc Cm Cy : ℝ)
    (hU : 0 < U) (hCc : 0 ≤ Cc) (hCm : 0 ≤ Cm) (hCy : 0 ≤ Cy)
    (hc : (s.card : ℝ) ≤ Cc*U^(V*(1-deficit)+countLoss))
    (hm : (∑ i ∈ s, ‖A i‖^4) ≤ Cm*U^(V-e*retained+momentLoss))
    (hy : ∀ i ∈ s, ‖B i‖^2 ≤ Cy*U^(ν*y+shortLoss))
    (hq : ∀ i ∈ s, ‖Q i‖^2 ≤ U^(e*L)) :
    (∑ i ∈ s, ‖A i*B i*Q i‖^2) ≤
      Cy*Real.sqrt Cc*Real.sqrt Cm*
        U^(V+ν*y+e*(L-retained/2)-V*deficit/2+
          shortLoss+(countLoss+momentLoss)/2) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s (fun _ => (1 : ℝ)) (fun i => ‖A i‖^2)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,←pow_mul] at hcs
  have hsum : (∑ i ∈ s, ‖A i‖^2) ≤
      Real.sqrt (Cc*U^(V*(1-deficit)+countLoss))*Real.sqrt (Cm*U^(V-e*retained+momentLoss)) :=
    hcs.trans (mul_le_mul (Real.sqrt_le_sqrt hc) (Real.sqrt_le_sqrt hm)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  calc
    _ ≤ (Cy*U^(ν*y+shortLoss)*U^(e*L))*(∑ i ∈ s, ‖A i‖^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      simp only [norm_mul,mul_pow]
      have h := mul_le_mul (hy i hi) (hq i hi) (sq_nonneg _) (by positivity)
      have h' := mul_le_mul_of_nonneg_left h (sq_nonneg ‖A i‖)
      convert h' using 1 <;> ring
    _ ≤ (Cy*U^(ν*y+shortLoss)*U^(e*L))*
        (Real.sqrt (Cc*U^(V*(1-deficit)+countLoss))*Real.sqrt (Cm*U^(V-e*retained+momentLoss))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      rw [Real.sqrt_mul hCc,Real.sqrt_mul hCm,sqrt_rpow U _ hU,sqrt_rpow U _ hU]
      have he : V+ν*y+e*(L-retained/2)-V*deficit/2+shortLoss+(countLoss+momentLoss)/2 =
          (ν*y+shortLoss)+(e*L)+(V*(1-deficit)+countLoss)/2+(V-e*retained+momentLoss)/2 := by ring
      rw [he]
      simp only [Real.rpow_add hU]
      ring

variable [Geometry.Parameters]

/-- Uniform shorter-factor control on arbitrary further restrictions of the
original Batch's selected medium rows. The physical polynomial, profile,
pitch, mask and buffered zero band are the original ones. -/
theorem original_short_on_rows (D : BaselineData) (F : BaselineSourceData D)
    (τ : ℝ) (hτ : 0 < τ) (hheight : 4*τ < (1/200 : ℝ)*D.cost)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0 ≤ profileBound k) :
    ∃ order : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (η : Character) (n : ℕ),
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (padding d threshold lowPay y : ℝ) (idx grid : FreeRow → ℕ),
      (1/200 : ℝ) ≤ d → d ≤ 7/8 → 0 ≤ y → y/d ≤ 22 →
      ProbeAssembly.selected D F padding τ n η Z idx grid →
    ∀ (i k : ℕ) (z : FreeRow → Fin D.N → ℂ) (s : Finset FreeRow),
      s ⊆ sharedRows D F (Z^(Geometry.h+padding)) Z d threshold lowPay idx grid z i k →
    ∀ S : ShortDataOn D F η Z τ d y idx grid order profileBound s,
    ∀ u ∈ s, ‖S.value u‖^2 ≤ C*Z^((2*bandLower D k-1)*y+d*D.ε) := by
  obtain ⟨order,C,hC,hupper⟩ := original_short_upper D F τ hτ hheight profileBound hprofile
  refine ⟨order,C,hC,?_⟩
  intro η n
  filter_upwards [hupper η n] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro padding d threshold lowPay y idx grid hd hd' hy hy' hsel i k z s hs S u hu
  have hrow := Finset.mem_filter.mp (hs hu)
  have hk : grid u=k := hrow.2.2.2.2.2
  have hdpos : 0 < d := (by norm_num : (0 : ℝ)<1/200).trans_le hd
  have hZpos : 0 < Z := zero_lt_one.trans hZ.1
  have hup := hZ.2 padding d (Z^(Geometry.h+padding)) idx grid hd hd' hsel u hrow.1
    hrow.2.1 hrow.2.2.1 (S.label u) (S.profile u) (S.lower u) (S.upper u) (y/d)
    (S.sigma u) (S.frequency u) (S.lower_pos u hu) (S.support u hu) (S.smooth u hu)
    (div_nonneg hy hdpos.le) hy' (S.frequency_bound u hu) (S.mellin_two u hu) (S.mellin_order u hu)
  have hscale : (Z^d)^(y/d)=Z^y := by
    rw [←Real.rpow_mul hZpos.le,mul_div_cancel₀ _ hdpos.ne']
  rw [hscale,←Real.rpow_mul hZpos.le] at hup
  have hex : d*((2*(51/100+D.e*grid u)-1)*(y/d)+D.ε)=
      (2*bandLower D k-1)*y+d*D.ε := by rw [hk];unfold bandLower;field_simp [hdpos.ne']
  simpa only [hex,ShortDataOn.value] using hup

#print axioms same_rows_price
#print axioms original_short_on_rows
end
end QRH.Cycle092.MediumInversePrice
