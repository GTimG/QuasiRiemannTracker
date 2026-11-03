/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighPrincipalLowRemainder.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIHighPrincipalOrdered
import Submissions.crossnox_perturbed_boundary.OAIHighPrincipalScale

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory Set
namespace SevenEighths.ProbePrincipalRemainderBounds
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal HeckeFamily.O

theorem source_remainders_power_bound_on_perturbed_boundary {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a e lengthShift : ℝ) (ha : a∈Icc PrincipalSlotEstimate.perturbedBoundary 2)
    (hβ : HeckeZeroSupremum.beta<a) (he : 0<e) (hehi : e≤5/6) :
    ∃C : ℝ,0<C ∧ ∀(ell : ι→ℝ),(∑j∈J,ell j=1/6+lengthShift) →
    ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,0<Z→
    (∀j∈J,480≤c*Z^(ell j)) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j)) →
    let K0 := fun s=>sourceMultiplier W0 W1 (Z^(AsymmetricGeometry.xBase-lengthShift/2:ℝ))
      (Z^(AsymmetricGeometry.yBase-lengthShift/2:ℝ)) Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=>Z^(ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral a (fun s=>verticalIntegral (1/6+e) (fun z=>verticalIntegral (19/20)
      (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*Z^(a+AsymmetricGeometry.signalOffset+AsymmetricGeometry.rowBase*e-AsymmetricGeometry.yBase/20+
        lengthShift*(1/40+3*e/2))) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=>verticalIntegral (33/200)
      (fun z=>K0 s 1 z*LFunction π (6*z)))‖≤
        C*Z^(a+AsymmetricGeometry.signalOffset-AsymmetricGeometry.rowBase/600-lengthShift/400)) := by
  obtain ⟨C,hC,hbound⟩ := ordered_remainders_scale_bound_on_perturbed_boundary η S hS hTail J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a e ha hβ he hehi
  refine ⟨C,hC,?_⟩
  intro ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound W hW hsupp (fun j=>Z^(ell j))
    (fun _ _=>Real.rpow_pos_of_pos hZ _) hthreshold hmod T hT
    (Z^(AsymmetricGeometry.xBase-lengthShift/2:ℝ)) (Z^(AsymmetricGeometry.yBase-lengthShift/2:ℝ)) Z
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hZ
  dsimp only at hh
  rw [perturbed_source_w_scale_identity J ell lengthShift Z a e hell hZ,
    perturbed_source_z_scale_identity J ell lengthShift Z a hell hZ] at hh
  exact hh

theorem source_remainders_strict_saving_on_perturbed_boundary {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (e lengthShift : ℝ) (he : 0<e) (hehi : e≤1/1000)
    (hβlo : PrincipalSlotEstimate.perturbedBoundary < HeckeZeroSupremum.beta)
    (ht : 0 ≤ lengthShift) (ht' : lengthShift ≤ 1/1000) :
    ∃C : ℝ,0<C ∧ ∀(ell : ι→ℝ),
      (∑j∈J,ell j=1/6+lengthShift) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) →
    ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,1≤Z→
    (∀j∈J,480≤c*Z^(ell j)) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j)) →
    let K0 := fun s=>sourceMultiplier W0 W1
      (Z^(AsymmetricGeometry.xBase-lengthShift/2:ℝ)) (Z^(AsymmetricGeometry.yBase-lengthShift/2:ℝ)) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ))
        (fun j=>Z^(ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral (HeckeZeroSupremum.beta+e)
      (fun s=>verticalIntegral (1/6+e) (fun z=>verticalIntegral (19/20)
        (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*Z^(HeckeZeroSupremum.beta+AsymmetricGeometry.signalOffset-1/3000)) ∧
    (‖HeckeReciprocal.regularizedL π 1 *
      verticalIntegral (HeckeZeroSupremum.beta+e)
      (fun s=>verticalIntegral (33/200)
        (fun z=>K0 s 1 z*LFunction π (6*z)))‖≤
      C*Z^(HeckeZeroSupremum.beta+AsymmetricGeometry.signalOffset-1/3000)) := by
  obtain ⟨C,hC,hbound⟩ := source_remainders_power_bound_on_perturbed_boundary
    η S hS hTail J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 (HeckeZeroSupremum.beta+e) e lengthShift
    ⟨by linarith, by linarith [HeckeZeroSupremum.beta_le_one]⟩
    (by linarith) he (by linarith)
  refine ⟨C,hC,?_⟩
  intro ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound ell hell W hW hsupp T hT Z (by linarith)
    hthreshold hmod
  dsimp only at hh
  have hw := perturbed_source_w_strict_exponent HeckeZeroSupremum.beta
    e lengthShift hehi ht ht'
  have hz := perturbed_source_z_strict_exponent HeckeZeroSupremum.beta
    e lengthShift hehi ht
  have hw' : (HeckeZeroSupremum.beta+e)+AsymmetricGeometry.signalOffset+AsymmetricGeometry.rowBase*e-AsymmetricGeometry.yBase/20+
      lengthShift*(1/40+3*e/2) ≤
      HeckeZeroSupremum.beta+AsymmetricGeometry.signalOffset-1/3000 := by linarith
  have hz' : (HeckeZeroSupremum.beta+e)+AsymmetricGeometry.signalOffset-AsymmetricGeometry.rowBase/600-lengthShift/400 ≤
      HeckeZeroSupremum.beta+AsymmetricGeometry.signalOffset-1/3000 := by linarith
  constructor
  · exact hh.1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hw')
      (div_nonneg hC.le he.le))
  · exact hh.2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hz') hC.le)


end SevenEighths.ProbePrincipalRemainderBounds
end

end OAI
