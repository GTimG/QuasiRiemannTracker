import Submissions.argonaut_20261008.PrincipalGeometryPerturbedV2
import Submissions.argonaut_20261008.PrincipalSameSCutoffsV2
import Submissions.argonaut_20261008.PrincipalGenericRemaindersSigmaV2
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalNormalized

namespace OAI.SevenEighths.LocalPrincipalRemainderV2
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Filter Set MeasureTheory Asymptotics
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
open ProbeRaySlots ProbePrincipalPhysical ProbePrincipalNormalized
open PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal
open ProbeMellinBoundary ProbePrincipalContours
open LocalPrincipalGeometryV2 LocalPrincipalCutoffsV2
local notation "Id" => Ideal HeckeFamily.O

/- Full proof bodies, NOT_RUN. The generic ordered bound is
ported in PrincipalGenericRemaindersSigmaV2 with Sigma evidence and complete official binders.
No final remainder estimate is an assumed theorem argument. -/
theorem source_remainders_power_bound_v2 {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (hTail : CorrectionTailSigma S)
    (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a e : ℝ) (ha : a∈Icc (analyticBoundaryB0:ℝ) 2) (hβ : HeckeZeroSupremum.beta<a)
    (he : 0<e) (hehi : e≤5/6) :
    ∃C : ℝ,0<C ∧ ∀(ell : ι→ℝ),(∑j∈J,ell j=E) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,0<Z→
    (∀j∈J,480≤c*Z^(ell j)) → (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j)) →
    let K0 := fun s=>sourceMultiplier W0 W1 (Z^lx) (Z^ly) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=>Z^(ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral a (fun s=>verticalIntegral (1/6+e) (fun z=>verticalIntegral (19/20)
      (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*Z^(a-11/16+H*e-ly/20)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=>verticalIntegral (33/200)
      (fun z=>K0 s 1 z*LFunction π (6*z)))‖≤C*Z^(a-11/16-H/600)) := by
  have hSigma : SourceExclusionsSigma S := ⟨hS.prime, hS.bad, hTail⟩
  obtain ⟨C,hC,hbound⟩ := LocalPrincipalGenericRemainderV2.ordered_remainders_scale_bound_pc2 η S hSigma J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a e ha hβ he hehi
  refine ⟨C,hC,?_⟩
  intro ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound W hW hsupp (fun j=>Z^(ell j)) (fun _ _=>Real.rpow_pos_of_pos hZ _)
    hthreshold hmod T hT (Z^lx) (Z^ly) Z
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hZ
  dsimp only at hh
  rw [actual_w_scale_identity J ell hell Z a e hZ,actual_z_scale_identity J ell hell Z a hZ] at hh
  exact hh

theorem source_remainders_strict_saving_v2 {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (hTail : CorrectionTailSigma S)
    (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (e : ℝ) (he : 0<e) (hehi : e≤1/1000)
    (ha : HeckeZeroSupremum.beta+e∈Icc (analyticBoundaryB0:ℝ) 2) :
    ∃C : ℝ,0<C ∧ ∀(ell : ι→ℝ),(∑j∈J,ell j=E) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,1≤Z→
    (∀j∈J,480≤c*Z^(ell j)) → (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j)) →
    let K0 := fun s=>sourceMultiplier W0 W1 (Z^lx) (Z^ly) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=>Z^(ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral (HeckeZeroSupremum.beta+e) (fun s=>verticalIntegral (1/6+e)
      (fun z=>verticalIntegral (19/20) (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*Z^(HeckeZeroSupremum.beta-11/16-17/48000)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral (HeckeZeroSupremum.beta+e)
      (fun s=>verticalIntegral (33/200) (fun z=>K0 s 1 z*LFunction π (6*z)))‖≤
      C*Z^(HeckeZeroSupremum.beta-11/16-17/48000)) := by
  obtain ⟨C,hC,hbound⟩ := source_remainders_power_bound_v2 η S hS hTail J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 (HeckeZeroSupremum.beta+e) e ha (by linarith) he (by linarith)
  refine ⟨C,hC,?_⟩
  intro ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound ell hell W hW hsupp T hT Z (by linarith) hthreshold hmod
  dsimp only at hh
  constructor
  · exact hh.1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (w_strict_exponent HeckeZeroSupremum.beta e hehi))
      (div_nonneg hC.le he.le))
  · exact hh.2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (z_strict_exponent HeckeZeroSupremum.beta e hehi)) hC.le)

end
end OAI.SevenEighths.LocalPrincipalRemainderV2
