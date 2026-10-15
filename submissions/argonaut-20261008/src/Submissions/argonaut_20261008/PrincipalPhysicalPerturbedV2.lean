import Submissions.argonaut_20261008.PrincipalRemainderPowersPerturbedV2
import Submissions.argonaut_20261008.PrincipalTransportSigmaV2
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalPhysical
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalNormalized

namespace OAI.SevenEighths.LocalPrincipalPhysicalV2
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

/- Complete physical decomposition and remainder proof bodies. NOT_RUN;
full Sigma contour/transport/generic-bound bodies are supplied as V2 candidates. -/
theorem principal_physical_pool_ordered_v2 {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusionsSigma S)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (b : Fin K→PrimeIdeal→ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : analyticBoundaryB0<a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e) (he2 : e≤11/6) :
    let F := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η Finset.univ T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    (∑P : (∀i,T i),(∏i,b i (P i).val)*
      principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z)=
      verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
        (fun w => F s w z*LFunction π (6*z)*LFunction π w)))+
      R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => F s 1 z*LFunction π (6*z)))+
      R^2/6*verticalIntegral a (fun s => F s 1 (1/6)) := by
  dsimp only
  rw [principal_physical_pool_initial η S hS.toSourceExclusions T hT hdis b W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  exact LocalPrincipalTransportV2.source_initial_joint_ordered_at_a_pc2 η S hS Finset.univ T b
    (fun i _ p hp=>hT i p hp) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2

theorem physical_principal_residue_remainder_v2 {K : ℕ}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (hTail : CorrectionTailSigma S)
    (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (e : ℝ) (he : 0<e) (hehi : e≤1/1000)
    (ha : analyticBoundaryB0<HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ell : Fin K→ℝ,(∑j,ell j)=E → ∀W : Fin K→ℝ→ℝ,
    (∀j x,0≤W j x ∧ W j x≤B) → (∀j,Function.support (W j)⊆Set.Icc c d) →
    ∀T : Fin K→Finset PrimeIdeal,(∀j p,p∈T j→p.val∉S) →
    (∀P:(∀j,T j),Function.Injective (fun j=>(P j).val)) →
    ∀Z : ℝ,1≤Z → (∀j,480≤c*Z^(ell j)) → (∀j,(Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j)) →
    ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^lx) (Z^ly) Z)-
      sourceResidueIntegral W0 W1 (∏p∈S,p) (η.excludePrimes S hS.prime)
        (HeckeZeroSupremum.beta+e) (Z^lx) (Z^ly) Z
        (globalClosedCorrection η S)
        (windowMultiplier η Finset.univ T (fun j x=>(W j x:ℂ)) (fun j=>Z^(ell j)))‖≤
      C/e*Z^(HeckeZeroSupremum.beta-11/16-17/48000) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := LocalPrincipalRemainderV2.source_remainders_strict_saving_v2 η S hS hTail
    (Finset.univ : Finset (Fin K)) c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ⟨ha.le,ha2⟩
  refine ⟨2*C,by positivity,?_⟩
  intro ell hell W hW hsupp T hT hdis Z hZ hthreshold hmod
  have hZ0 : 0<Z := by linarith
  have hb := hbound ell hell W (fun j _=>hW j) (fun j _=>hsupp j) T (fun j _ p hp=>hT j p hp)
    Z hZ (fun j _=>hthreshold j) (fun j _=>hmod j)
  dsimp only at hb
  have hSigma : SourceExclusionsSigma S := ⟨hS.prime, hS.bad, hTail⟩
  have heq := principal_physical_pool_ordered_v2 η S hSigma T hT hdis
    (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/Z^(ell j)):ℂ)) W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 (Z^lx) (Z^ly) Z (HeckeZeroSupremum.beta+e) e
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0 ha (by linarith) (by linarith) he (by linarith)
  dsimp only at heq
  have hres (F : ℂ→ℂ) :
      (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)^2/6*
        verticalIntegral (HeckeZeroSupremum.beta+e) F=
      verticalIntegral (HeckeZeroSupremum.beta+e) (fun s=>fixedPrincipalResidue (∏p∈S,p)^2/6*F s) := by
    rw [verticalIntegral,verticalIntegral,integral_const_mul]
    dsimp only [fixedPrincipalResidue,fixedPrincipal,fixedSourcePrincipal]
    ring
  rw [heq]
  unfold sourceResidueIntegral windowMultiplier
  rw [hres,add_sub_cancel_right]
  have hn := (norm_add_le _ _).trans (add_le_add hb.1 hb.2)
  change _≤(2*C)/e*Z^(HeckeZeroSupremum.beta-11/16-17/48000)
  apply hn.trans
  have hCe : C≤C/e := (le_div_iff₀ he).mpr (by nlinarith)
  have hzpow : 0≤Z^(HeckeZeroSupremum.beta-11/16-17/48000) := Real.rpow_nonneg hZ0.le _
  have htwo : (2*C)/e=2*(C/e) := by ring
  rw [htwo]
  nlinarith

end
end OAI.SevenEighths.LocalPrincipalPhysicalV2
