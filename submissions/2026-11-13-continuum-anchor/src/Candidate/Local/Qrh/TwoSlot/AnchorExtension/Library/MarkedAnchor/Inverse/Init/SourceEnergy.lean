/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
/- Adapted from openai_baseline `OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferenceSourceEnergy.lean`
(Apache-2.0). Modified by Sil (2026-11-11): the native gates (`gap`, `r+2S ≤ m-2gap`,
`2r+8S ≤ 3m-2gap`) are replaced by the parent rectangle `0 ≤ r ≤ Pmax`, `S ≤ Smax`, `1 ≤ m` and
the canonical oracle on `InitState Pmax Smax κ`; the slot filter `Adm` is required of the
pool-reindexed, conjugated, log-phase twisted coefficients; the lower live-width bound is proved
from `eta ≤ lag`. Proof otherwise unchanged. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Init.ResidualUniform
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceSourceEnergy

/-! # Inverse.Init.SourceEnergy — tenth file of the oracle-parametric initialization chain (`original_source_energy_of_oracle`):
the physical marked inverse source energy on the parent rectangle from the canonical oracle. -/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths
open DetectorDictionaryInverseMarkedReference
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalCoefficientClass ConcreteTraceCRT InverseInitialRayAttachment InverseMoment InverseInitialProfile
open InverseInitialOverlapFourier InverseInitialConjugateEnergy InverseInitialQuotientGeometry
open InverseInitialEnergyCallerWindow InverseInitialPoissonBridge InverseInitialPhysicalMeasure
open InverseInitialMarkedAssignedGeometry DetectorDictionaryInverseRawConjugateGates
local notation "O"=>HeckeFamily.O

private theorem assigned_admissible_clone {ι:Type}[Fintype ι][DecidableEq ι]
    (L:ι→Finset (Ideal O))(hp:∀i,∀P∈L i,Prime P)
    (hs:∀i,∀P∈L i,Supported P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J):Admissible (assignedIdeal L J x) := by
  apply tuple_admissible (fun i:↥J=>L i.val)
    (fun i=>hp i.val) (fun i=>hs i.val) _ x
  intro i hi j hj hij
  exact hdis (Finset.mem_univ _) (Finset.mem_univ _)
    (fun he=>hij (Subtype.ext he))

theorem original_source_energy_of_oracle
    (W:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (Adm:SlotAdm)(Pmax Smax κ Lp:ℝ)
    (eps π eta τ loss:ℝ)(heps:0<eps)(hπ:0<π)
    (heta:0<eta)(hetaone:eta≤1)(hτ:0<τ)(hκ:8*eta+τ≤κ)(hLp:Lp≤3)
    (hloss:0<loss)(K:ℕ)
    (horacle:∀(Wf:𝓢(ℝ,ℂ))(lf hf:ℝ),0<lf→lf≤hf→Function.support (Wf:ℝ→ℂ)⊆Set.Icc lf hf→
      GoodEnergyExists Adm (InitState Pmax Smax κ) eps Lp K Wf):
    ∀q:ℕ,q≠0→∃(degree:ℕ)(C U₀:ℝ),0<C ∧ 1<U₀ ∧
    ∀U:ℝ,U₀≤U→(2:ℝ)^K≤U^eta→
    ∀{ι:Type}[Fintype ι][DecidableEq ι],Fintype.card ι≤K→
    ∀(L:ι→Finset (Ideal O))(ell:ι→ℝ)(coeff:ι→Ideal O→ℂ),
      (∀i,0≤ell i)→(∀i,∀P∈L i,Prime P)→
      (∀i,∀P∈L i,Supported P)→
      (((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)→
      (∀i,∀P∈L i,((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2)→
      (∀i,∀P∈L i,‖coeff i P‖≤1)→
      (∀i,∀P∈L i,InverseInitialExcludedPool.outside (reflectionExcludedPrimes q) P)→
    ∀(primeW:ι→ℝ→ℂ),
      (∀i,Function.support (primeW i)⊆Set.Icc (1:ℝ) 2)→
      (∀i,∀P∈L i,primeW i ((P.absNorm:ℝ)/U^(ell i))≠0)→
    ∀χ:Ideal O→*ℂ,(∀I,‖χ I‖≤1)→
      FactorsModulo (fixedBaseConductor q) (elementCharacter (conjugateIdealCharacter χ))→
      (∀I,¬InverseInitialExcludedPool.outside (reflectionExcludedPrimes q) I→
        conjugateIdealCharacter χ I=0)→
    ∀hv:ℝ,0≤hv→
      (∀(J:Finset ι)(Dpool:ℕ)(t:ℝ),Adm q Dpool ι (Finset.univ\J)
        (fun i=>InverseInitialCommonLists.poolList
          (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool) (L i))
        (fun i=>2*U^(ell i))
        (fun i P=>star (coeff i P.val)*FourierBridge.logPhase (-t)
          (Real.log (InverseInitialCommonProfile.slotRatio U ell i P.val))) U (hv+|t|))→
    ∀m r:ℝ,0≤m→m≤2→
      (∀J:Finset ι,-2≤r+(∑i,ell i)-2*(∑i∈J,ell i))→
      0≤Pmax→ r≤Pmax→(∑i,ell i)≤Smax→1≤m→
      r+(∑i,ell i)+7*eta≤2→
    ∀rows:Finset O,(∀u∈rows,‖eisEmbedding u‖^2≤U^m)→∀θ:ℝ,
      (∑u∈rows,‖∑x:Tuple L,(∏i,coeff i (x i).val)*
        originalTotalPolynomial (originalSource U r bo) (∏i,(x i).val) χ (fun _=>1)
          (childLogTest W θ) U r (∑i,ell i) u‖^2)≤
      C*(1+hv)^(2*degree)*U^(m+15*eta+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  have hsstar:Function.support (fun x=>star (W x))⊆Set.Icc ao bo := by
    intro x hx
    exact hsW (by simpa using hx)
  have henergy:=original_residual_uniform_energy_of_oracle
    (fun x=>star (W x)) ao bo hao hab hsstar (Complex.conjCLE.contDiff.comp hW)
    DetectorDictionaryInverseMarkedPadding.radialMajorant
    DetectorDictionaryInverseMarkedPadding.radialMajorant_nonneg
    DetectorDictionaryInverseMarkedPadding.radialMajorant_one
    Adm Pmax Smax κ Lp 2 eps π eta τ loss (by norm_num) heps hπ heta hetaone hτ hκ hloss K
    (by linarith) horacle
  intro q hq
  obtain ⟨degree,C,U₀,hC,hU₀,henergy⟩:=henergy q hq
  let A:ℝ:=((2:ℝ)^K*DetectorDictionaryInverseAssignedCount.assignedConstant K 2)^2
  have hA:0<A:=sq_pos_of_pos (mul_pos (by positivity)
    (DetectorDictionaryInverseAssignedCount.assignedConstant_pos K (by norm_num)))
  refine ⟨degree,A*C,U₀,mul_pos hA hC,hU₀,?_⟩
  intro U hU hpow ι inst dec hK L ell coeff hell hp hs hdis hratio hc hout primeW hprimeW hlive
    χ hχ hperiod hzero hv hv0 hadm m r hm hmcap hD hr0 hrP hSm hm1 hparent rows hrows θ
  have hUone:1<U:=hU₀.trans_le hU
  have hUpos:0<U:=zero_lt_one.trans hUone
  have hscale (i:ι):0<U^(ell i):=Real.rpow_pos_of_pos hUpos _
  have hnorm (i:ι)(P:Ideal O)(hP:P∈L i):(P.absNorm:ℝ)≤2*U^(ell i):=
    (div_le_iff₀ (hscale i)).mp (hratio i P hP).2
  let E:ℝ:=C*(1+hv)^(2*degree)*U^(m+15*eta+π+eps+loss)*((1+‖θ‖)^degree)^2
  have hE:0≤E:=by dsimp [E];positivity
  have hlowJ (J:Finset ι) :
      U^(InverseInitialQuotientGeometry.assignedCenter (Finset.univ\J) ell)≤
        ∏i∈Finset.univ\J,2*U^(ell i) := by
    unfold InverseInitialQuotientGeometry.assignedCenter
    rw [Real.rpow_sum_of_pos hUpos]
    gcongr with i hi
    have := Real.rpow_nonneg hUpos.le (ell i)
    linarith
  have hHlowJ (J:Finset ι) : ∀i∈Finset.univ\J,∀P∈L i,2*U^(ell i)≤2*(P.absNorm:ℝ) := by
    intro i _ P hP
    have h1 := (hratio i P hP).1
    rw [le_div_iff₀ (hscale i), one_mul] at h1
    linarith
  have hres (J:Finset ι)(x:Assigned L J):
      (∑u∈rows,(1:ℝ)*‖remainingPolynomial (originalSource U r bo) L J x coeff χ
        (childLogTest W θ) U r (∑i,ell i) (∑i∈J,ell i) u‖^2)≤E := by
    have hJ:J.card≤K:=(Finset.card_le_univ J).trans hK
    have hH (i:ι):1≤2*U^(ell i) := by
      have hh:=Real.one_le_rpow hUone.le (hell i)
      linarith
    have hprod (T:Finset ι):
        (∏i∈T,2*U^(ell i))≤U^((∑i∈T,ell i)+eta) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,←Real.rpow_sum_of_pos hUpos,
        Real.rpow_add hUpos]
      rw [mul_comm (U^(∑i∈T,ell i))]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hUpos.le _)
      exact (pow_le_pow_right₀ (by norm_num) ((Finset.card_le_univ T).trans hK)).trans hpow
    have hje:Admissible (assignedIdeal L J x):=assigned_admissible_clone L hp hs hdis J x
    have hh:=henergy U hU Finset.univ J (Finset.subset_univ _) (by simpa using hK)
      L (fun i=>2*U^(ell i)) (fun i P=>star (coeff i P)) hdis
      (fun i _=>hH i) (fun i _=>hnorm i)
      (fun i _ P hP=>by simpa using hc i P hP)
      (assignedGenerator L J x) ell (fun _=>1) (fun _=>2) primeW
      (fun i _=>hell i)
      (assignedGenerator_ne_zero L J x (fun i _ P hP=>(hp i P hP).ne_zero))
      (fun i _=>hprimeW i) (assignedGenerator_window_live L J x U ell primeW (fun i _=>hlive i))
      (conjugateIdealCharacter χ)
      (fun u=>by simpa [elementCharacter,conjugateIdealCharacter] using hχ (Ideal.span {u}))
      hperiod hzero (r+(∑i,ell i)-2*(∑i∈J,ell i)) m r hm hmcap (hD J)
      (by simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hJ).trans hpow)
      (by simpa [assignedCenter] using hprod (Finset.univ\J))
      (hlowJ J) (hHlowJ J) hpow rfl hr0 hrP (by simpa [assignedCenter] using hSm) hm1
      (by simpa [assignedCenter] using hparent) rows hrows (assignedIdeal L J x) hje
      (assignedElement_span L J x)
      (assigned_ratio_interval L J x U hUpos ell K hJ (fun i _=>hratio i))
      (fun i _=>hp i) (fun i _ P hP _=>hratio i P hP)
      (remaining_tuple_admissible L hp hs hdis J x)
      (remaining_tuple_coprime L hp hdis J)
      (remaining_tuple_outside L (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)
        hout J x) hv hv0 (hadm J) (-θ)
    simpa only [one_mul,remainingPolynomial_original_pi,childLogTest_conjugate,
      assignedCenter,norm_neg,E] using hh
  have hb:=original_energy_with_assigned_count K (by norm_num : (1:ℝ)≤2) hUone.le hK
    (originalSource U r bo) L hp hdis ell (fun i P hP=>⟨(hp i P hP).ne_zero,hnorm i P hP⟩)
    coeff hc χ (assigned_admissible_clone L hp hs hdis) (fun J x=>hχ _)
    (childLogTest W θ) r (∑i,ell i) rows (fun _=>1) (fun _=>zero_le_one) E hE hres
  simpa only [one_mul,E,A,mul_assoc] using hb

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.original_source_energy_of_oracle
