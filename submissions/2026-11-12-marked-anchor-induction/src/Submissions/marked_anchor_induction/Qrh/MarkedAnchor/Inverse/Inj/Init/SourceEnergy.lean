/- Copyright (c) 2026 Sil. Apache-2.0. -/
/- Adapted from openai_baseline `OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferenceSourceEnergy.lean`
(Apache-2.0), via `Inverse/Init/SourceEnergy.lean`. Modified by Sil (2026-11-12): injective tuples
on possibly overlapping lists (no `PairwiseDisjoint`); the injective Assigned × Remaining split of
`Inj/Dict`; the residual bound is the injective residual layer (`PiOK` remaining tuples, full lists,
injective height-aware oracle). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Inj.Dict.Energy
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Inj.Oracle
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Inj.Init.ResidualUniform
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceSourceEnergy

/-!
# Inverse.Inj.Init.SourceEnergy — the injective physical marked source energy

* `ResidualUniformInjConcl`: the conclusion of the injective residual layer
  (`Inj/Init/ResidualUniform`) = the conclusion of the disjoint
  `original_residual_uniform_energy_of_oracle` without `PairwiseDisjoint` and without the tuple
  coprimality hypothesis; the tuple sum and the two other tuple hypotheses run over
  `((all\assigned).pi L).filter (PiOK (all\assigned) j)`.
* `source_energy_inj_of_residual`: the `original_source_energy_of_oracle` statement for the
  INJECTIVE tuple sum `∑ x ∈ tupInj L` with no disjointness, from that conclusion.
* **`source_energy_inj`**: the same from the injective oracle `GoodEnergyExistsInj` on
  `InitState Pmax Smax κ` (via `original_residual_uniform_energy_of_oracle_inj`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Inj
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths
open DetectorDictionaryInverseMarkedReference
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalCoefficientClass ConcreteTraceCRT InverseInitialRayAttachment InverseMoment InverseInitialProfile
open InverseInitialOverlapFourier InverseInitialConjugateEnergy InverseInitialQuotientGeometry
open InverseInitialEnergyCallerWindow InverseInitialPoissonBridge InverseInitialPhysicalMeasure
open InverseInitialMarkedAssignedGeometry DetectorDictionaryInverseRawConjugateGates
open InverseInitialCommonLists InverseInitialCommonRatios InverseInitialExcludedPool
open InverseInitialCommonProfile
local notation "O" => HeckeFamily.O

/-- The conclusion of the injective residual layer (`Inj/Init/ResidualUniform`). -/
def ResidualUniformInjConcl (Woriginal : ℝ → ℂ) (bo : ℝ) (Adm : SlotAdm) (Pmax Smax : ℝ)
    (cap eps π η loss : ℝ) (K : ℕ) : Prop :=
    ∀q:ℕ,q≠0→∃(degree:ℕ)(C Z₀:ℝ),0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(L:σ→Finset (Ideal O))(Hslot:σ→ℝ)(coeff:σ→Ideal O→ℂ),
      (∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈L i,(P.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈L i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀χ:Ideal O→*ℂ,(∀u,‖elementCharacter χ u‖≤1)→
      FactorsModulo (fixedBaseConductor q) (elementCharacter χ)→
      (∀c,¬outside (reflectionExcludedPrimes q) c→χ c=0)→
    ∀(D m r:ℝ),0≤m→m≤cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      Z^(assignedCenter (all\assigned) z)≤(∏i∈all\assigned,Hslot i)→
      (∀i∈all\assigned,∀P∈L i,Hslot i≤2*(P.absNorm:ℝ))→(2:ℝ)^K≤Z^η→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      0≤Pmax→ r≤Pmax→assignedCenter all z≤Smax→1≤m→
      r+assignedCenter all z+7*η≤cap→
    ∀(rows:Finset O),(∀u∈rows,‖eisEmbedding u‖^2≤Z^m)→
    ∀(j:Ideal O),Admissible j→Ideal.span {assignedElement assigned qelem}=j→
      ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))∈Set.Icc (1:ℝ) ((2:ℝ)^K)→
      (∀i∈all\assigned,∀P∈L i,Prime P)→
      (∀i∈all\assigned,∀P∈L i,coeff i P≠0→slotRatio Z z i P∈Set.Icc (1:ℝ) 2)→
      (∀t∈((all\assigned).pi L).filter (PiOK (all\assigned) j),
        Admissible (j*survivingProduct (all\assigned) t))→
      (∀t∈((all\assigned).pi L).filter (PiOK (all\assigned) j),outside (reflectionExcludedPrimes q)
        (j*survivingProduct (all\assigned) t))→
    ∀hv:ℝ,0≤hv→
      (∀(Dpool:ℕ)(t:ℝ),Adm q Dpool σ (all\assigned)
        (fun i=>poolList (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool) (L i))
        Hslot (fun i P=>coeff i P.val*FourierBridge.logPhase (-t) (Real.log (slotRatio Z z i P.val))) Z (hv+|t|))→
    ∀θ:ℝ,
      (∑u∈rows,‖∑t∈((all\assigned).pi L).filter (PiOK (all\assigned) j),
        (∏i∈(all\assigned).attach,coeff i.val (t i.val i.property))*
        residualNormalizedPolynomial (originalSource Z r bo)
          (j*survivingProduct (all\assigned) t) j χ (fun _=>1)
          (childLogTest Woriginal θ) Z r (assignedCenter all z) (assignedCenter assigned z) u‖^2)≤
        C*(1+hv)^(2*degree)*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2

theorem source_energy_inj_of_residual
    (W:ℝ→ℂ)(bo:ℝ)
    (Adm:SlotAdm)(Pmax Smax:ℝ)
    (eps π eta loss:ℝ)(K:ℕ)
    (hresidual:ResidualUniformInjConcl (fun x=>star (W x)) bo Adm Pmax Smax 2 eps π eta loss K):
    ∀q:ℕ,q≠0→∃(degree:ℕ)(C U₀:ℝ),0<C ∧ 1<U₀ ∧
    ∀U:ℝ,U₀≤U→(2:ℝ)^K≤U^eta→
    ∀{ι:Type}[Fintype ι][DecidableEq ι],Fintype.card ι≤K→
    ∀(L:ι→Finset (Ideal O))(ell:ι→ℝ)(coeff:ι→Ideal O→ℂ),
      (∀i,0≤ell i)→(∀i,∀P∈L i,Prime P)→
      (∀i,∀P∈L i,Supported P)→
      (∀i,∀P∈L i,((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2)→
      (∀i,∀P∈L i,‖coeff i P‖≤1)→
      (∀i,∀P∈L i,outside (reflectionExcludedPrimes q) P)→
    ∀(primeW:ι→ℝ→ℂ),
      (∀i,Function.support (primeW i)⊆Set.Icc (1:ℝ) 2)→
      (∀i,∀P∈L i,primeW i ((P.absNorm:ℝ)/U^(ell i))≠0)→
    ∀χ:Ideal O→*ℂ,(∀I,‖χ I‖≤1)→
      FactorsModulo (fixedBaseConductor q) (elementCharacter (conjugateIdealCharacter χ))→
      (∀I,¬outside (reflectionExcludedPrimes q) I→
        conjugateIdealCharacter χ I=0)→
    ∀hv:ℝ,0≤hv→
      (∀(J:Finset ι)(Dpool:ℕ)(t:ℝ),Adm q Dpool ι (Finset.univ\J)
        (fun i=>poolList
          (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool) (L i))
        (fun i=>2*U^(ell i))
        (fun i P=>star (coeff i P.val)*FourierBridge.logPhase (-t)
          (Real.log (slotRatio U ell i P.val))) U (hv+|t|))→
    ∀m r:ℝ,0≤m→m≤2→
      (∀J:Finset ι,-2≤r+(∑i,ell i)-2*(∑i∈J,ell i))→
      0≤Pmax→ r≤Pmax→(∑i,ell i)≤Smax→1≤m→
      r+(∑i,ell i)+7*eta≤2→
    ∀rows:Finset O,(∀u∈rows,‖eisEmbedding u‖^2≤U^m)→∀θ:ℝ,
      (∑u∈rows,‖∑x∈tupInj L,(∏i,coeff i (x i).val)*
        originalTotalPolynomial (originalSource U r bo) (∏i,(x i).val) χ (fun _=>1)
          (childLogTest W θ) U r (∑i,ell i) u‖^2)≤
      C*(1+hv)^(2*degree)*U^(m+15*eta+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  intro q hq
  obtain ⟨degree,C,U₀,hC,hU₀,henergy⟩:=hresidual q hq
  let A:ℝ:=((2:ℝ)^K*DetectorDictionaryInverseAssignedCount.assignedConstant K 2)^2
  have hA:0<A:=sq_pos_of_pos (mul_pos (by positivity)
    (DetectorDictionaryInverseAssignedCount.assignedConstant_pos K (by norm_num)))
  refine ⟨degree,A*C,U₀,mul_pos hA hC,hU₀,?_⟩
  intro U hU hpow ι inst dec hK L ell coeff hell hp hs hratio hc hout primeW hprimeW hlive
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
  have hres (J:Finset ι)(x:Assigned L J)(hx:x∈asgInj L J):
      (∑u∈rows,(1:ℝ)*‖remainingPolynomialInj (originalSource U r bo) L J x coeff χ
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
    have hje:Admissible (assignedIdeal L J x):=assigned_admissible_inj L hp hs J x hx
    have hh:=henergy U hU Finset.univ J (Finset.subset_univ _) (by simpa using hK)
      L (fun i=>2*U^(ell i)) (fun i P=>star (coeff i P))
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
      (fun t ht=>remaining_tuple_admissible_inj L hp hs J x hx t ht)
      (fun t ht=>remaining_tuple_outside_inj L (reflectionExcludedPrimes q)
        (reflectionExcludedPrimes_prime q) hout J x _ t ht) hv hv0 (hadm J) (-θ)
    simpa only [one_mul,remainingPolynomialInj_original_pi,childLogTest_conjugate,
      assignedCenter,norm_neg,E] using hh
  have hb:=original_energy_with_assigned_count_inj K (by norm_num : (1:ℝ)≤2) hUone.le hK
    (originalSource U r bo) L hp ell (fun i P hP=>⟨(hp i P hP).ne_zero,hnorm i P hP⟩)
    coeff hc χ (fun J x hx=>assigned_admissible_inj L hp hs J x hx) (fun J x=>hχ _)
    (childLogTest W θ) r (∑i,ell i) rows (fun _=>1) (fun _=>zero_le_one) E hE hres
  simpa only [one_mul,E,A,mul_assoc] using hb

theorem source_energy_inj
    (W:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (Adm:SlotAdm)(Pmax Smax κ Lp:ℝ)
    (eps π eta τ loss:ℝ)(heps:0<eps)(hπ:0<π)
    (heta:0<eta)(hetaone:eta≤1)(hτ:0<τ)(hκ:8*eta+τ≤κ)(hLp:Lp≤3)
    (hloss:0<loss)(K:ℕ)
    (horacle:∀(Wf:𝓢(ℝ,ℂ))(lf hf:ℝ),0<lf→lf≤hf→Function.support (Wf:ℝ→ℂ)⊆Set.Icc lf hf→
      GoodEnergyExistsInj Adm (InitState Pmax Smax κ) eps Lp K Wf):
    ∀q:ℕ,q≠0→∃(degree:ℕ)(C U₀:ℝ),0<C ∧ 1<U₀ ∧
    ∀U:ℝ,U₀≤U→(2:ℝ)^K≤U^eta→
    ∀{ι:Type}[Fintype ι][DecidableEq ι],Fintype.card ι≤K→
    ∀(L:ι→Finset (Ideal O))(ell:ι→ℝ)(coeff:ι→Ideal O→ℂ),
      (∀i,0≤ell i)→(∀i,∀P∈L i,Prime P)→
      (∀i,∀P∈L i,Supported P)→
      (∀i,∀P∈L i,((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2)→
      (∀i,∀P∈L i,‖coeff i P‖≤1)→
      (∀i,∀P∈L i,outside (reflectionExcludedPrimes q) P)→
    ∀(primeW:ι→ℝ→ℂ),
      (∀i,Function.support (primeW i)⊆Set.Icc (1:ℝ) 2)→
      (∀i,∀P∈L i,primeW i ((P.absNorm:ℝ)/U^(ell i))≠0)→
    ∀χ:Ideal O→*ℂ,(∀I,‖χ I‖≤1)→
      FactorsModulo (fixedBaseConductor q) (elementCharacter (conjugateIdealCharacter χ))→
      (∀I,¬outside (reflectionExcludedPrimes q) I→
        conjugateIdealCharacter χ I=0)→
    ∀hv:ℝ,0≤hv→
      (∀(J:Finset ι)(Dpool:ℕ)(t:ℝ),Adm q Dpool ι (Finset.univ\J)
        (fun i=>poolList
          (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool) (L i))
        (fun i=>2*U^(ell i))
        (fun i P=>star (coeff i P.val)*FourierBridge.logPhase (-t)
          (Real.log (slotRatio U ell i P.val))) U (hv+|t|))→
    ∀m r:ℝ,0≤m→m≤2→
      (∀J:Finset ι,-2≤r+(∑i,ell i)-2*(∑i∈J,ell i))→
      0≤Pmax→ r≤Pmax→(∑i,ell i)≤Smax→1≤m→
      r+(∑i,ell i)+7*eta≤2→
    ∀rows:Finset O,(∀u∈rows,‖eisEmbedding u‖^2≤U^m)→∀θ:ℝ,
      (∑u∈rows,‖∑x∈tupInj L,(∏i,coeff i (x i).val)*
        originalTotalPolynomial (originalSource U r bo) (∏i,(x i).val) χ (fun _=>1)
          (childLogTest W θ) U r (∑i,ell i) u‖^2)≤
      C*(1+hv)^(2*degree)*U^(m+15*eta+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  have hsstar:Function.support (fun x=>star (W x))⊆Set.Icc ao bo := by
    intro x hx
    exact hsW (by simpa using hx)
  exact source_energy_inj_of_residual W bo Adm Pmax Smax eps π eta loss K
    (original_residual_uniform_energy_of_oracle_inj
      (fun x=>star (W x)) ao bo hao hab hsstar (Complex.conjCLE.contDiff.comp hW)
      DetectorDictionaryInverseMarkedPadding.radialMajorant
      DetectorDictionaryInverseMarkedPadding.radialMajorant_nonneg
      DetectorDictionaryInverseMarkedPadding.radialMajorant_one
      Adm Pmax Smax κ Lp 2 eps π eta τ loss (by norm_num) heps hπ heta hetaone hτ hκ hloss K
      (by linarith) horacle)

end
end Qrh.MarkedAnchor.Inverse.Inj

#print axioms Qrh.MarkedAnchor.Inverse.Inj.source_energy_inj_of_residual
#print axioms Qrh.MarkedAnchor.Inverse.Inj.source_energy_inj
