/- Copyright (c) 2026 Sil. Apache-2.0. -/
/- Adapted from openai_baseline `OAI/NumberTheory/DirichletL/Inversion/{InitialFiniteEnergy,
InitialTotalEnergy,InitialTotalRows,InitialTotalFourier,InitialOverlapFourier,
InitialMarkedInputEnergy}.lean` (Apache-2.0), via `Inverse/Init/{FiniteEnergy,TotalEnergy,
TotalRows,TotalFourier}.lean`. Modified by Sil (2026-11-12): injective mark `primeMarkInj`
(lists may overlap, no `PairwiseDisjoint` hypothesis), injective oracle `GoodEnergyExistsInj`;
the high-mass tail and the zero mode use `Inj.Tail`/`Inj.ZeroMode` (constant `× (K^K)^2`);
the mode integrability uses the injective tuple form of the twisted mark. Proofs otherwise
unchanged. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Init.TotalFourier
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Inj.Init.Retained
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Inj.ZeroMode

/-!
# Inverse.Inj.Init.Energy — files 4-7 of the initialization chain for the injective mark

`finite_physical_bound_inj`, `original_input_bound_inj`, `original_input_rows_fourier_bound_inj`,
`original_fourier_energy_bound_inj`; helpers `tuple_markInj_phase`,
`overlap_mode_integrable_inj`, `marked_input_integrable_inj`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Inj
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
open MeasureTheory
open FourierBridge JointLogSeparation InverseInitialOverlapFourier
open FirstPassCubeLabels FirstCauchyArithmetic
open Qrh.MarkedAnchor.Inverse
local notation "O"=>ActualEisensteinCubic.O

section Phase
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

theorem tuple_markInj_phase (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ)
    (y : σ→ι→ℝ) (A : Finset ι) (t : ℝ) :
    primeMarkInj I L (fun i p=>a i p*logPhase (-t) (y i p)) A =
      ∑p∈(I.pi L).filter (fun p => ∀ i (hi : i ∈ I) j (hj : j ∈ I), p i hi = p j hj → i = j),
        (∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
        logPhase (-t) (∑i∈I.attach,y i.val (p i.val i.property)) := by
  unfold primeMarkInj
  refine Finset.sum_congr (by ext q; simp) (fun p hp => ?_)
  rw [logPhase_sum,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs <;> simp

theorem overlap_mode_integrable_inj (g : 𝓢(ℝ,ℂ))
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (A : Finset ι) (xj xc : ℝ) :
    Integrable (fun t:ℝ=>density g xj t*logPhase t xc*
      primeMarkInj I L (fun i p=>a i p*logPhase (-t) (y i p)) A) := by
  simp_rw [tuple_markInj_phase]
  simp only [Finset.mul_sum,density]
  apply integrable_finsetSum
  intro p hp
  convert fourier_phase_integrable g
    (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))
    (∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0) using 1
  funext t
  rw [←phase_sub]
  ring

end Phase

section Input
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem marked_input_integrable_inj (g:𝓢(ℝ,ℂ))(F:Finset ι)(Ψ:O→*ℂ)(j u:O)
    (I:Finset σ)(L:σ→Finset ι)(a:σ→ι→ℂ)(y:σ→ι→ℝ)
    (wFresh:ℝ→ℂ)(Z D xj:ℝ) :
    Integrable (fun t:ℝ=>density g xj t*
      (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
        (initialTest p (primeMarkInj I L (fun i q=>a i q*logPhase (-t) (y i q)))
          (childLogTest wFresh t) Z D) u)) := by
  simp_rw [InverseInitialArithmetic.initial_input_row p hg]
  unfold FirstCauchyArithmetic.supportConjugateSum
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro A hA
  have hh := (overlap_mode_integrable_inj g I L a y A xj
    (Real.log (primeProductNorm p A/Z^D))).const_mul
    (((Z^(-D/2):ℝ):ℂ)*FirstCauchyArithmetic.supportMobius (fun i=>Ideal.span {p i}) A*
      Ψ (∏i∈A,p i)*rowCoprimeMask (fun i=>Ideal.span {p i}) A j*
      star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg A u)*
      wFresh (primeProductNorm p A/Z^D))
  convert hh using 1
  funext t
  unfold initialTest childLogTest
  ring

end Input

theorem finite_physical_bound_inj
    (W₁ W₂:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)(Φ:𝓢(ℝ,ℂ))
    (B₀:ℝ)(hB₀:0≤B₀)(hb₁:∀x,‖W₁ x‖≤B₀)(hb₂:∀x,‖W₂ x‖≤B₀)
    (Adm:SlotAdm)(Pmax Smax κ Lp:ℝ)
    (cap eps π η τ loss:ℝ)(hcap:0≤cap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hτ:0<τ)(hκ:8*η+τ≤κ)(hloss:0<loss)(K:ℕ)
    (horacle:∀(Wf:𝓢(ℝ,ℂ))(lf hf:ℝ),0<lf→lf≤hf→Function.support (Wf:ℝ→ℂ)⊆Set.Icc lf hf→
      GoodEnergyExistsInj Adm (InitState Pmax Smax κ) eps Lp K Wf):
    ∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃(degree:ℕ)(C Z₀:ℝ),0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^Lp≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hp:=poolPrimary_ne_zero F hF;
    let hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀hv:ℝ,0≤hv→Adm q Dpool σ (all\assigned) lists Hslot coeff Z hv→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(S:Finset (Source (ι:=primePool F) 0)),
      (∀x∈S,x.divisor⊆x.common)→(∀x∈S,x.frequency≠0)→
      (∀x∈S,x.common⊆Finset.univ)→(∀x∈S,x.overlap⊆Finset.univ)→
    ∀(D m r:ℝ),0≤m→m≤cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      Z^(assignedCenter (all\assigned) z)≤(∏i∈all\assigned,Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,Hslot i≤2*(P.val.absNorm:ℝ))→(2:ℝ)^K≤Z^η→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      0≤Pmax→ r≤Pmax→assignedCenter all z≤Smax→1≤m→
      r+assignedCenter all z+7*η≤cap→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),1≤c₁→c₁≤bcap→1≤c₂→c₂≤bcap→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
      ‖physicalBlock p hp hcop hg (pointSource Finset.univ S) (w∘erasePoint) Ψ
        (assignedElement assigned qelem) (primeMarkInj (all\assigned) lists coeff)
        (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*(1+hv)^(2*degree)*Z^(m+15*η+π+eps+loss)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  obtain ⟨Btree,hBtree,hretained⟩:=retained_sum_bound_inj
    W₁ W₂ a₀ b₀ bcap ha₀ hbcap hs₁ hs₂ hW₁ hW₂ Φ
    Adm Pmax Smax κ Lp cap eps π η τ loss hcap heps hπ hη hηone hτ hκ hloss K horacle
  obtain ⟨ss,Ct,hCt,htail⟩:=actual_high_mass_tail_inj (2*cap+2) 1 τ hτ K
  let tailC:=Ct*B₀*B₀*ss.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ
  have htailC:0≤tailC:=by dsimp [tailC];positivity
  have hevent:∀ᶠZ:ℝ in atTop,max 1 b₀≤Z ∧ 64*(max 1 b₀)^2≤Z^η:=
    (eventually_ge_atTop (max 1 b₀)).and
      ((tendsto_rpow_atTop hη).eventually (eventually_ge_atTop (64*(max 1 b₀)^2)))
  obtain ⟨Zaux,haux⟩:=eventually_atTop.mp hevent
  refine ⟨Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨J,Cr,Zr,hCr,hZr,hretained⟩:=hretained q hq
  refine ⟨J,Cr+tailC,max Zr Zaux,by linarith,lt_max_of_lt_left hZr,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hHs hPs hac hv hv0 hadm
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf hcommon hoverlap
    D m r hm hmcap hDlo hprodj hprod hlow hHlow hKη hDeq hr0 hrP hzS hm1 hparent
    c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hw
  have hZr':Zr≤Z:=(le_max_left _ _).trans hZ
  have hZp:1<Z:=hZr.trans_le hZr'
  obtain ⟨hbZ,h64⟩:=haux Z ((le_max_right _ _).trans hZ)
  have hDcap:D≤cap:=by
    have hg:0≤assignedCenter assigned z:=Finset.sum_nonneg (fun i hi=>hz i (hassigned hi))
    rw [hDeq];linarith
  have hsize:max 1 b₀*Z^D≤Z^(2*cap+2):=by
    calc
      _≤Z*Z^D:=mul_le_mul_of_nonneg_right hbZ (Real.rpow_nonneg (by linarith) _)
      _=Z^(D+1):=by rw [Real.rpow_add (by linarith : 0<Z),Real.rpow_one];ring
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZp.le (by linarith)
  have hs₁':Function.support (clippedSource W₁ c₁ θ₁)⊆Set.Iic (max 1 b₀):=
    by
      intro x hx
      exact le_trans (clipped_support_upper W₁ a₀ b₀ c₁ θ₁ ha₀ hc₁ hs₁ hx) (le_max_right 1 b₀)
  have hs₂':Function.support (clippedSource W₂ c₂ θ₂)⊆Set.Iic (max 1 b₀):=
    by
      intro x hx
      exact le_trans (clipped_support_upper W₂ a₀ b₀ c₂ θ₂ ha₀ hc₂ hs₂ hx) (le_max_right 1 b₀)
  obtain ⟨T,hT,hfreqcap⟩:=exists_source_frequency_cap p S
  have hsplit:=actual_physical_retained_tail p hp hcop hg
    (InverseInitialRayAttachment.poolPrimary_primary F hFa) Finset.univ S hdiv hf w Ψ
    (assignedElement assigned qelem) (primeMarkInj (all\assigned) lists coeff)
    (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ
    Z D m (max 1 b₀) T (4*η+τ) hZp hs₁' hs₂' hfreqcap
  rw [hsplit]
  apply (norm_add_le _ _).trans
  have hret:=hretained Z hZr' Dpool hD all assigned hassigned hK lists Hslot coeff
    hHs hPs hac hv hv0 hadm qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf
    D m r T hm hT hprodj hprod hlow hHlow hKη hDeq hr0 hrP hzS hm1 hparent c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hw
  let Sc:=cappedSource p S (fun _=>1) (physicalCaps (max 1 b₀) Z D T)
  have ht:=htail p hp hcop hg (InverseInitialRayAttachment.poolPrimary_injective F hFa)
    (poolPrimary_odd F hFa) (InverseInitialRayAttachment.poolPrimary_primary F hFa) Ψ hΨ
    (assignedElement assigned qelem) (all\assigned) lists coeff
    ((Finset.card_le_card Finset.sdiff_subset).trans hK) hac
    (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m η (max 1 b₀) 1 B₀ B₀
    hZp hη.le (by positivity) h64 (by linarith) hsize (by linarith) (by linarith)
    (by norm_num) hB₀ hB₀ (clipped_bound W₁ B₀ hb₁ c₁ θ₁) (clipped_bound W₂ B₀ hb₂ c₂ θ₂)
    hs₁' hs₂' Finset.univ Sc w
    (fun x hx=>hcommon x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hoverlap x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hdiv x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hf x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hw x (Finset.mem_filter.mp hx).1)
    (fun _=>1) (physicalCaps (max 1 b₀) Z D T) (by intros;norm_num)
    (fun x hx=>(Finset.mem_filter.mp hx).2)
  have hheight:1≤(1+hv)^(2*J)*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
      (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)):=
    one_le_mul_of_one_le_of_one_le (one_le_hvPow hv0 _)
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [norm_nonneg θ₁]))
      (one_le_pow₀ (by linarith [norm_nonneg θ₂])))
  have hpow:Z^(-1:ℝ)≤Z^(m+15*η+π+eps+loss):=
    Real.rpow_le_rpow_of_exponent_le hZp.le (by linarith)
  apply (add_le_add hret ht).trans
  change Cr*(1+hv)^(2*J)*Z^(m+15*η+π+eps+loss)*_+
    (Ct*1*B₀*B₀*ss.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-1:ℝ))≤_
  have hh:tailC*Z^(-1:ℝ)≤tailC*Z^(m+15*η+π+eps+loss)*
      ((1+hv)^(2*J)*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J))):=by
    calc
      _≤tailC*Z^(m+15*η+π+eps+loss):=mul_le_mul_of_nonneg_left hpow htailC
      _≤_:=le_mul_of_one_le_right (by positivity) hheight
  convert add_le_add_left hh (Cr*(1+hv)^(2*J)*Z^(m+15*η+π+eps+loss)*
    ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
      (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J))) using 1 <;> dsimp [tailC] <;> ring

theorem original_input_bound_inj
    (W:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (B₀:ℝ)(hB₀:0≤B₀)(hb:∀x,‖W x‖≤B₀)
    (Adm:SlotAdm)(Pmax Smax κ Lp:ℝ)
    (cap eps π η τ loss:ℝ)(hcap:0≤cap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hτ:0<τ)(hκ:8*η+τ≤κ)(hloss:0<loss)(K:ℕ)
    (horacle:∀(Wf:𝓢(ℝ,ℂ))(lf hf:ℝ),0<lf→lf≤hf→Function.support (Wf:ℝ→ℂ)⊆Set.Icc lf hf→
      GoodEnergyExistsInj Adm (InitState Pmax Smax κ) eps Lp K Wf):
    ∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃(degree:ℕ)(C Z₀:ℝ),0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^Lp≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let _hp:=poolPrimary_ne_zero F hF;
    let _hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀hv:ℝ,0≤hv→Adm q Dpool σ (all\assigned) lists Hslot coeff Z hv→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(D m r:ℝ),0≤m→m≤cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      Z^(assignedCenter (all\assigned) z)≤(∏i∈all\assigned,Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,Hslot i≤2*(P.val.absNorm:ℝ))→(2:ℝ)^K≤Z^η→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      0≤Pmax→ r≤Pmax→assignedCenter all z≤Smax→1≤m→
      r+assignedCenter all z+7*η≤cap→
    ∀(c θ:ℝ),1≤c→c≤bcap→
      ‖∑'u:O,Φ (‖eisEmbedding u‖^2/Z^m)*
        (‖((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ
          (assignedElement assigned qelem) 1 1
          (initialTest p (primeMarkInj (all\assigned) lists coeff)
            (clippedSource W c θ) Z D) u‖^2:ℝ)‖≤
        C*(1+hv)^(2*degree)*Z^(m+15*η+π+eps+loss)*
          (1+‖θ‖)^(2*InverseClippingProfiles.momentOrder (4*degree)) := by
  have hsstar:Function.support (fun x=>star (W x))⊆Set.Icc a₀ b₀:=by
    intro x hx
    apply hs
    simpa only [Function.mem_support,star_ne_zero] using hx
  have hbStar:∀x,‖star (W x)‖≤B₀:=by intro x;simpa only [norm_star] using hb x
  obtain ⟨Btree,hBtree,hfinite⟩:=finite_physical_bound_inj
    (fun x=>star (W x)) W a₀ b₀ bcap ha₀ hbcap hsstar hs
    (Complex.conjCLE.contDiff.comp hW) hW Φ B₀ hB₀ hbStar hb
    Adm Pmax Smax κ Lp cap eps π η τ loss hcap heps hπ hη hηone hτ hκ hloss K horacle
  obtain ⟨Cz,hCz,hzero⟩:=physical_marked_zero_bound_inj
    loss cap (max 1 b₀) B₀ hloss hcap (by positivity) hB₀ Φ K
  refine ⟨Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨J,Cf,Z₀,hCf,hZ₀,hfinite⟩:=hfinite q hq
  refine ⟨J,Cf+Cz,Z₀,by linarith,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hHs hPs hac hv hv0 hadm
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
    D m r hm hmcap hDlo hprodj hprod hlow hHlow hKη hDeq hr0 hrP hzS hm1 hparent c θ hc hbc
  have hZp:1<Z:=hZ₀.trans_le hZ
  have hDcap:D≤cap:=by
    have hg:0≤assignedCenter assigned z:=Finset.sum_nonneg (fun i hi=>hz i (hassigned hi))
    rw [hDeq];linarith
  have hconj:(fun x=>star (clippedSource W c θ x))=clippedSource (fun x=>star (W x)) c (-θ):=
    funext (clippedSource_conjugate W c θ)
  have hn:=nonzero_frequency_norm_le p hp hcop hg
    (InverseInitialRayAttachment.poolPrimary_injective F hFa) (poolPrimary_odd F hFa)
    (InverseInitialRayAttachment.poolPrimary_primary F hFa) Finset.univ Ψ
    (assignedElement assigned qelem) (primeMarkInj (all\assigned) lists coeff)
    (clippedSource W c θ) Φ Z D m
    (Cf*(1+hv)^(2*J)*Z^(m+15*η+π+eps+loss)*(1+‖θ‖)^(2*InverseClippingProfiles.momentOrder (4*J)))
    (by linarith : 0<Z) (by
      intro freqT hzero
      rw [hconj]
      have h:=hfinite Z hZ Dpool hD all assigned hassigned hK lists Hslot coeff
        hHs hPs hac hv hv0 hadm qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
        (finiteSource Finset.univ freqT)
        (finiteSource_divisor Finset.univ freqT) (finiteSource_nonzero Finset.univ freqT hzero)
        (fun x hx=>Finset.subset_univ _) (fun x hx=>Finset.subset_univ _)
        D m r hm hmcap hDlo hprodj hprod hlow hHlow hKη hDeq hr0 hrP hzS hm1 hparent
        c c (-θ) θ hc hbc hc hbc (fun _=>1) (by intros;norm_num)
      simpa only [Function.comp_def,norm_neg,pow_mul,pow_two,mul_pow] using h)
  have hz0:=hzero p hp hcop hg (InverseInitialRayAttachment.poolPrimary_injective F hFa)
    (poolPrimary_odd F hFa) (InverseInitialRayAttachment.poolPrimary_primary F hFa)
    Finset.univ Ψ hΨ (assignedElement assigned qelem) (all\assigned) lists coeff
    ((Finset.card_le_card Finset.sdiff_subset).trans hK) hac
    (clippedSource W c θ) (clipped_bound W B₀ hb c θ)
    (fun x hx=>le_trans (clipped_support_upper W a₀ b₀ c θ ha₀ hc hs hx) (le_max_right 1 b₀))
    Z D m hZp.le hDcap
  rw [original_input_zero_nonzero p hp hcop hg
    (InverseInitialRayAttachment.poolPrimary_injective F hFa) (poolPrimary_odd F hFa)
    (InverseInitialRayAttachment.poolPrimary_primary F hFa) Finset.univ Ψ
    (assignedElement assigned qelem) (primeMarkInj (all\assigned) lists coeff)
    (clippedSource W c θ) Φ Z D m (by linarith)]
  apply (norm_add_le _ _).trans
  have hh:1≤(1+hv)^(2*J)*(1+‖θ‖)^(2*InverseClippingProfiles.momentOrder (4*J)):=
    one_le_mul_of_one_le_of_one_le (one_le_hvPow hv0 _) (one_le_pow₀ (by linarith [norm_nonneg θ]))
  have hz1:Cz*Z^(m+loss)≤Cz*(1+hv)^(2*J)*Z^(m+15*η+π+eps+loss)*
      (1+‖θ‖)^(2*InverseClippingProfiles.momentOrder (4*J)):=by
    calc
      _≤Cz*Z^(m+15*η+π+eps+loss):=mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZp.le (by linarith)) hCz.le
      _≤Cz*Z^(m+15*η+π+eps+loss)*((1+hv)^(2*J)*
          (1+‖θ‖)^(2*InverseClippingProfiles.momentOrder (4*J))):=le_mul_of_one_le_right (by positivity) hh
      _=_:=by ring
  change ‖physicalFrequency _ _ _ _ _ _ _ _ _ _ _ _ _ 0‖+_≤_
  exact (add_le_add (hz0.trans hz1) hn).trans_eq (by ring)

theorem original_input_rows_fourier_bound_inj
    (W:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (B₀:ℝ)(hB₀:0≤B₀)(hb:∀x,‖W x‖≤B₀)
    (Adm:SlotAdm)(Pmax Smax κ Lp:ℝ)
    (cap eps π η τ loss:ℝ)(hcap:0≤cap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hτ:0<τ)(hκ:8*η+τ≤κ)(hloss:0<loss)(K:ℕ)
    (horacle:∀(Wf:𝓢(ℝ,ℂ))(lf hf:ℝ),0<lf→lf≤hf→Function.support (Wf:ℝ→ℂ)⊆Set.Icc lf hf→
      GoodEnergyExistsInj Adm (InitState Pmax Smax κ) eps Lp K Wf):
    ∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃(degree:ℕ)(C Z₀:ℝ),0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^Lp≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let _hp:=poolPrimary_ne_zero F hF;
    let _hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(D m r:ℝ),0≤m→m≤cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      Z^(assignedCenter (all\assigned) z)≤(∏i∈all\assigned,Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,Hslot i≤2*(P.val.absNorm:ℝ))→(2:ℝ)^K≤Z^η→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      0≤Pmax→ r≤Pmax→assignedCenter all z≤Smax→1≤m→
      r+assignedCenter all z+7*η≤cap→
    ∀(rows:Finset O),(∀u∈rows,‖eisEmbedding u‖^2≤Z^m)→
    ∀(y:σ→primePool F→ℝ)(θ:ℝ),∀hv:ℝ,0≤hv→
      Adm q Dpool σ (all\assigned) lists Hslot
        (fun i P=>coeff i P*FourierBridge.logPhase (-θ) (y i P)) Z hv→
      (∑u∈rows,‖((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ
          (assignedElement assigned qelem) 1 1
          (initialTest p (primeMarkInj (all\assigned) lists
            (fun i P=>coeff i P*FourierBridge.logPhase (-θ) (y i P)))
            (childLogTest W θ) Z D) u‖^2)≤
        C*(1+hv)^(2*degree)*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨Btree,hBtree,henergy⟩:=original_input_bound_inj
    W a₀ b₀ bcap ha₀ hbcap hs hW Φ B₀ hB₀ hb
    Adm Pmax Smax κ Lp cap eps π η τ loss hcap heps hπ hη hηone hτ hκ hloss K horacle
  refine ⟨Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨J,C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  refine ⟨InverseClippingProfiles.momentOrder (4*J),C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
    D m r hm hmcap hDlo hprodj hprod hlow hHlow hKη hDeq hr0 hrP hzS hm1 hparent rows hrows y θ
    hv hv0 hadm
  have hZp:1<Z:=hZ₀.trans_le hZ
  have he:=henergy Z hZ Dpool hD all assigned hassigned hK lists Hslot
    (fun i P=>coeff i P*FourierBridge.logPhase (-θ) (y i P)) hHs hPs
    (by intro i hi P hP;simpa only [norm_mul,FourierBridge.logPhase_norm,mul_one] using hac i hi P hP)
    hv hv0 hadm
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
    D m r hm hmcap hDlo hprodj hprod hlow hHlow hKη hDeq hr0 hrP hzS hm1 hparent 1 θ le_rfl hbcap
  have hr:=InverseInitialInputRadial.finite_rows_le_input_norm p hg Finset.univ Ψ
    (assignedElement assigned qelem)
    (initialTest p (primeMarkInj (all\assigned) lists
      (fun i P=>coeff i P*FourierBridge.logPhase (-θ) (y i P))) (childLogTest W θ) Z D)
    ((Z^(-D/2):ℝ):ℂ) Φ hΦ hone (Z^m) (Real.rpow_pos_of_pos (by linarith) _) rows hrows
  have he' := he.trans (hvFactor_mono hC.le (Real.rpow_nonneg (by linarith) _) (by positivity) hv0
    (show 2*J ≤ 2*InverseClippingProfiles.momentOrder (4*J) by
      unfold InverseClippingProfiles.momentOrder; omega))
  apply hr.trans
  simpa only [InverseInitialProfileBounds.childLogTest_eq_clipped,pow_mul,pow_two,mul_pow] using he'

theorem original_fourier_energy_bound_inj
    (g:𝓢(ℝ,ℂ))(W:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (B₀:ℝ)(hB₀:0≤B₀)(hb:∀x,‖W x‖≤B₀)
    (Adm:SlotAdm)(Pmax Smax κ Lp:ℝ)
    (cap eps π η τ loss:ℝ)(hcap:0≤cap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hτ:0<τ)(hκ:8*η+τ≤κ)(hloss:0<loss)(K:ℕ)
    (horacle:∀(Wf:𝓢(ℝ,ℂ))(lf hf:ℝ),0<lf→lf≤hf→Function.support (Wf:ℝ→ℂ)⊆Set.Icc lf hf→
      GoodEnergyExistsInj Adm (InitState Pmax Smax κ) eps Lp K Wf):
    ∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃(degree:ℕ)(C Z₀:ℝ),0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^Lp≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let _hp:=poolPrimary_ne_zero F hF;
    let _hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(D m r:ℝ),0≤m→m≤cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      Z^(assignedCenter (all\assigned) z)≤(∏i∈all\assigned,Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,Hslot i≤2*(P.val.absNorm:ℝ))→(2:ℝ)^K≤Z^η→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      0≤Pmax→ r≤Pmax→assignedCenter all z≤Smax→1≤m→
      r+assignedCenter all z+7*η≤cap→
    ∀(rows:Finset O),(∀u∈rows,‖eisEmbedding u‖^2≤Z^m)→
    ∀(y:σ→primePool F→ℝ)(xj θ:ℝ),∀hv:ℝ,0≤hv→
      (∀t:ℝ,Adm q Dpool σ (all\assigned) lists Hslot
        (fun i P=>coeff i P*FourierBridge.logPhase (-t) (y i P)) Z (hv+|t|))→
      (∑u∈rows,‖∫t:ℝ,density (frequencyTwist g θ) xj t*
        (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ
          (assignedElement assigned qelem) 1 1
          (initialTest p (primeMarkInj (all\assigned) lists
            (fun i P=>coeff i P*FourierBridge.logPhase (-t) (y i P)))
            (childLogTest W t) Z D) u)‖^2)≤
        C*(1+hv)^(2*degree)*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨Btree,hBtree,henergy⟩:=original_input_rows_fourier_bound_inj
    W a₀ b₀ bcap ha₀ hbcap hs hW Φ hΦ hone B₀ hB₀ hb
    Adm Pmax Smax κ Lp cap eps π η τ loss hcap heps hπ hη hηone hτ hκ hloss K horacle
  refine ⟨Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨J,C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  obtain ⟨Cm,hCm,hmeasure⟩:=InverseInitialOverlapHeight.twisted_polynomial_measure_energy g (2*J)
  refine ⟨2*J+(volume:Measure ℝ).integrablePower,(Cm+1)*C,Z₀,mul_pos (by linarith) hC,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
    D m r hm hmcap hDlo hprodj hprod hlow hHlow hKη hDeq hr0 hrP hzS hm1 hparent rows hrows y xj θ
    hv hv0 hadm
  have hZp:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  let φ:O→ℝ→ℂ:=fun u t=>((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ
    (assignedElement assigned qelem) 1 1
    (initialTest p (primeMarkInj (all\assigned) lists
      (fun i P=>coeff i P*logPhase (-t) (y i P))) (childLogTest W t) Z D) u
  have ht:=hmeasure θ xj (fun u:rows=>φ u.val) (C*(1+hv)^(2*J)*Z^(m+15*η+π+eps+loss))
    (by positivity)
    (fun u=>marked_input_integrable_inj p hg
      (frequencyTwist g θ) Finset.univ Ψ (assignedElement assigned qelem) u.val
      (all\assigned) lists coeff y W Z D xj)
    (fun t=>by
      apply (Finset.sum_coe_sort rows (fun u=>‖φ u t‖^2)).le.trans
      have hvt:0≤hv+|t|:=by positivity
      have h1:=henergy Z hZ Dpool hD all assigned hassigned hK lists Hslot coeff
        hHs hPs hac qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
        D m r hm hmcap hDlo hprodj hprod hlow hHlow hKη hDeq hr0 hrP hzS hm1 hparent rows hrows y t (hv+|t|) hvt (hadm t)
      have h2:(1+(hv+|t|))^(2*J)≤(1+hv)^(2*J)*(1+‖t‖)^(2*J):=by
        have h3:=heightPow_split t hv hv0 (2*J)
        rw [Real.norm_eq_abs] at h3 ⊢
        have h4:(1+(hv+|t|))=1+|t|+hv:=by ring
        rw [h4]
        exact h3
      have hZ0:0≤Z^(m+15*η+π+eps+loss):=Real.rpow_nonneg hZp.le _
      refine h1.trans ?_
      calc _≤C*((1+hv)^(2*J)*(1+‖t‖)^(2*J))*Z^(m+15*η+π+eps+loss)*((1+‖t‖)^J)^2:=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h2 hC.le) hZ0) (by positivity)
        _=_:=by ring)
  apply (Finset.sum_coe_sort rows (fun u=>‖∫t:ℝ,density (frequencyTwist g θ) xj t*φ u t‖^2)).symm.le.trans
  apply ht.trans
  have hh:0≤C*(1+hv)^(2*J)*Z^(m+15*η+π+eps+loss)*
      (1+‖θ‖)^(2*(2*J+(volume:Measure ℝ).integrablePower)):=by positivity
  have he:=mul_le_mul_of_nonneg_right (show Cm≤Cm+1 by linarith) hh
  have he2:(Cm+1)*(C*(1+hv)^(2*J)*Z^(m+15*η+π+eps+loss)*
        (1+‖θ‖)^(2*(2*J+(volume:Measure ℝ).integrablePower)))≤
      (Cm+1)*(C*(1+hv)^(2*(2*J+(volume:Measure ℝ).integrablePower))*Z^(m+15*η+π+eps+loss)*
        (1+‖θ‖)^(2*(2*J+(volume:Measure ℝ).integrablePower))):=
    mul_le_mul_of_nonneg_left (hvFactor_mono hC.le (Real.rpow_nonneg hZp.le _) (by positivity) hv0
      (by omega)) (by linarith)
  have he3:=he.trans he2
  convert he3 using 1 <;> simp only [pow_mul,pow_two,mul_pow] <;> ring

end
end Qrh.MarkedAnchor.Inverse.Inj

#print axioms Qrh.MarkedAnchor.Inverse.Inj.finite_physical_bound_inj
#print axioms Qrh.MarkedAnchor.Inverse.Inj.original_fourier_energy_bound_inj
