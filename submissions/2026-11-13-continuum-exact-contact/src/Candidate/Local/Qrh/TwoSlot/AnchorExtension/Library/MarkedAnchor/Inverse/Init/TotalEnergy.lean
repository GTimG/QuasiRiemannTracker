/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
/- Adapted from openai_baseline `OAI/NumberTheory/DirichletL/Inversion/InitialTotalEnergy.lean`
(Apache-2.0). Modified by Sil (2026-11-11): native gates (`gap`, `r+2z ≤ m-2gap`,
`2r+8z ≤ 3m-2gap`) replaced by the parent rectangle `0 ≤ r ≤ Pmax`, `z ≤ Smax`, `1 ≤ m` and the
canonical oracle on `InitState Pmax Smax κ`; slot filter `Adm` and lower live-width bound added;
pool exponent `cap+1` replaced by `Lp`. Proof otherwise unchanged. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Init.FiniteEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialTotalEnergy

/-! # Inverse.Init.TotalEnergy — fifth file of the oracle-parametric initialization chain (`original_input_bound_of_oracle`). -/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O
open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment

theorem original_input_bound_of_oracle
    (W:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (B₀:ℝ)(hB₀:0≤B₀)(hb:∀x,‖W x‖≤B₀)
    (Adm:SlotAdm)(Pmax Smax κ Lp:ℝ)
    (cap eps π η τ loss:ℝ)(hcap:0≤cap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hτ:0<τ)(hκ:8*η+τ≤κ)(hloss:0<loss)(K:ℕ)
    (horacle:∀(Wf:𝓢(ℝ,ℂ))(lf hf:ℝ),0<lf→lf≤hf→Function.support (Wf:ℝ→ℂ)⊆Set.Icc lf hf→
      GoodEnergyExists Adm (InitState Pmax Smax κ) eps Lp K Wf):
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
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
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
          (initialTest p (primeMark (all\assigned) lists coeff)
            (clippedSource W c θ) Z D) u‖^2:ℝ)‖≤
        C*(1+hv)^(2*degree)*Z^(m+15*η+π+eps+loss)*
          (1+‖θ‖)^(2*InverseClippingProfiles.momentOrder (4*degree)) := by
  have hsstar:Function.support (fun x=>star (W x))⊆Set.Icc a₀ b₀:=by
    intro x hx
    apply hs
    simpa only [Function.mem_support,star_ne_zero] using hx
  have hbStar:∀x,‖star (W x)‖≤B₀:=by intro x;simpa only [norm_star] using hb x
  obtain ⟨Btree,hBtree,hfinite⟩:=finite_physical_bound_of_oracle
    (fun x=>star (W x)) W a₀ b₀ bcap ha₀ hbcap hsstar hs
    (Complex.conjCLE.contDiff.comp hW) hW Φ B₀ hB₀ hbStar hb
    Adm Pmax Smax κ Lp cap eps π η τ loss hcap heps hπ hη hηone hτ hκ hloss K horacle
  obtain ⟨Cz,hCz,hzero⟩:=InverseInitialZeroMode.physical_marked_zero_bound
    loss cap (max 1 b₀) B₀ hloss hcap (by positivity) hB₀ Φ
  refine ⟨Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨J,Cf,Z₀,hCf,hZ₀,hfinite⟩:=hfinite q hq
  refine ⟨J,Cf+Cz,Z₀,by linarith,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac hv hv0 hadm
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
    (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
    (clippedSource W c θ) Φ Z D m
    (Cf*(1+hv)^(2*J)*Z^(m+15*η+π+eps+loss)*(1+‖θ‖)^(2*InverseClippingProfiles.momentOrder (4*J)))
    (by linarith : 0<Z) (by
      intro freqT hzero
      rw [hconj]
      have h:=hfinite Z hZ Dpool hD all assigned hassigned hK lists Hslot coeff
        hdis hHs hPs hac hv hv0 hadm qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
        (finiteSource Finset.univ freqT)
        (finiteSource_divisor Finset.univ freqT) (finiteSource_nonzero Finset.univ freqT hzero)
        (fun x hx=>Finset.subset_univ _) (fun x hx=>Finset.subset_univ _)
        D m r hm hmcap hDlo hprodj hprod hlow hHlow hKη hDeq hr0 hrP hzS hm1 hparent
        c c (-θ) θ hc hbc hc hbc (fun _=>1) (by intros;norm_num)
      simpa only [Function.comp_def,norm_neg,pow_mul,pow_two,mul_pow] using h)
  have hz0:=hzero p hp hcop hg (InverseInitialRayAttachment.poolPrimary_injective F hFa)
    (poolPrimary_odd F hFa) (InverseInitialRayAttachment.poolPrimary_primary F hFa)
    Finset.univ Ψ hΨ (assignedElement assigned qelem) (all\assigned) lists coeff
    (fun i hi j hj hij=>hdis (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij) hac
    (clippedSource W c θ) (clipped_bound W B₀ hb c θ)
    (fun x hx=>le_trans (clipped_support_upper W a₀ b₀ c θ ha₀ hc hs hx) (le_max_right 1 b₀))
    Z D m hZp.le hDcap
  rw [original_input_zero_nonzero p hp hcop hg
    (InverseInitialRayAttachment.poolPrimary_injective F hFa) (poolPrimary_odd F hFa)
    (InverseInitialRayAttachment.poolPrimary_primary F hFa) Finset.univ Ψ
    (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
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

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.original_input_bound_of_oracle
