/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
/- Adapted from openai_baseline `OAI/NumberTheory/DirichletL/Inversion/InitialTotalFourier.lean`
(Apache-2.0). Modified by Sil (2026-11-11): native gates (`gap`, `r+2z ≤ m-2gap`,
`2r+8z ≤ 3m-2gap`) replaced by the parent rectangle `0 ≤ r ≤ Pmax`, `z ≤ Smax`, `1 ≤ m` and the
canonical oracle on `InitState Pmax Smax κ`; slot filter `Adm` and lower live-width bound added;
pool exponent `cap+1` replaced by `Lp`. Proof otherwise unchanged. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Init.TotalRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialTotalFourier

/-! # Inverse.Init.TotalFourier — seventh file of the oracle-parametric initialization chain (`original_fourier_energy_bound_of_oracle`); `Adm` is required of every log-phase twist of the coefficients. -/

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
open MeasureTheory FourierBridge JointLogSeparation InverseInitialOverlapFourier

theorem original_fourier_energy_bound_of_oracle
    (g:𝓢(ℝ,ℂ))(W:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
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
          (initialTest p (primeMark (all\assigned) lists
            (fun i P=>coeff i P*FourierBridge.logPhase (-t) (y i P)))
            (childLogTest W t) Z D) u)‖^2)≤
        C*(1+hv)^(2*degree)*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨Btree,hBtree,henergy⟩:=original_input_rows_fourier_bound_of_oracle
    W a₀ b₀ bcap ha₀ hbcap hs hW Φ hΦ hone B₀ hB₀ hb
    Adm Pmax Smax κ Lp cap eps π η τ loss hcap heps hπ hη hηone hτ hκ hloss K horacle
  refine ⟨Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨J,C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  obtain ⟨Cm,hCm,hmeasure⟩:=InverseInitialOverlapHeight.twisted_polynomial_measure_energy g (2*J)
  refine ⟨2*J+(volume:Measure ℝ).integrablePower,(Cm+1)*C,Z₀,mul_pos (by linarith) hC,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
    D m r hm hmcap hDlo hprodj hprod hlow hHlow hKη hDeq hr0 hrP hzS hm1 hparent rows hrows y xj θ
    hv hv0 hadm
  have hZp:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  let φ:O→ℝ→ℂ:=fun u t=>((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ
    (assignedElement assigned qelem) 1 1
    (initialTest p (primeMark (all\assigned) lists
      (fun i P=>coeff i P*logPhase (-t) (y i P))) (childLogTest W t) Z D) u
  have ht:=hmeasure θ xj (fun u:rows=>φ u.val) (C*(1+hv)^(2*J)*Z^(m+15*η+π+eps+loss))
    (by positivity)
    (fun u=>InverseInitialMarkedInputEnergy.marked_input_integrable p hg
      (frequencyTwist g θ) Finset.univ Ψ (assignedElement assigned qelem) u.val
      (all\assigned) lists coeff y W Z D xj)
    (fun t=>by
      apply (Finset.sum_coe_sort rows (fun u=>‖φ u t‖^2)).le.trans
      have hvt:0≤hv+|t|:=by positivity
      have h1:=henergy Z hZ Dpool hD all assigned hassigned hK lists Hslot coeff
        hdis hHs hPs hac qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
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
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.original_fourier_energy_bound_of_oracle
