/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
/- Adapted from openai_baseline `OAI/NumberTheory/DirichletL/Inversion/InitialRetainedWindow.lean`
(Apache-2.0). Modified by Sil (2026-11-11): the native gates (`gap`, `r+2z ≤ m-2gap`,
`2r+8z ≤ 3m-2gap`, `cap`) are replaced by the parent rectangle `0 ≤ r ≤ Pmax`, `z ≤ Smax`,
`1 ≤ m` and the canonical oracle on `InitState Pmax Smax κ`; the slot data carry `Adm` and the
lower live-width bound. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Init.RetainedPhysical
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Init.WindowState
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Init.AssignedWidth
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialRetainedWindow

/-!
# Inverse.Init.RetainedWindow — second file of the oracle-parametric initialization chain

`retained_window_bound_of_oracle`: the baseline `retained_window_bound` for a parent of free
width `r ≤ Pmax` and mark width `∑ z ≤ Smax` on the ball `‖u‖² ≤ Z^m`, `m ≥ 1`, with the
canonical energy supplied by `GoodEnergyExists Adm (InitState Pmax Smax κ) eps Lp K`.
The window states of every allocated subcollection are initial states at their actual width
(`window_initState_assigned`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialEnergyCallerSourceMask InverseInitialQuotientGeometry InverseInitialClippedColumns
open InverseInitialCanonicalState InverseInitialEnergyCallerState FirstPassCubeLabels
open InverseInitialEnergyCallerAssigned
local notation "O" => ActualEisensteinCubic.O

theorem retained_window_bound_of_oracle
    (W₁ W₂:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)(Φ:𝓢(ℝ,ℂ))
    (lo hi:Fin 4→ℝ)(hlo:∀i,0<lo i)(hhi:∀i,lo i≤hi i)
    (Adm:SlotAdm)(Pmax Smax κ Lp eps U π:ℝ)(heps:0<eps)(hU:0≤U)(hπ:0<π)(K:ℕ)
    (horacle:∀(Wf:𝓢(ℝ,ℂ))(lf hf:ℝ),0<lf→lf≤hf→Function.support (Wf:ℝ→ℂ)⊆Set.Icc lf hf→
      GoodEnergyExists Adm (InitState Pmax Smax κ) eps Lp K Wf):
    ∃Btree Tclip:ℝ,1≤Btree ∧ 0≤Tclip ∧
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
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
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
    ∀(ψ:Fin 4→ℝ→ℂ),(∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))→
    ∀(D B v θ H m r η τ:ℝ),0≤η→0≤τ→8*η+τ≤κ→
      (∀i,hi i≤Z^η)→Z^(-η)≤lo 1→Tclip≤3*η*Real.log Z→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      Z^(assignedCenter (all\assigned) z)≤(∏i∈all\assigned,Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,Hslot i≤2*(P.val.absNorm:ℝ))→(2:ℝ)^K≤Z^η→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      0≤Pmax→ r≤Pmax→assignedCenter all z≤Smax→1≤m→B-θ+2*η≤U→
      radialCenter m H θ D B≤4*η+τ→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),1≤c₁→c₁≤bcap→1≤c₂→c₂≤bcap→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
      ‖physicalBlock p hp hcop hg (pointSource Finset.univ (windowSource p S ψ Z D B v θ H))
        (w∘erasePoint) Ψ (assignedElement assigned qelem)
        (primeMark (all\assigned) lists coeff)
        (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*(1+hv)^(2*degree)*Z^(m+15*η+π+eps)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  obtain ⟨fresh,Vlog,Mlog,af,bf,haf,hab,hfc,hfs,hM,hVc,hVs,hwindow⟩:=
    InverseInitialEnergyCallerFixedWindows.exists_actual_initial_windows
      W₁ W₂ a₀ b₀ bcap ha₀ hbcap hs₁ hs₂ hW₁ hW₂ lo hi hlo hhi
  have hfs':Function.support (fresh:ℝ→ℂ)⊆Set.Icc af (max 1 bf):=by
    intro x hx
    have h:=hfs (subset_closure hx)
    exact ⟨h.1,h.2.trans (le_max_right _ _)⟩
  obtain ⟨Btree,hBtree,hbound⟩:=retained_physical_bound_of_oracle
    W₁ W₂ a₀ b₀ ha₀ hs₁ hs₂ hW₁ hW₂ Φ (fun i=>Vlog i) Mlog
    (fun i=>(Vlog i).smooth ⊤) hVc hM (fun i y hy=>abs_le.mpr (hVs i hy))
    fresh fresh af (max 1 bf) haf (le_max_left _ _) hfs' hfs' (fresh.smooth ⊤) (fresh.smooth ⊤)
    Adm (InitState Pmax Smax κ) Lp eps U π heps hU hπ K horacle
  refine ⟨Btree,Real.log (max 1 bf),hBtree,Real.log_nonneg (le_max_left _ _),?_⟩
  intro q hq
  obtain ⟨J,C,Z₀,hC,hZ₀,hbound⟩:=hbound q hq
  refine ⟨J,C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac hv hv0 hadm
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf ψ hψ
    D B v θ H m r η τ hη hτ0 hκ hhiZ hloZ hlog hprodj hprod hlow hHlow hKη hDeq hr0 hrP hzS hm1 hR hrad
    c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hw
  have hZp:1<Z:=hZ₀.trans_le hZ
  have hprimary:=InverseInitialRayAttachment.poolPrimary_primary F hFa
  let Sw:=windowSource p S ψ Z D B v θ H
  let Sc:=coprimeSource p Sw
  have hdivw:∀x∈Sw,x.divisor⊆x.common:=fun x hx=>hdiv x (Finset.mem_filter.mp hx).1
  have hfw:∀x∈Sw,x.frequency≠0:=fun x hx=>hf x (Finset.mem_filter.mp hx).1
  have hdivc:∀x∈Sc,x.divisor⊆x.common:=fun x hx=>hdivw x (Finset.mem_filter.mp hx).1
  have hfc':∀x∈Sc,x.frequency≠0:=fun x hx=>hfw x (Finset.mem_filter.mp hx).1
  have hswhole:=hwindow p hp Finset.univ S hdiv hf ψ hψ Z D B v θ H c₁ c₂ θ₁ θ₂
    (zero_lt_one.trans hZp) hc₁ hbc₁ hc₂ hbc₂
  have hpoint:pointSource Finset.univ Sc⊆pointSource Finset.univ Sw:=by
    intro x hx
    obtain ⟨y,hy,hm⟩:=Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨y,(Finset.mem_filter.mp hy).1,hm⟩
  have hsupport:BlockSupport p (pointSource Finset.univ Sc) W₁ W₂ fresh fresh
      (fun i=>Vlog i) Z D B v θ H c₁ c₂ θ₁ θ₂:=
    ⟨fun x hx=>hswhole.1 x (hpoint hx),fun x hx=>hswhole.2.1 x (hpoint hx),
      fun x hx=>hswhole.2.2 x (hpoint hx)⟩
  rw [physicalBlock_coprimeSource p hp hcop hg hprimary Finset.univ _ hdivw hfw]
  by_cases hempty:physicalBlock p hp hcop hg (pointSource Finset.univ Sc) (w∘erasePoint) Ψ
      (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m=0
  · rw [hempty,norm_zero];positivity
  have hclip:= (InverseInitialEnergyCallerEmpty.physical_nonzero_clipping p hp hcop hg
    hprimary Finset.univ Sc hdivc hfc' (w∘erasePoint) Ψ (assignedElement assigned qelem)
    (primeMark (all\assigned) lists coeff) W₁ W₂ fresh fresh (fun i=>Vlog i) Φ
    Z D B v θ H m c₁ c₂ θ₁ θ₂ af (max 1 bf) η hZp (le_max_left _ _) hfs' hsupport hlog hempty).2
  have hqt:quotientSet p Sc⊆quotientSet p Sw:=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have hn:∀t∈quotientSet p Sc,(t.absNorm:ℝ)≤Z^(B-θ+2*η):=by
    intro t ht
    exact retained_quotient_bound p hp S (fun _=>1) (ψ 0) (ψ 1)
      (lo 0) (hi 0) (lo 1) (hi 1) Z B θ η (zero_lt_one.trans hZp)
      (hψ 0) (hψ 1) (hhiZ 0) hloZ hdiv t
      (window_quotient_subset_retained p S ψ Z D B v θ H (hqt ht))
  have hstates:∀t∈quotientSet p Sc,
      assignedElement assigned qelem*primaryGenerator t≠0 ∧ 0≤θ+v+2*η ∧ 0≤θ+H+2*η ∧
      0≤fullPunctureWidth Z t (assignedElement assigned qelem) ∧
      ‖eisEmbedding (assignedElement assigned qelem*primaryGenerator t)‖^2=
        Z^(fullPunctureWidth Z t (assignedElement assigned qelem)):=by
    intro t ht
    have hs:=window_initState p hp hprimary S ψ lo hi hψ Z D B v θ H η hZp hη hhiZ hloZ
      hdiv hf all assigned hassigned qelem z al bl primeW hz hqe hprimeW hprimeLive hprodj (hqt ht)
      m r τ Pmax Smax κ hDeq hr0 hrP hzS hm1 hτ0 hκ hrad hclip
    obtain ⟨hm,hN,hV,hM,hQ,he,_⟩:=hs
    exact ⟨hm,hV,hM,hQ,he⟩
  have hdisA : ((all\assigned : Finset σ) : Set σ).PairwiseDisjoint lists :=
    fun i hi j hj hij=>hdis (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij
  have hHlow' : ∀ i ∈ all\assigned, ∀ P ∈ lists i,
      Hslot i ≤ 2*(Ideal.absNorm (Ideal.span {poolPrimary F P}) : ℝ) := by
    intro i hi P hP
    rw [poolPrimary_span F hFa P]
    exact hHlow i hi P hP
  have hScw : Sc ⊆ windowSource p S ψ Z D B v θ H := Finset.filter_subset _ _
  have hgoodA : ∀J₁∈(all\assigned).powerset,∀J₂∈(all\assigned).powerset,
      ∀t∈quotientSet p (assignedSource Sc J₁ J₂ lists lists),
      InitState Pmax Smax κ (max 0 (columnCenter D B v)) (θ+v+2*η) (θ+H+2*η)
        (fullPunctureWidth Z t (assignedElement assigned qelem))
        (Real.logb Z (∏i∈(all\assigned)\J₁,Hslot i)) ∧
      InitState Pmax Smax κ (max 0 (columnCenter D B v)) (θ+v+2*η) (θ+H+2*η)
        (fullPunctureWidth Z t (assignedElement assigned qelem))
        (Real.logb Z (∏i∈(all\assigned)\J₂,Hslot i)) := by
    intro J₁ hJ₁ J₂ hJ₂ t ht
    obtain ⟨x,hx,f₁,f₂,rfl,hl₁,hm₁,hl₂,hm₂⟩ := assigned_quotient_cases p Sc J₁ J₂ lists ht
    constructor
    · exact window_initState_assigned p hp hprimary S ψ lo hi hψ Z D B v θ H η hZp hη hhiZ hloZ
        hdiv hf all assigned hassigned qelem z al bl primeW hz hqe hprimeW hprimeLive hprodj
        lists Hslot K hK hdisA hHs hHlow' hprod hlow hKη Sc hScw J₁ (Finset.mem_powerset.mp hJ₁)
        x hx f₁ hl₁ hm₁ m r τ Pmax Smax κ hDeq hr0 hrP hzS hm1 hτ0 hκ hrad hclip
    · exact window_initState_assigned p hp hprimary S ψ lo hi hψ Z D B v θ H η hZp hη hhiZ hloZ
        hdiv hf all assigned hassigned qelem z al bl primeW hz hqe hprimeW hprimeLive hprodj
        lists Hslot K hK hdisA hHs hHlow' hprod hlow hKη Sc hScw J₂ (Finset.mem_powerset.mp hJ₂)
        x hx f₂ hl₂ hm₂ m r τ Pmax Smax κ hDeq hr0 hrP hzS hm1 hτ0 hκ hrad hclip
  apply hbound Z hZ Dpool hD (all\assigned) ((Finset.card_le_card Finset.sdiff_subset).trans hK)
    lists Hslot coeff (fun i hi j hj hij=>hdis (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij) hHs hPs hac
    hv hv0 hadm Ψ hΨ hperiod Sc hdivc hfc' (assignedElement assigned qelem) D B v θ H (B-θ+2*η) m η
    hR hη c₁ c₂ θ₁ θ₂ (zero_lt_one.trans_le hc₁) (zero_lt_one.trans_le hc₂) hsupport hn w
    (fun x hx=>hw x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)
    (idealRange (Z^(θ+v+2*η))) (nonzeroChildFrequencyBall 1 (Z^(θ+H+2*η)))
    (fun f hf=>mem_idealRange.mp hf) (Finset.Subset.refl _) ?_ ?_ hclip rfl hstates hgoodA
  · intro k hk
    exact (child_ball_neg _ k).mpr hk
  · intro x hx
    exact InverseInitialCanonicalDomains.actual_window_domains p hp hcop hg (poolPrimary_odd F hFa)
      hprimary S hdiv hf ψ lo hi hψ Z D B v θ H η (zero_lt_one.trans hZp) hhiZ x hx _

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.retained_window_bound_of_oracle
