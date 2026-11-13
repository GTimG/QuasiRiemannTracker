/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
/- Adapted from openai_baseline `OAI/NumberTheory/DirichletL/Inversion/{InitialRetainedPhysical,
InitialCanonicalEnergy,InitialRetainedWindow,InitialRetainedSum}.lean` (Apache-2.0), via
`Inverse/Init/{RetainedPhysical,RetainedWindow,RetainedSum}.lean`. Modified by Sil (2026-11-12):
injective mark `primeMarkInj` (lists may overlap, no `PairwiseDisjoint` hypothesis), injective
oracle `GoodEnergyExistsInj`, injective assigned sources `assignedSourceInj` (allocation widths by
`window_initState_assigned_inj`), caller `actual_physical_reference_bound_inj`. Proofs otherwise
unchanged. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Init.RetainedSum
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Inj.Init.Window

/-!
# Inverse.Inj.Init.Retained — the retained physical / window / sum bounds, injective mark

`retained_physical_bound_inj` (plug point of the injective oracle), `retained_window_bound_inj`,
`retained_sum_bound_inj`: the first three files of the initialization chain for `primeMarkInj`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Inj
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseReflectedPhase InverseMoment InverseInitialClippedColumns
open CanonicalCoefficientClass ConcreteTraceCRT SecondPassArithmetic FirstPassCubeLabels IdealMobiusDivisorSum
open InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerModes
open InverseInitialQuotientGeometry InverseInitialEnergyCallerGeometry InverseInitialCanonicalState
open InverseInitialEnergyCallerAssigned
open InverseInitialEnergyCallerWindows InverseInitialEnergyCallerSourceMask InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseSecondChildWindows Filter
open Qrh.MarkedAnchor.Inverse
local notation "O" => ActualEisensteinCubic.O

section Child
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [DecidableEq σ] in
theorem normalizedColumnEnergyInj_rescale (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal O)) (rows : Finset O) (w : Ideal O → ℝ) (W : ℝ → ℂ)
    (X Z F G : ℝ) (hZ : 0 < Z) :
    normalizedColumnEnergyInj p hp hcop hg pool Ψ m slots lists a labels rows w W X Z F =
      Z^(G-F)*normalizedColumnEnergyInj p hp hcop hg pool Ψ m slots lists a labels rows w W X Z G := by
  have key (F' : ℝ) (r : ℂ) : ‖((Z^(-F'/2) : ℝ) : ℂ) * r‖^2 = Z^(-F') * ‖r‖^2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hZ.le _), mul_pow,
      ← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
    congr 2
    push_cast
    ring
  have e : Z^(-F) = Z^(G-F)*Z^(-G) := by
    rw [← Real.rpow_add hZ]
    congr 1
    ring
  unfold normalizedColumnEnergyInj
  simp_rw [key, e]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun f _ => Finset.sum_congr rfl (fun k _ => by ring))

omit [DecidableEq σ] in
theorem energyInj_range_weight_le (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal O)) (rows largeRows : Finset O) (w v : Ideal O → ℝ) (W : ℝ → ℂ)
    (X Z F : ℝ) (hrows : rows ⊆ largeRows) (hw : ∀ f ∈ labels, 0 ≤ w f)
    (hv : ∀ f ∈ labels, w f ≤ v f) :
    normalizedColumnEnergyInj p hp hcop hg pool Ψ m slots lists a labels rows w W X Z F ≤
      normalizedColumnEnergyInj p hp hcop hg pool Ψ m slots lists a labels largeRows v W X Z F := by
  unfold normalizedColumnEnergyInj
  apply Finset.sum_le_sum
  intro f hf
  apply mul_le_mul (hv f hf)
    (Finset.sum_le_sum_of_subset_of_nonneg hrows (fun _ _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    ((hw f hf).trans (hv f hf))

/-- `initial_child_from_good` with the injective oracle moments. -/
theorem initial_child_from_good_inj (Good : StatePred) (pool : Finset ι) (base Ψ : O →* ℂ)
    (slots subslots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (H : σ → ℝ)
    (W : 𝓢(ℝ,ℂ)) (Z eps A hv N V M Q η : ℝ) (K degree : ℕ) (m : O)
    (hZ : 1 < Z) (hbase : IsBaseRayTwist base Ψ) (hm : m ≠ 0)
    (hN : 0 ≤ N) (hV : 0 ≤ V+2*η) (hM : 0 ≤ M) (hQ : 0 ≤ Q)
    (hgood : Good N (V+2*η) M Q (Real.logb Z (∏ i ∈ subslots, H i)))
    (hmnorm : ‖eisEmbedding m‖^2 = Z^Q) (hsub : subslots ⊆ slots)
    (labels : Finset (Ideal O)) (hlabels : ∀ f ∈ labels, Admissible f ∧ (f.absNorm : ℝ) ≤ Z^(V+2*η))
    (rows : Finset O) (hrows : rows ⊆ nonzeroChildFrequencyBall 1 (Z^M))
    (weight : Ideal O → ℝ) (hw : ∀ f ∈ labels, 0 ≤ weight f)
    (hweight : ∀ f ∈ labels, weight f ≤ secondLabelWeight K f) (s : ℝ)
    (hmoment : GoodRankMomentsInj p hp hcop hg Good pool base slots lists a H W Z eps A hv K
      degree) :
    normalizedColumnEnergyInj p hp hcop hg pool Ψ m subslots lists a labels rows weight
      (childLogTest W s) (Z^N) Z (N+V) ≤ A*Z^(N+V+eps+4*η)*(1+‖s‖+hv)^(2*degree) := by
  have hcanon := hmoment Ψ hbase m hm N (V+2*η) M Q hN hV hM hQ hmnorm
    subslots hsub hgood labels hlabels s
  rw [normalizedColumnEnergyInj_rescale p hp hcop hg pool Ψ m subslots lists a
    labels rows weight (childLogTest W s) (Z^N) Z (N+V) (N+(V+2*η)) (zero_lt_one.trans hZ)]
  apply (mul_le_mul_of_nonneg_left
    ((energyInj_range_weight_le p hp hcop hg pool Ψ m subslots lists a
      labels rows (nonzeroChildFrequencyBall 1 (Z^M)) weight (secondLabelWeight K)
      (childLogTest W s) (Z^N) Z (N+(V+2*η)) hrows hw hweight).trans hcanon)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)).trans_eq
  rw [show N+(V+2*η)-(N+V) = 2*η by ring]
  calc
    _ = A*(Z^(2*η)*Z^(N+(V+2*η)+eps))*(1+‖s‖+hv)^(2*degree) := by ring
    _ = _ := by
      rw [← Real.rpow_add (zero_lt_one.trans hZ)]
      congr 3
      ring

end Child

/-- `retained_physical_bound_of_oracle` with the injective mark and the injective oracle. -/
theorem retained_physical_bound_inj
    (W₁ W₂:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (Φ:𝓢(ℝ,ℂ))(Vlog:Fin 6→ℝ→ℂ)(Mlog:Fin 6→ℝ)
    (hVlog:∀i,ContDiff ℝ ∞ (Vlog i))(hSlog:∀i,HasCompactSupport (Vlog i))
    (hMlog:∀i,0≤Mlog i)(hbox:∀i y,Vlog i y≠0→|y|≤Mlog i)
    (ω₁ ω₂:ℝ→ℂ)(lo b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hω₁:Function.support ω₁⊆Set.Icc lo b)(hω₂:Function.support ω₂⊆Set.Icc lo b)
    (hd₁:ContDiff ℝ ∞ ω₁)(hd₂:ContDiff ℝ ∞ ω₂)
    (Adm:SlotAdm)(Good:StatePred)(Lp eps U π:ℝ)(heps:0<eps)(hU:0≤U)(hπ:0<π)(K:ℕ)
    (horacle:∀(Wf:𝓢(ℝ,ℂ))(lf hf:ℝ),0<lf→lf≤hf→Function.support (Wf:ℝ→ℂ)⊆Set.Icc lf hf→
      GoodEnergyExistsInj Adm Good eps Lp K Wf):
    ∃Btree:ℝ,1≤Btree ∧ ∀q:ℕ,q≠0→∃(degree:ℕ)(C Z₀:ℝ),0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^Lp≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hp:=poolPrimary_ne_zero F hF;
    let hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](slots:Finset σ),slots.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(a:σ→primePool F→ℂ),
      (∀i∈slots,1≤Hslot i)→
      (∀i∈slots,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1)→
    ∀hv:ℝ,0≤hv→Adm q Dpool σ slots lists Hslot a Z hv→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(S:Finset (Source (ι:=primePool F) 0)),
      (∀x∈S,x.divisor⊆x.common)→(∀x∈S,x.frequency≠0)→
    ∀(j:O)(D B v θ H R m η:ℝ),R≤U→0≤η→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),0<c₁→0<c₂→
      BlockSupport p (pointSource Finset.univ S) W₁ W₂ ω₁ ω₂ Vlog Z D B v θ H c₁ c₂ θ₁ θ₂→
      (∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
    ∀(labels:Finset (Ideal O))(rows:Finset O),
      (∀f∈labels,Admissible f ∧ (f.absNorm:ℝ)≤Z^(θ+v+2*η))→
      rows⊆nonzeroChildFrequencyBall 1 (Z^(θ+H+2*η))→(∀k∈rows,-k∈rows)→
      (∀x∈S,(initialChild (toTuple p (sectorSource
        (unitSector p hp (InverseInitialRayAttachment.poolPrimary_primary F hF) (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource
        (unitSector p hp (InverseInitialRayAttachment.poolPrimary_primary F hF) (sourcePoint x ∅ ∅)) x))).2.2∈rows)→
      max 0 (columnCenter D B v)-columnCenter D B v≤3*η→R=B-θ+2*η→
      (∀t∈quotientSet p S,
        j*primaryGenerator t≠0 ∧ 0≤θ+v+2*η ∧ 0≤θ+H+2*η ∧
        0≤fullPunctureWidth Z t j ∧
        ‖eisEmbedding (j*primaryGenerator t)‖^2=Z^(fullPunctureWidth Z t j))→
      (∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p (assignedSourceInj S J₁ J₂ lists lists),
        Good (max 0 (columnCenter D B v)) (θ+v+2*η) (θ+H+2*η) (fullPunctureWidth Z t j)
          (Real.logb Z (∏i∈slots\J₁,Hslot i)) ∧
        Good (max 0 (columnCenter D B v)) (θ+v+2*η) (θ+H+2*η) (fullPunctureWidth Z t j)
          (Real.logb Z (∏i∈slots\J₂,Hslot i)))→
      ‖physicalBlock p hp hcop hg (pointSource Finset.univ S) (w∘erasePoint) Ψ j
        (primeMarkInj slots lists a) (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*(1+hv)^(2*degree)*Z^(m+15*η+π+eps)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  obtain ⟨fresh₁,fresh₂,hsf₁,hsf₂,hphysical⟩:=
    actual_physical_reference_bound_inj
      W₁ W₂ a₀ b₀ ha₀ hs₁ hs₂ hW₁ hW₂ Φ Vlog Mlog hVlog hSlog hMlog hbox
      ω₁ ω₂ lo b hlo hb hω₁ hω₂ hd₁ hd₂
  obtain ⟨af₁,bf₁,haf₁,hab₁,_,hs₁f⟩:=hsf₁
  obtain ⟨af₂,bf₂,haf₂,hab₂,_,hs₂f⟩:=hsf₂
  obtain ⟨B₁,hB₁,hm₁⟩:=horacle fresh₁ af₁ bf₁ haf₁ hab₁
    (subset_trans (subset_tsupport _) hs₁f)
  obtain ⟨B₂,hB₂,hm₂⟩:=horacle fresh₂ af₂ bf₂ haf₂ hab₂
    (subset_trans (subset_tsupport _) hs₂f)
  refine ⟨B₁+B₂,by linarith,?_⟩
  intro q hq
  obtain ⟨J₁,C₁,Z₁,hC₁,hZ₁,hm₁⟩:=hm₁ q hq
  obtain ⟨J₂,C₂,Z₂,hC₂,hZ₂,hm₂⟩:=hm₂ q hq
  let J:=J₁+J₂
  obtain ⟨Cp,hCp,hphysical⟩:=hphysical J K U π hU hπ
  refine ⟨J,Cp*(C₁+C₂),max Z₁ Z₂,mul_pos hCp (add_pos hC₁ hC₂),lt_max_of_lt_left hZ₁,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec slots hslots lists Hslot a hHslot hP ha hv hv0 hadm Ψ hΨ hperiod
    S hdiv hf j D B v θ H R m η hR hη c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn w hw labels rows hlabels hrows hneg hchild hclip hReq hstate hgoodA
  have hZp:1<Z:=hZ₁.trans_le ((le_max_left _ _).trans hZ)
  have hD₁:B₁*Z^Lp≤Dpool:=
    (mul_le_mul_of_nonneg_right (by linarith : B₁≤B₁+B₂) (Real.rpow_nonneg (by linarith) _)).trans hD
  have hD₂:B₂*Z^Lp≤Dpool:=
    (mul_le_mul_of_nonneg_right (by linarith : B₂≤B₁+B₂) (Real.rpow_nonneg (by linarith) _)).trans hD
  have hmoment₁:=hm₁ Z ((le_max_left _ _).trans hZ) Dpool hD₁ slots hslots lists Hslot a hHslot hP ha
    hv hv0 hadm Ψ hΨ hperiod
  have hmoment₂:=hm₂ Z ((le_max_right _ _).trans hZ) Dpool hD₂ slots hslots lists Hslot a hHslot hP ha
    hv hv0 hadm Ψ hΨ hperiod
  have hbound:=hphysical p hp hcop hg
    (InverseInitialRayAttachment.poolPrimary_injective F hFa)
    (InverseInitialRayAttachment.poolPrimary_primary F hFa) (poolPrimary_odd F hFa)
    S hdiv hf Finset.univ Ψ hΨ j slots hslots lists a ha
    Z D B v θ H R m η hZp hR (mul_nonneg hη (Real.log_pos hZp).le)
    c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn w hw labels rows
    (fun f hf=>(hlabels f hf).1.1) hneg hchild
    (max 0 (columnCenter D B v)+(θ+v)) ((C₁+C₂)*(1+hv)^(2*J)) (eps+4*η) (by positivity) hclip
    (by unfold columnCenter;ring) hReq ?_
  · convert hbound using 1
    rw [show m+11*η+π+(eps+4*η)=m+15*η+π+eps by ring]
    ring
  · intro s ρ A₁ hA₁ A₂ hA₂ t ht
    obtain ⟨hm,hV,hM,hQ,hnorm⟩:=hstate t
      (quotientSet_assignedSourceInj_subset p S A₁ A₂ lists lists ht)
    obtain ⟨hg1,hg2⟩:=hgoodA A₁ hA₁ A₂ hA₂ t ht
    have hweight:∀f∈labels,((idealDivisors f).card:ℝ)^(A₁.card+A₂.card+1)≤secondLabelWeight K f:=by
      intro f hf
      exact assigned_label_weight_le slots A₁ A₂ K hslots (Finset.mem_powerset.mp hA₁)
        (Finset.mem_powerset.mp hA₂) f (hlabels f hf).1.1
    have hleft:=initial_child_from_good_inj p hp hcop hg Good Finset.univ Ψ
      (secondRayMinus Ψ ρ) slots (slots\A₁) lists a Hslot fresh₁ Z eps C₁ hv
      (max 0 (columnCenter D B v)) (θ+v) (θ+H+2*η) (fullPunctureWidth Z t j) η K J₁
      (j*primaryGenerator t) hZp ((show IsBaseRayTwist Ψ Ψ from Or.inl rfl).secondMinus ρ) hm
      (le_max_left _ _) hV hM hQ hg1 hnorm Finset.sdiff_subset labels hlabels rows hrows
      _ (by intros;positivity) hweight s hmoment₁
    have hright:=initial_child_from_good_inj p hp hcop hg Good Finset.univ Ψ
      (secondRayPlus Ψ ρ) slots (slots\A₂) lists a Hslot fresh₂ Z eps C₂ hv
      (max 0 (columnCenter D B v)) (θ+v) (θ+H+2*η) (fullPunctureWidth Z t j) η K J₂
      (j*primaryGenerator t) hZp ((show IsBaseRayTwist Ψ Ψ from Or.inl rfl).secondPlus ρ) hm
      (le_max_left _ _) hV hM hQ hg2 hnorm Finset.sdiff_subset labels hlabels rows hrows
      _ (by intros;positivity) hweight s hmoment₂
    constructor
    · apply hleft.trans
      have hexp:max 0 (columnCenter D B v)+(θ+v)+eps+4*η=
        max 0 (columnCenter D B v)+(θ+v)+(eps+4*η):=by ring
      rw [hexp]
      exact height_moment_le hC₁.le (by linarith) (Real.rpow_nonneg (by linarith) _) hv0
        (by dsimp [J]; omega)
    · apply hright.trans
      have hexp:max 0 (columnCenter D B v)+(θ+v)+eps+4*η=
        max 0 (columnCenter D B v)+(θ+v)+(eps+4*η):=by ring
      rw [hexp]
      exact height_moment_le hC₂.le (by linarith) (Real.rpow_nonneg (by linarith) _) hv0
        (by dsimp [J]; omega)

theorem retained_window_bound_inj
    (W₁ W₂:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)(Φ:𝓢(ℝ,ℂ))
    (lo hi:Fin 4→ℝ)(hlo:∀i,0<lo i)(hhi:∀i,lo i≤hi i)
    (Adm:SlotAdm)(Pmax Smax κ Lp eps U π:ℝ)(heps:0<eps)(hU:0≤U)(hπ:0<π)(K:ℕ)
    (horacle:∀(Wf:𝓢(ℝ,ℂ))(lf hf:ℝ),0<lf→lf≤hf→Function.support (Wf:ℝ→ℂ)⊆Set.Icc lf hf→
      GoodEnergyExistsInj Adm (InitState Pmax Smax κ) eps Lp K Wf):
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
        (primeMarkInj (all\assigned) lists coeff)
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
  obtain ⟨Btree,hBtree,hbound⟩:=retained_physical_bound_inj
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
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hHs hPs hac hv hv0 hadm
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
      (assignedElement assigned qelem) (primeMarkInj (all\assigned) lists coeff)
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m=0
  · rw [hempty,norm_zero];positivity
  have hclip:= (InverseInitialEnergyCallerEmpty.physical_nonzero_clipping p hp hcop hg
    hprimary Finset.univ Sc hdivc hfc' (w∘erasePoint) Ψ (assignedElement assigned qelem)
    (primeMarkInj (all\assigned) lists coeff) W₁ W₂ fresh fresh (fun i=>Vlog i) Φ
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
  have hHlow' : ∀ i ∈ all\assigned, ∀ P ∈ lists i,
      Hslot i ≤ 2*(Ideal.absNorm (Ideal.span {poolPrimary F P}) : ℝ) := by
    intro i hi P hP
    rw [poolPrimary_span F hFa P]
    exact hHlow i hi P hP
  have hScw : Sc ⊆ windowSource p S ψ Z D B v θ H := Finset.filter_subset _ _
  have hgoodA : ∀J₁∈(all\assigned).powerset,∀J₂∈(all\assigned).powerset,
      ∀t∈quotientSet p (assignedSourceInj Sc J₁ J₂ lists lists),
      InitState Pmax Smax κ (max 0 (columnCenter D B v)) (θ+v+2*η) (θ+H+2*η)
        (fullPunctureWidth Z t (assignedElement assigned qelem))
        (Real.logb Z (∏i∈(all\assigned)\J₁,Hslot i)) ∧
      InitState Pmax Smax κ (max 0 (columnCenter D B v)) (θ+v+2*η) (θ+H+2*η)
        (fullPunctureWidth Z t (assignedElement assigned qelem))
        (Real.logb Z (∏i∈(all\assigned)\J₂,Hslot i)) := by
    intro J₁ hJ₁ J₂ hJ₂ t ht
    obtain ⟨x,hx,f₁,f₂,rfl,hl₁,hm₁,hi₁,hl₂,hm₂,hi₂⟩ := assigned_quotient_cases_inj p Sc J₁ J₂ lists ht
    constructor
    · exact window_initState_assigned_inj p hp hprimary S ψ lo hi hψ Z D B v θ H η hZp hη hhiZ hloZ
        hdiv hf all assigned hassigned qelem z al bl primeW hz hqe hprimeW hprimeLive hprodj
        lists Hslot K hK hHs hHlow' hprod hlow hKη Sc hScw J₁ (Finset.mem_powerset.mp hJ₁)
        x hx f₁ hl₁ hm₁ hi₁ m r τ Pmax Smax κ hDeq hr0 hrP hzS hm1 hτ0 hκ hrad hclip
    · exact window_initState_assigned_inj p hp hprimary S ψ lo hi hψ Z D B v θ H η hZp hη hhiZ hloZ
        hdiv hf all assigned hassigned qelem z al bl primeW hz hqe hprimeW hprimeLive hprodj
        lists Hslot K hK hHs hHlow' hprod hlow hKη Sc hScw J₂ (Finset.mem_powerset.mp hJ₂)
        x hx f₂ hl₂ hm₂ hi₂ m r τ Pmax Smax κ hDeq hr0 hrP hzS hm1 hτ0 hκ hrad hclip
  apply hbound Z hZ Dpool hD (all\assigned) ((Finset.card_le_card Finset.sdiff_subset).trans hK)
    lists Hslot coeff hHs hPs hac
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

theorem retained_sum_bound_inj
    (W₁ W₂:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)(Φ:𝓢(ℝ,ℂ))
    (Adm:SlotAdm)(Pmax Smax κ Lp:ℝ)
    (cap eps π η τ loss:ℝ)(hcap:0≤cap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(_hηone:η≤1)(hτ:0<τ)(hκ:8*η+τ≤κ)(hloss:0<loss)(K:ℕ)
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
    ∀(D m r T:ℝ),0≤m→0<T→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      Z^(assignedCenter (all\assigned) z)≤(∏i∈all\assigned,Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,Hslot i≤2*(P.val.absNorm:ℝ))→(2:ℝ)^K≤Z^η→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      0≤Pmax→ r≤Pmax→assignedCenter all z≤Smax→1≤m→
      r+assignedCenter all z+7*η≤cap→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),1≤c₁→c₁≤bcap→1≤c₂→c₂≤bcap→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
      ‖∑k∈retainedWindows (fun _=>1) (physicalCaps (max 1 b₀) Z D T) Z D m (4*η+τ),
        windowBlock p hp hcop hg Finset.univ
          (cappedSource p S (fun _=>1) (physicalCaps (max 1 b₀) Z D T)) w Ψ
          (assignedElement assigned qelem) (primeMarkInj (all\assigned) lists coeff)
          (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m (fun i=>(k i).val)‖≤
        C*(1+hv)^(2*degree)*Z^(m+15*η+π+eps+loss)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  have hb:0<max 1 b₀:=zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨Btree,Tclip,hBtree,hTclip,hwindow⟩:=
    retained_window_bound_inj W₁ W₂ a₀ b₀ bcap ha₀ hbcap hs₁ hs₂ hW₁ hW₂ Φ
      (fun _=>1/4) (fun _=>1) (by intros;norm_num) (by intros;norm_num)
      Adm Pmax Smax κ Lp eps (cap+3) π heps (by linarith) hπ K horacle
  obtain ⟨A,hA,hcount⟩:=retained_card_subpower (max 1 b₀) cap (4*η+τ) loss hb hcap (by positivity) hloss
  have hpowers:∀ᶠZ:ℝ in atTop,(4:ℝ)≤Z^η:=
    (tendsto_rpow_atTop hη).eventually (eventually_ge_atTop 4)
  have hlogs:∀ᶠZ:ℝ in atTop,Tclip≤3*η*Real.log Z:=by
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Tclip/(3*η)))] with Z hZ
    exact (div_le_iff₀ (by positivity : 0<3*η)).mp hZ |>.trans_eq (mul_comm _ _)
  have hevent:=window_exponent_eventual_upper (max 1 b₀) 1 hb (by norm_num)
  obtain ⟨Zaux,haux⟩:=eventually_atTop.mp (hcount.and (hpowers.and (hlogs.and hevent)))
  refine ⟨Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨J,C,Zq,hC,hZq,hw⟩:=hwindow q hq
  refine ⟨J,A*C,max Zq Zaux,mul_pos hA hC,lt_max_of_lt_left hZq,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hHs hPs hac hv hv0 hadm
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf D m r T hm hT
    hprodj hprod hlow hHlow hKη hDeq hr0 hrP hzS hm1 hparent c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hweight
  have hZq':Zq≤Z:=(le_max_left _ _).trans hZ
  obtain ⟨hcZ,hpow,hlog,hexp⟩:=haux Z ((le_max_right _ _).trans hZ)
  have hZp:1<Z:=hZq.trans_le hZq'
  have hDcap:D≤cap:=by
    have hg:0≤assignedCenter assigned z:=Finset.sum_nonneg (fun i hi=>hz i (hassigned hi))
    rw [hDeq]
    linarith
  let Sc:=cappedSource p S (fun _=>1) (physicalCaps (max 1 b₀) Z D T)
  have hdivc:∀x∈Sc,x.divisor⊆x.common:=fun x hx=>hdiv x (Finset.mem_filter.mp hx).1
  have hfc:∀x∈Sc,x.frequency≠0:=fun x hx=>hf x (Finset.mem_filter.mp hx).1
  have hlo:Z^(-η)≤(1/4:ℝ):=by
    rw [Real.rpow_neg (zero_lt_one.trans hZp).le]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ)<4) hpow
  have hnorm (k:Windows (fun _=>1) (physicalCaps (max 1 b₀) Z D T))
      (hk:k∈retainedWindows (fun _=>1) (physicalCaps (max 1 b₀) Z D T) Z D m (4*η+τ)):
      ‖windowBlock p hp hcop hg Finset.univ Sc w Ψ (assignedElement assigned qelem)
        (primeMarkInj (all\assigned) lists coeff) (clippedSource W₁ c₁ θ₁)
        (clippedSource W₂ c₂ θ₂) Φ Z D m (fun i=>(k i).val)‖≤
        C*(1+hv)^(2*J)*Z^(m+15*η+π+eps)*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)):=by
    have hsize:0<max 1 b₀*Z^D:=mul_pos hb (Real.rpow_pos_of_pos (zero_lt_one.trans hZp) D)
    have h0:=hexp.2 (max 1 b₀*Z^D) D hsize le_rfl (k 0).val (k 0).property
    have h1:=hexp.2 (max 1 b₀*Z^D) D hsize le_rfl (k 1).val (k 1).property
    apply hw Z hZq' Dpool hD all assigned hassigned hK lists Hslot coeff hHs hPs hac hv hv0 hadm
      qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod Sc hdivc hfc cutoff
      (fun i x hx=>Set.Ioo_subset_Icc_self (cutoff_support i hx))
      D (exponent Z (k 0).val) (exponent Z (k 2).val) (exponent Z (k 1).val)
      (exponent Z (k 3).val) m r η τ hη.le hτ.le hκ
      (fun _=>by linarith) hlo hlog hprodj hprod hlow hHlow hKη hDeq hr0 hrP hzS hm1
      (by linarith [h0.2,h1.1]) (Finset.mem_filter.mp hk).2 c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂
      (fun x=>w x*outerCutoff cutoff (sourceRelative p x Z D (exponent Z (k 0).val)
        (exponent Z (k 2).val) (exponent Z (k 1).val) (exponent Z (k 3).val))) ?_
    intro x hx
    rw [norm_mul]
    have hmul {a b : ℝ} (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
      (mul_le_of_le_one_left hb₀ ha).trans hb
    apply hmul (hweight x (Finset.mem_filter.mp hx).1) (by positivity)
    unfold outerCutoff
    simp only [norm_mul]
    exact hmul (hmul (hmul (cutoff_norm_le _ _) (by positivity)
      (cutoff_norm_le _ _)) (by positivity) (cutoff_norm_le _ _)) (by positivity) (cutoff_norm_le _ _)
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hnorm).trans
  rw [Finset.sum_const, nsmul_eq_mul]
  calc
    _≤(A*Z^loss)*(C*(1+hv)^(2*J)*Z^(m+15*η+π+eps)*
        ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J))):=
      mul_le_mul_of_nonneg_right (hcZ D m (4*η+τ) T hDcap hm le_rfl hT) (by positivity)
    _=_:=by rw [Real.rpow_add (zero_lt_one.trans hZp) (m+15*η+π+eps) loss];ring

end
end Qrh.MarkedAnchor.Inverse.Inj

#print axioms Qrh.MarkedAnchor.Inverse.Inj.retained_physical_bound_inj
#print axioms Qrh.MarkedAnchor.Inverse.Inj.retained_sum_bound_inj
