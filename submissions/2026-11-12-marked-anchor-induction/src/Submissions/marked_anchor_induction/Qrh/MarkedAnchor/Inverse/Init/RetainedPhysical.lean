/- Copyright (c) 2026 Sil. Apache-2.0. -/
/- Adapted from openai_baseline `OAI/NumberTheory/DirichletL/Inversion/InitialRetainedPhysical.lean`
and `Inversion/InitialCanonicalEnergy.lean` (Apache-2.0).
Modified by Sil (2026-11-11): the native canonical energy `canonical_marked_energy_exists` and the
`CanonicalMargins` of the window states are replaced by the oracle `GoodEnergyExists Adm Good`
(Inverse.Oracle) and the state predicate `Good`; the slot data carry the filter `Adm` and the
two-sided live width `Z^(z-lag) ≤ ∏ H ≤ Z^z`; the pool exponent `cap+1` becomes the oracle's `Lp`. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialRetainedPhysical
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Oracle
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Caller.Assigned

/-!
# Inverse.Init.RetainedPhysical — first file of the oracle-parametric initialization chain

`retained_physical_bound_of_oracle` is the baseline `retained_physical_bound` with the canonical
energy supplied by the oracle `GoodEnergyExists Adm Good lag eps Lp K` for every fresh compactly
supported profile, and with `Good` in place of `CanonicalMargins` on the window states. The oracle
enters through the energy hypothesis `_hmoment` of `actual_physical_reference_bound`; the later
files of the chain only pass `hstate`/margins through.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
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
local notation "O" => ActualEisensteinCubic.O

section Child
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

/-- `initial_child_from_rank` with the oracle `GoodRankMoments` (baseline
`InitialCanonicalEnergy.lean:48`). -/
theorem initial_child_from_good (Good : StatePred) (pool : Finset ι) (base Ψ : O →* ℂ)
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
    (hmoment : GoodRankMoments p hp hcop hg Good pool base slots lists a H W Z eps A hv K degree) :
    normalizedColumnEnergy p hp hcop hg pool Ψ m subslots lists a labels rows weight
      (childLogTest W s) (Z^N) Z (N+V) ≤ A*Z^(N+V+eps+4*η)*(1+‖s‖+hv)^(2*degree) := by
  have hcanon := hmoment Ψ hbase m hm N (V+2*η) M Q hN hV hM hQ hmnorm
    subslots hsub hgood labels hlabels s
  rw [InverseInitialCanonicalEnergy.normalization_change p hp hcop hg pool Ψ m subslots lists a
    labels rows weight (childLogTest W s) (Z^N) Z (N+V) (N+(V+2*η)) (zero_lt_one.trans hZ)]
  apply (mul_le_mul_of_nonneg_left
    ((InverseInitialCanonicalEnergy.energy_range_weight_le p hp hcop hg pool Ψ m subslots lists a
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

/-- The height-aware oracle moment `C Y (1+‖s‖+hv)^(2a)` is a height-free moment with constant
`C' (1+hv)^(2b)` (`C ≤ C'`, `a ≤ b`). -/
theorem height_moment_le {C C' Y s hv : ℝ} {a b : ℕ} (hC : 0 ≤ C) (hCC : C ≤ C') (hY : 0 ≤ Y)
    (hv0 : 0 ≤ hv) (hab : a ≤ b) :
    C*Y*(1+‖s‖+hv)^(2*a) ≤ (C'*(1+hv)^(2*b))*Y*(1+‖s‖)^(2*b) := by
  have h1 := heightPow_split s hv hv0 (2*a)
  have h2 : (1+hv)^(2*a) ≤ (1+hv)^(2*b) := hvPow_mono hv0 (by omega)
  have h3 : (1+‖s‖)^(2*a) ≤ (1+‖s‖)^(2*b) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg s]) (by omega)
  have hv1 : 0 ≤ (1+hv)^(2*a) := by positivity
  have hs1 : 0 ≤ (1+‖s‖)^(2*a) := by positivity
  have hs2 : 0 ≤ (1+‖s‖+hv)^(2*a) := by positivity
  calc C*Y*(1+‖s‖+hv)^(2*a) ≤ C*Y*((1+hv)^(2*a)*(1+‖s‖)^(2*a)) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hC hY)
    _ ≤ C'*Y*((1+hv)^(2*b)*(1+‖s‖)^(2*b)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hCC hY) (mul_le_mul h2 h3 hs1 (hv1.trans h2))
          (mul_nonneg hv1 hs1) (mul_nonneg (hC.trans hCC) hY)
    _ = (C'*(1+hv)^(2*b))*Y*(1+‖s‖)^(2*b) := by ring

/-- The baseline `retained_physical_bound` with the canonical energy supplied by the oracle. -/
theorem retained_physical_bound_of_oracle
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
      GoodEnergyExists Adm Good eps Lp K Wf):
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
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,1≤Hslot i)→
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
        ∀t∈quotientSet p (assignedSource S J₁ J₂ lists lists),
        Good (max 0 (columnCenter D B v)) (θ+v+2*η) (θ+H+2*η) (fullPunctureWidth Z t j)
          (Real.logb Z (∏i∈slots\J₁,Hslot i)) ∧
        Good (max 0 (columnCenter D B v)) (θ+v+2*η) (θ+H+2*η) (fullPunctureWidth Z t j)
          (Real.logb Z (∏i∈slots\J₂,Hslot i)))→
      ‖physicalBlock p hp hcop hg (pointSource Finset.univ S) (w∘erasePoint) Ψ j
        (primeMark slots lists a) (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*(1+hv)^(2*degree)*Z^(m+15*η+π+eps)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  obtain ⟨fresh₁,fresh₂,hsf₁,hsf₂,hphysical⟩:=
    actual_physical_reference_bound_assigned
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
  intro p hp hcop hg σ dec slots hslots lists Hslot a hdis hHslot hP ha hv hv0 hadm Ψ hΨ hperiod
    S hdiv hf j D B v θ H R m η hR hη c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn w hw labels rows hlabels hrows hneg hchild hclip hReq hstate hgoodA
  have hZp:1<Z:=hZ₁.trans_le ((le_max_left _ _).trans hZ)
  have hD₁:B₁*Z^Lp≤Dpool:=
    (mul_le_mul_of_nonneg_right (by linarith : B₁≤B₁+B₂) (Real.rpow_nonneg (by linarith) _)).trans hD
  have hD₂:B₂*Z^Lp≤Dpool:=
    (mul_le_mul_of_nonneg_right (by linarith : B₂≤B₁+B₂) (Real.rpow_nonneg (by linarith) _)).trans hD
  have hmoment₁:=hm₁ Z ((le_max_left _ _).trans hZ) Dpool hD₁ slots hslots lists Hslot a hdis hHslot hP ha
    hv hv0 hadm Ψ hΨ hperiod
  have hmoment₂:=hm₂ Z ((le_max_right _ _).trans hZ) Dpool hD₂ slots hslots lists Hslot a hdis hHslot hP ha
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
      (InverseInitialEnergyCallerMass.assigned_quotient_subset p S A₁ A₂ lists lists ht)
    obtain ⟨hg1,hg2⟩:=hgoodA A₁ hA₁ A₂ hA₂ t ht
    have hweight:∀f∈labels,((idealDivisors f).card:ℝ)^(A₁.card+A₂.card+1)≤secondLabelWeight K f:=by
      intro f hf
      exact assigned_label_weight_le slots A₁ A₂ K hslots (Finset.mem_powerset.mp hA₁)
        (Finset.mem_powerset.mp hA₂) f (hlabels f hf).1.1
    have hleft:=initial_child_from_good p hp hcop hg Good Finset.univ Ψ
      (secondRayMinus Ψ ρ) slots (slots\A₁) lists a Hslot fresh₁ Z eps C₁ hv
      (max 0 (columnCenter D B v)) (θ+v) (θ+H+2*η) (fullPunctureWidth Z t j) η K J₁
      (j*primaryGenerator t) hZp ((show IsBaseRayTwist Ψ Ψ from Or.inl rfl).secondMinus ρ) hm
      (le_max_left _ _) hV hM hQ hg1 hnorm Finset.sdiff_subset labels hlabels rows hrows
      _ (by intros;positivity) hweight s hmoment₁
    have hright:=initial_child_from_good p hp hcop hg Good Finset.univ Ψ
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

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.retained_physical_bound_of_oracle
