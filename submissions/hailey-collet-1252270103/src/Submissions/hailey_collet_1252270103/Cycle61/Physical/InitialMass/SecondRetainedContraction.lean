/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondNormalizedWindows
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondRatioCap

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentSourceLiveColumn CenteredMomentCommonPairedSource
open CenteredMomentAmplificationChildInput CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentLogDyadic CenteredMomentOriginalCommonHarmonic CenteredMomentSecondLocalization
open CenteredMomentSecondBlockAggregate
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondLiveBlock
open CenteredMomentActiveSource CenteredMomentFirstSectors CenteredMomentSourceRow
open Cycle61Moment RayFourExpansion CenteredMomentCommonHeightEnvelope
open CenteredMomentSourceMass CenteredMomentSecondActivePhysicalDictionary
local notation "O" => HeckeFamily.O
local instance secondRestrictedSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Change only the physical row set. The original input, character family,
Fourier scale and dyadic block coordinates remain literal. -/
def ordinarySecondDatum (d : SecondInputDatum α) (χ : RayCharacter) (Q : Ideal O) (m : O) :
    SecondInputDatum α :=
  {d with
    rows:=partRows false d.input.η χ Q m d.C d.D d.inactive d.radius
    rows_ne:=fun z hz=>sourceRows_nonzero d.C d.D d.inactive d.radius z
      (Finset.mem_filter.mp hz).1}

@[simp] theorem ordinary_second_dyad (d : SecondInputDatum α)
    (χ : RayCharacter)(Q : Ideal O)(m : O)(i : Fin 4) :
    (ordinarySecondDatum d χ Q m).block.dyad i=d.block.dyad i := rfl

@[simp] theorem ordinary_second_ratio (d : SecondInputDatum α)
    (χ : RayCharacter)(Q : Ideal O)(m : O) :
    secondRatioIndex (ordinarySecondDatum d χ Q m).block=secondRatioIndex d.block := rfl

/-- The two full positive normalized sums, on the rows of the supplied
restricted datums. Residual ideals and all source labels stay in the sum. -/
def secondNormalizedSum {Label : Type*}[Fintype Label]
    (reflected : Bool)(d : Label→SecondInputDatum α)(w : Label→ℂ)(t u : ℝ) : ℝ :=
  ∑r∈secondLiveRows (fun l=>(d l).block),
    ∑L∈secondResidualIdeals (fun l=>(d l).block) r,
      (‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData)*
        (if reflected then
          ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.2.1⁻¹)
            ((d r.1).input.t+2*Real.pi*(u-(-t))))
            (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed L (-r.2.2.2.val)‖^2
         else
          ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.1)
            ((d r.1).input.t+2*Real.pi*(u-t)))
            (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed L r.2.2.2.val‖^2)

lemma normalized_balance_sqrt (E H T : ℝ)(hE : 0≤E)(hH : 0<H)(hT : 0≤T) :
    Real.sqrt (E*H*T)*Real.sqrt (E/H*T)=E*T := by
  rw [←Real.sqrt_mul (mul_nonneg (mul_nonneg hE hH.le) hT)]
  have heq : E*H*T*(E/H*T)=(E*T)^2 := by field_simp
  rw [heq,Real.sqrt_sq_eq_abs,abs_of_nonneg (mul_nonneg hE hT)]

/-- Literal full positive normalized sums on every exact ratio fiber. -/
def SecondNormalizedBound {Label : Type*}[Fintype Label]
    (W : 𝓢(ℝ,ℂ))(degree windowDegree : ℕ)
    (d : Label→SecondInputDatum α)(w : Label→ℂ)(E H : ℤ→ℝ) : Prop :=
  ∀r∈secondRatioBins (fun l=>(d l).block),∀(reflected : Bool)(t u : ℝ),
        let datum:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>d l.val;
        let src:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>(datum l).block;
        let weight:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>w l.val;
        secondNormalizedSum reflected datum (secondEffectiveWeight src weight W) t u≤
          ((if reflected then E r/H r else E r*H r)*(1+‖t‖)^degree)*
            (1+‖u‖)^(2*windowDegree)

/-- Joint restricted physical block contraction from literal positive sums
on each exact ratio fiber. Constants precede the moving datum family. -/
theorem restricted_second_ratio_from_normalized (W : 𝓢(ℝ,ℂ))(A degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ,0≤C ∧ ∀{Label : Type*}[Fintype Label]
    (d : Label→SecondInputDatum α)(w : Label→ℂ)(E H : ℤ→ℝ),
      (∀r∈secondRatioBins (fun l=>(d l).block),0≤E r) →
      (∀r∈secondRatioBins (fun l=>(d l).block),0<H r) →
      SecondNormalizedBound W degree windowDegree d w E H →
      ‖∑l,w l*(d l).block.value W‖≤
        C*∑r∈secondRatioBins (fun l=>(d l).block),E r/(1+dyadicScale r)^A := by
  obtain ⟨C,hC,hcon⟩:=actual_second_ratio_contraction W A degree
  let IL:=|∫u : ℝ,(1+‖u‖)^windowDegree*‖columnDensity logAnnulus hc hs u‖|
  let IR:=|∫u : ℝ,(1+‖u‖)^windowDegree*‖columnDensity (fun x=>star (logAnnulus x))
    (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
    (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hs) u‖|
  refine ⟨C*IL*IR,by dsimp [IL,IR];positivity,?_⟩
  intro Label _ d w E H hE hH hnorm
  have hh:=hcon (fun l=>(d l).block) w (fun r=>E r*IL*IR)
    (fun r hr=>by have he:=hE r hr; dsimp [IL,IR];positivity) ?_
  · apply hh.trans_eq
    simp_rw [show ∀ r : ℤ, E r*IL*IR/(1+dyadicScale r)^A =
      E r/(1+dyadicScale r)^A*IL*IR by intro r; ring]
    rw [←Finset.sum_mul,←Finset.sum_mul]
    ring
  · intro r hr t
    let datum:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>d l.val
    let src:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>(datum l).block
    let weight:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>w l.val
    let ew:=secondEffectiveWeight src weight W
    have hleft:=hnorm r hr false t
    have hright:=hnorm r hr true t
    have hEt : 0≤E r*H r*(1+‖t‖)^degree := by have he:=hE r hr; have hh:=hH r hr; positivity
    have hEr : 0≤E r/H r*(1+‖t‖)^degree := by have he:=hE r hr; have hh:=hH r hr; positivity
    have hb:=actual_balanced_energy_from_normalized datum ew t windowDegree
      (E r*H r*(1+‖t‖)^degree) (E r/H r*(1+‖t‖)^degree) hEt hEr hc hs
      (fun u=>by simpa only [secondNormalizedSum,Bool.false_eq_true,ite_false] using hleft u)
      (fun u=>by simpa only [secondNormalizedSum,ite_true] using hright u)
    rw [normalized_balance_sqrt (E r) (H r) ((1+‖t‖)^degree) (hE r hr) (hH r hr)
      (by positivity)] at hb
    exact hb.trans_eq (by dsimp [IL,IR];ring)

/-- Ordinary restriction leaves the exact ratio image unchanged. -/
@[simp] theorem ordinary_second_ratio_bins {Label : Type*}[Fintype Label]
    (d : Label→SecondInputDatum α)(χ : Label→RayCharacter)
    (Q : Label→Ideal O)(m : Label→O) :
    secondRatioBins (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block)=
      secondRatioBins (fun l=>(d l).block) := rfl

/-- Literal ordinary part of the original retained energy, preserving the
single weighted block sum. No restricted block is required to be nonzero. -/
theorem actual_original_ordinary_assembly (slots : Finset α) (s : Input slots)
    (R seed : Ideal O) (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (χ : RayCharacter)(Q : Ideal O)(m : O)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    partEnergy false s.η χ Q m s.t (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s R seed) W K Tsec Z ξ (sourceRadius s)=
      ∑q : ActualSecondBlockIndex s R seed K Tsec Z ξ,
        actualSecondBlockWeight s R seed K Tsec Z ξ q*
          (ordinarySecondDatum
            (actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q)
            χ Q m).block.value W := by
  unfold partEnergy
  rw [Fintype.sum_sigma]
  conv_lhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [actualSecondBlockWeight,ordinarySecondDatum,actualSecondBlockDatum,
    actualSecondInputDatum,SecondInputDatum.block,originalSecondBlock,SecondBlockSource.value]
  apply congrArg (fun x : ℂ=>heightCoeff s.η s.t p.val.val.1*
    star (heightCoeff s.η s.t p.val.val.2)*x)
  exact (physicalBlock_active s.η s.t _ _ _ _ _ _ U _ _ W K _).symm

/-- Heterogeneous ordinary parts remain one joint physical block sum. -/
theorem actual_joint_ordinary_assembly {Label : Type*} [Fintype Label]
    (slots : Label→Finset α) (s : (l : Label)→Input (slots l))
    (R seed : Label→Ideal O) (hseed : ∀l,Squarefree (seed l))
    (hz₁ : ∀l,(s l).W₁ 0=0) (hz₂ : ∀l,(s l).W₂ 0=0)
    (χ : Label→RayCharacter)(Q : Label→Ideal O)(m : Label→O)
    (W : 𝓢(ℝ,ℂ)) (K Tsec : Label→ℝ) (Z ξ : ℝ) (hK : ∀l,0<K l)
    (weight : Label→ℂ) :
    (∑l,weight l*partEnergy false (s l).η (χ l) (Q l) (m l) (s l).t
      (finiteColumns (Fintype.piFinset (s l).pools)) (coefficient (s l) (R l) (seed l))
        W (K l) (Tsec l) Z ξ (sourceRadius (s l)))=
      ∑q : (l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ,
        (weight q.1*actualSecondBlockWeight (s q.1) (R q.1) (seed q.1) (K q.1) (Tsec q.1) Z ξ q.2)*
          (ordinarySecondDatum
            (actualSecondBlockDatum (slots q.1) (s q.1) (R q.1) (seed q.1)
              (hseed q.1) (hz₁ q.1) (hz₂ q.1) (K q.1) (Tsec q.1) Z ξ (hK q.1) q.2)
            (χ q.1) (Q q.1) (m q.1)).block.value W := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro l hl
  rw [actual_original_ordinary_assembly (slots l) (s l) (R l) (seed l)
    (hseed l) (hz₁ l) (hz₂ l) (χ l) (Q l) (m l) W (K l) (Tsec l) Z ξ (hK l),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact (mul_assoc _ _ _).symm

/-- Actual source-block ratio cardinality survives ordinary restriction;
conductor caps are still discharged by the original polynomial support. -/
theorem actual_ordinary_ratio_bins_subpower
    (A D₀ B L Cr ε : ℝ)(hA : 0≤A)(hD₀ : 0≤D₀)(hB : 0≤B)(hL : 0≤L)
    (hCr : 0<Cr)(hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ ∀ᶠZ : ℝ in atTop,
    ∀{Label : Type*}[Fintype Label](slots : Label→Finset α)(s : (l : Label)→Input (slots l))
      (R seed : Label→Ideal O)(hseed : ∀l,Squarefree (seed l))
      (hz₁ : ∀l,(s l).W₁ 0=0)(hz₂ : ∀l,(s l).W₂ 0=0)
      (K Tsec : Label→ℝ)(ξ : ℝ)(hK : ∀l,0<K l),
      (∀l,Z^(-D₀)≤K l) → (∀l,K l≤Z^A) →
      (∀l,frequencyRadius (Tsec l) Z ξ≤Cr*Z^L) → (∀l,sourceRadius (s l)≤Z^B) →
    ∀(q : (l : Label)→ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ)
      (χ : Label→RayCharacter)(Q : Label→Ideal O)(m : Label→O),
      ((secondRatioBins (fun l=>(ordinarySecondDatum
        (actualSecondBlockDatum (slots l) (s l) (R l) (seed l)
          (hseed l) (hz₁ l) (hz₂ l) (K l) (Tsec l) Z ξ (hK l) (q l))
        (χ l) (Q l) (m l)).block)).card:ℝ)≤C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩:=actual_second_datum_ratio_bins_subpower (α:=α)
    A D₀ B L Cr ε hA hD₀ hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount] with Z hcount
  intro Label _ slots s R seed hseed hz₁ hz₂ K Tsec ξ hK hKlo hKhi hR hsource q χ Q m
  simpa only [ordinary_second_ratio_bins] using
    hcount slots s R seed hseed hz₁ hz₂ K Tsec ξ hK hKlo hKhi hR hsource q

/-- A genuine absolute dyadic envelope pays only the ratio-image overhead,
not the number of arithmetic source labels. Rows may already be restricted. -/
theorem actual_restricted_second_subpower (W : 𝓢(ℝ,ℂ))
    (decay degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (A D₀ B L Cr ε : ℝ)(hA : 0≤A)(hD₀ : 0≤D₀)(hB : 0≤B)(hL : 0≤L)
    (hCr : 0<Cr)(hε : 0<ε) :
    ∃C : ℝ,0≤C ∧ ∀ᶠZ : ℝ in atTop,
    ∀{Label : Type*}[Fintype Label](d : Label→SecondInputDatum α)
      (w : Label→ℂ)(sourceCap : Label→ℝ)(H : ℤ→ℝ)(E₀ : ℝ),0≤E₀ →
      (∀l,Z^(-D₀)≤(d l).K) → (∀l,(d l).K≤Z^A) →
      (∀l,(d l).radius≤Cr*Z^L) → (∀l,sourceCap l≤Z^B) →
      (∀l,((d l).C.absNorm:ℝ)≤Z^B) → (∀l,((d l).D.absNorm:ℝ)≤Z^B) →
    ∀n : (l : Label)→SourceBlocks (d l).C (d l).D (d l).inactive
        (d l).K (d l).radius (sourceCap l),
      (∀l i,(d l).dyad i=(n l i:ℤ)) →
      (∀r∈secondRatioBins (fun l=>(d l).block),0<H r) →
      SecondNormalizedBound W degree windowDegree d w (fun _=>E₀) H →
      ‖∑l,w l*(d l).block.value W‖≤C*E₀*Z^ε := by
  obtain ⟨C₁,hC₁,hcon⟩:=restricted_second_ratio_from_normalized (α:=α) W decay degree windowDegree hc hs
  obtain ⟨C₀,hC₀,hcount⟩:=actual_second_ratio_bins_subpower A D₀ B L Cr ε hA hD₀ hB hL hCr hε
  refine ⟨C₁*C₀,mul_nonneg hC₁ hC₀.le,?_⟩
  filter_upwards [hcount] with Z hcount
  intro Label _ d w sourceCap H E₀ hE hKlo hKhi hR hsource hNC hND n hdyad hH hnorm
  have hcard:=hcount (fun l=>(d l).block) (fun l=>(d l).C) (fun l=>(d l).D)
    (fun l=>(d l).hC) (fun l=>(d l).hD) (fun l=>(d l).sameSupport)
    (fun l=>(d l).inactive) (fun l=>(d l).K) (fun l=>(d l).radius) sourceCap
    (fun l=>(d l).K_pos) hKlo hKhi hR hsource hNC hND n hdyad
  have hh:=hcon d w (fun _=>E₀) H (fun _ _=>hE) hH hnorm
  have hsum : (∑r∈secondRatioBins (fun l=>(d l).block),E₀/(1+dyadicScale r)^decay)≤
      ((secondRatioBins (fun l=>(d l).block)).card:ℝ)*E₀ := by
    calc
      _ ≤ ∑r∈secondRatioBins (fun l=>(d l).block),E₀ := by
        apply Finset.sum_le_sum
        intro r hr
        exact div_le_self hE (one_le_pow₀ (by linarith [dyadicScale_pos r]))
      _ = _ := by simp
  have ht:=(hh.trans (mul_le_mul_of_nonneg_left hsum hC₁)).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hE) hC₁)
  exact ht.trans_eq (by ring)

/-- Direct whole ordinary-energy bound from the actual normalized ratio
fibers. All fixed Mellin constants precede sources, allocations and heights. -/
theorem actual_joint_ordinary_from_normalized (W : 𝓢(ℝ,ℂ))
    (decay degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ,0≤C ∧ ∀{Label : Type*}[Fintype Label]
    (slots : Label→Finset α) (s : (l : Label)→Input (slots l))
    (R seed : Label→Ideal O) (hseed : ∀l,Squarefree (seed l))
    (hz₁ : ∀l,(s l).W₁ 0=0) (hz₂ : ∀l,(s l).W₂ 0=0)
    (χ : Label→RayCharacter)(Q : Label→Ideal O)(m : Label→O)
    (K Tsec : Label→ℝ) (Z ξ : ℝ) (hK : ∀l,0<K l)(weight : Label→ℂ),
      let datum := fun q : (l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l)
        (K l) (Tsec l) Z ξ=>ordinarySecondDatum
          (actualSecondBlockDatum (slots q.1) (s q.1) (R q.1) (seed q.1)
            (hseed q.1) (hz₁ q.1) (hz₂ q.1) (K q.1) (Tsec q.1) Z ξ (hK q.1) q.2)
          (χ q.1) (Q q.1) (m q.1);
      let jointWeight := fun q : (l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l)
        (K l) (Tsec l) Z ξ=>weight q.1*
          actualSecondBlockWeight (s q.1) (R q.1) (seed q.1) (K q.1) (Tsec q.1) Z ξ q.2;
      ∀E H : ℤ→ℝ,
      (∀r∈secondRatioBins (fun q=>(datum q).block),0≤E r) →
      (∀r∈secondRatioBins (fun q=>(datum q).block),0<H r) →
      SecondNormalizedBound W degree windowDegree datum jointWeight E H →
      ‖∑l,weight l*partEnergy false (s l).η (χ l) (Q l) (m l) (s l).t
        (finiteColumns (Fintype.piFinset (s l).pools)) (coefficient (s l) (R l) (seed l))
        W (K l) (Tsec l) Z ξ (sourceRadius (s l))‖≤
          C*∑r∈secondRatioBins (fun q=>(datum q).block),E r/(1+dyadicScale r)^decay := by
  obtain ⟨C,hC,hcon⟩:=restricted_second_ratio_from_normalized (α:=α) W decay degree windowDegree hc hs
  refine ⟨C,hC,?_⟩
  intro Label _ slots s R seed hseed hz₁ hz₂ χ Q m K Tsec Z ξ hK weight
  dsimp only
  intro E H hE hH hnorm
  rw [actual_joint_ordinary_assembly slots s R seed hseed hz₁ hz₂ χ Q m W K Tsec Z ξ hK weight]
  exact hcon _ _ E H hE hH hnorm

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.ordinary_second_ratio
#print axioms OAI.SevenEighths.Cycle61InitialMass.restricted_second_ratio_from_normalized

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_joint_ordinary_assembly

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_restricted_second_subpower

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_joint_ordinary_from_normalized

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_ordinary_ratio_bins_subpower
