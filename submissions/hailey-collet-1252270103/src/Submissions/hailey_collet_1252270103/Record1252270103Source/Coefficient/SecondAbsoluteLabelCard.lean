/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Absolute counting of the actual second block labels. Common ideals, all
inactive subsets and the full four-coordinate dyad box are counted explicitly. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.SecondSectorDatumFamily
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.ModifiedFibersDyads
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.SecondAbsoluteEnvelope
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentOriginalCommonHarmonic CenteredMomentCanonicalFirst
open CenteredMomentCompleteCommon CenteredMomentSecondBlockAggregate
open CenteredMomentSecondLiveBlock Record1252270103Second Cycle61InitialMass
open CenteredMomentSectorLocalization
open QRH.Record1252270103Source.High
local notation "O" => HeckeFamily.O
local instance absoluteLabelSumDecidable {ι : Type*} :
    DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem common_subset_card_bound :
    ∃C:ℝ,0<C ∧ ∀I J:Ideal O,I≠0 →
      (Fintype.card (Finset (CommonIndex I J)):ℝ)≤C*(I.absNorm:ℝ) := by
  obtain ⟨C,hC,h⟩:=SquarefreeDivisorBound.prime_support_subsets_bound 1 (by norm_num)
  refine ⟨C,hC,?_⟩
  intro I J hI
  have hc : Fintype.card (CommonIndex I J)≤(primeSupport I).card := by
    simpa only [CommonIndex,Fintype.card_coe] using
      Finset.card_le_card (show commonSupport I J⊆primeSupport I from Finset.inter_subset_left)
  have hpow : (2:ℝ)^Fintype.card (CommonIndex I J)≤(2:ℝ)^(primeSupport I).card :=
    pow_le_pow_right₀ (by norm_num) hc
  simpa only [Fintype.card_finset,Nat.cast_pow,Nat.cast_ofNat,Real.rpow_one] using
    hpow.trans (h I hI)

theorem live_label_card {ι:Type*} [Fintype ι]
    (s:Input ι) (modifier:Tuple ι→ℂ) (R seed:Ideal O)
    (hseed:Squarefree seed) (hz₁:s.W₁ 0=0) (hz₂:s.W₂ 0=0)
    (Y:ℝ) (hY:0≤Y) (hsource:sourceRadius s≤Y) :
    (Fintype.card (liveLabels s.η (finiteColumns (Fintype.piFinset s.pools))
      (CoupledFirst.coefficient s modifier R seed)):ℝ)≤(128*Y)^2 := by
  let L:=liveLabels s.η (finiteColumns (Fintype.piFinset s.pools))
    (CoupledFirst.coefficient s modifier R seed)
  have hg (p:L) := CoupledFirst.actual_common_gates s modifier R seed hseed hz₁ hz₂
    p.val.val.1 p.val.val.2 p.val.property
  let f:L→(idealBall Y)×(idealBall Y):=fun p=>
    (⟨p.val.val.1,(mem_idealBall _ _).mpr ⟨(hg p).1,(hg p).2.2.2.2.2.1.trans hsource⟩⟩,
     ⟨p.val.val.2,(mem_idealBall _ _).mpr ⟨(hg p).2.1,(hg p).2.2.2.2.2.2.trans hsource⟩⟩)
  have hf:Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (congrArg (fun x=>x.1.val) hpq) (congrArg (fun x=>x.2.val) hpq)
  have hc:(Fintype.card L:ℝ)≤((idealBall Y).card:ℝ)^2 := by
    exact_mod_cast (show Fintype.card L≤(idealBall Y).card^2 by
      simpa only [Fintype.card_prod,Fintype.card_coe,pow_two] using Fintype.card_le_of_injective f hf)
  exact hc.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (idealBall_card Y hY) 2)

/-- The dyad-box membership is an actual finite support condition, not a
bound on a physical norm. The complete-block filter only decreases this count. -/
theorem block_card_in_box {ι:Type*} [Fintype ι] [DecidableEq ι]
    (s:Input ι) (modifier:Tuple ι→ℂ) (R seed:Ideal O)
    (hseed:Squarefree seed) (hz₁:s.W₁ 0=0) (hz₂:s.W₂ 0=0)
    (H Tsec Z ξ Y C:ℝ) (hY:0≤Y) (hC:0≤C) (hsource:sourceRadius s≤Y)
    (hsub:∀I J:Ideal O,I≠0 →
      (Fintype.card (Finset (CommonIndex I J)):ℝ)≤C*(I.absNorm:ℝ))
    (box:Finset (Fin 4→ℤ))
    (hbox:∀q:BlockIndex s modifier R seed H Tsec Z ξ,(fun i=>(q.2.2 i:ℤ))∈box) :
    (Fintype.card (BlockIndex s modifier R seed H Tsec Z ξ):ℝ)≤
      (128*Y)^2*(C*Y)*box.card := by
  let L:=liveLabels s.η (finiteColumns (Fintype.piFinset s.pools))
    (CoupledFirst.coefficient s modifier R seed)
  have hdyad (p:L) (U:Finset (CommonIndex p.val.val.1 p.val.val.2)) :
      (Fintype.card (SourceBlocks p.val.val.1 p.val.val.2 U H
        (frequencyRadius Tsec Z ξ) (sourceRadius s)):ℝ)≤box.card := by
    let f:SourceBlocks p.val.val.1 p.val.val.2 U H
        (frequencyRadius Tsec Z ξ) (sourceRadius s)→box :=
      fun n=>⟨fun i=>(n i:ℤ),hbox ⟨p,U,n⟩⟩
    have hf:Function.Injective f := by
      intro n m he
      funext i
      apply Subtype.ext
      exact congrFun (congrArg Subtype.val he) i
    exact_mod_cast (show Fintype.card _≤box.card by
      simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf)
  have hsub' (p:L) :
      (Fintype.card (Finset (CommonIndex p.val.val.1 p.val.val.2)):ℝ)≤C*Y := by
    have hg:=CoupledFirst.actual_common_gates s modifier R seed hseed hz₁ hz₂
      p.val.val.1 p.val.val.2 p.val.property
    exact (hsub _ _ hg.1).trans
      (mul_le_mul_of_nonneg_left (hg.2.2.2.2.2.1.trans hsource) hC)
  change (Fintype.card (Σp:L,ΣU:Finset (CommonIndex p.val.val.1 p.val.val.2),
    SourceBlocks p.val.val.1 p.val.val.2 U H (frequencyRadius Tsec Z ξ) (sourceRadius s)):ℝ)≤_
  simp only [Fintype.card_sigma,Nat.cast_sum]
  calc
    _≤∑p:L,(C*Y)*box.card := by
      apply Finset.sum_le_sum
      intro p _
      calc
        _≤∑_U:Finset (CommonIndex p.val.val.1 p.val.val.2),(box.card:ℝ) :=
          Finset.sum_le_sum (fun U _=>hdyad p U)
        _=(Fintype.card (Finset (CommonIndex p.val.val.1 p.val.val.2)):ℝ)*box.card := by simp
        _≤_:=mul_le_mul_of_nonneg_right (hsub' p) (Nat.cast_nonneg _)
    _=(Fintype.card L:ℝ)*((C*Y)*box.card) := by simp
    _≤(128*Y)^2*((C*Y)*box.card) :=
      mul_le_mul_of_nonneg_right (live_label_card s modifier R seed hseed hz₁ hz₂ Y hY hsource)
        (by positivity)
    _=_ := by ring

end
end QRH.Record1252270103Source.SecondAbsoluteEnvelope
#print axioms QRH.Record1252270103Source.SecondAbsoluteEnvelope.common_subset_card_bound
#print axioms QRH.Record1252270103Source.SecondAbsoluteEnvelope.live_label_card
#print axioms QRH.Record1252270103Source.SecondAbsoluteEnvelope.block_card_in_box
