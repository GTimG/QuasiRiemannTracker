/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual selected physical classes, original volume and native packing are
priced with a genuine selected-image multiplicity and one uniform horizon. -/
import Candidate.C092.transport.ActualStageFrameBudgetHorizon
import Candidate.C092.transport.PairedRetainedBudgetLambda
import Candidate.C092.transport.PairedRetainedBudgetShares
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentFirstMixedAllowance
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalAllocations MixedFirstLiveSource MixedOriginalTail MixedInnerExceptionalBlock MixedPrincipalWindow
open QRH.SilDensitySplit.CubeFree.Second.Concrete QRH.SilDensitySplit.CubeFree.Second.Provider
open QRH.Cycle092.PairedRetainedBudget QRH.Cycle092.ColoredSelectionAverage QRH.Cycle092.TwistedRawBall
local notation "Id"=>Ideal HeckeFamily.O
local instance (priority := 2000) classSubtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

/-- This is a literal physical class estimate, not an estimate of the retained
ball or either averaged side. Numerical class prices and original packing
are enough; the divisor-image multiplicity and allocation costs are internal. -/
theorem eventual_part_of_class_frames (N J:ℕ)(K Cfee δ loss share:ℝ)
    (hK:1 ≤ K)(hCfee:0 ≤ Cfee)(hδ:0<δ)(hgap:3*δ<loss)(hshare:0<share) :
    ∃Cm:ℝ,0<Cm ∧ ∀ᶠZ:ℝ in atTop,3 ≤ Z ∧
    ∀(ι:Type)[Fintype ι](s:Source ι (1/4) (9/4)),Fintype.card ι ≤ N → (∀i,s.M i ≤ K) →
    ∀(cover:OriginalEnclosure s)(w:ι→ℝ),(∀i,0 ≤ w i) → (∀i,s.P i=Z^(w i)) →
    ∀(G opp:Id),G≠0 → (G.absNorm:ℝ) ≤ Z^(8:ℝ) → opp≠0 →
    ∀Js:∀B:actualAllocations (tuplePools s) G,Finset (liveIndices B.val),
      (∀B,(∑j∈Js B,w j.val) ≤ 3/5000) →
    ∀(η₁ η₂ τ:Character)(χ₀:RayCharacter)(Q:Id)(m:HeckeFamily.O)(t Kr ξ A NV:ℝ),
      0 ≤ Kr → Kr ≤ Z^(40:ℝ) → 0 ≤ A → 0 ≤ NV →
      NV*(opp.absNorm:ℝ) ≤ (τ.modulus.absNorm:ℝ)*(G.absNorm:ℝ) →
    ∀part:Bool,∀boxes Cg Mm Cb B₀:actualAllocations (tuplePools s) G→ℝ,∀a:ℝ,
      (∀B,0 ≤ boxes B ∧ 0 ≤ Cg B ∧ 0 ≤ Mm B ∧ 0 ≤ Cb B) →
      (∀B,B₀ B ≤ Cb B*sourceVolume (renorm (restOf s (by norm_num) cover G B (Js B)))*
        NV*(∏j:Js B,(allocatedLiveSource s (by norm_num) cover G B).P j.val)) →
      (∀B,classLambda (boxes B) (Cg B) (Mm B) (Cb B) a J ≤ Cfee*A*Z^δ) →
      (∀B ζ,selectedPartTerm part s cover G B (Js B) η₁ η₂ τ χ₀ Q m t Kr Z ξ ζ ≤
        boxes B*Cg B*((sourceVolume (renorm (restOf s (by norm_num) cover G B (Js B)))/a^2)*
          Mm B*B₀ B)*(CenteredMomentSecondWindowBudget.heightEnvelope t^J*
            CenteredMomentSecondWindowBudget.profileMoment J)^2) →
      let M:=clippedMultiplicity s (by norm_num) cover G Js (fun _=>Cm*Z^δ)
      MultBound s (by norm_num) cover G Js Kr
        (fun B=>RawSides.selectionScaleQ s (by norm_num) cover G B (Js B)) M ∧
      averagedPartSideCost part s cover G Js M η₁ η₂ τ χ₀ Q m t Kr Z ξ ≤
        share*balancedBudget s τ G opp A Z loss*(1+‖t‖)^(2*J) := by
  obtain ⟨Cm,hCm,hmult⟩:=actual_multBound_subpower N δ hδ
  refine ⟨Cm,hCm,?_⟩
  filter_upwards [hmult,eventual_label_payment N K Cm Cfee δ loss share hK hCm.le hCfee hδ hgap hshare]
    with Z hm hp
  refine ⟨hm.1,?_⟩
  intro ι inst s hN hMs cover w hw hP G opp hG hGcap hopp Js hJs η₁ η₂ τ χ₀ Q m t Kr ξ A NV
    hKr hKrcap hA hNV hpack part boxes Cg Mm Cb B₀ a hnonneg hB₀ hfee hphysical
  have hz:0<Z:=lt_of_lt_of_le (by norm_num : (0:ℝ)<3) hm.1
  let M:=clippedMultiplicity s (by norm_num) cover G Js (fun _=>Cm*Z^δ)
  let Kl:=Cfee*A*Z^δ
  let Λ:=fun B:actualAllocations (tuplePools s) G=>classLambda (boxes B) (Cg B) (Mm B) (Cb B) a J*
    sourceVolume (renorm (restOf s (by norm_num) cover G B (Js B)))^2*
      (∏j:Js B,(allocatedLiveSource s (by norm_num) cover G B).P j.val)*NV
  have hm':=hm.2 ι s hN cover w hw hP G Js hJs Kr hKr hKrcap
  refine ⟨hm',?_⟩
  apply averagedPartSideCost_le_balanced part s cover G opp Js η₁ η₂ τ χ₀ Q m t Kr Z ξ A loss share
    M Λ N J (Cm*Z^δ) Kl NV
  · intro B
    exact (Fintype.card_le_of_injective (fun j:Js B=>j.val.val) (by
      intro x y h;exact Subtype.ext (Subtype.ext h))).trans hN
  · intro B
    exact ⟨(hm' B).1,clippedMultiplicity_le s (by norm_num) cover G Js (fun _=>Cm*Z^δ) B⟩
  · dsimp [Kl];positivity
  · intro B
    dsimp [Λ]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hfee B) (sq_nonneg _))
        (Finset.prod_nonneg (fun j _=>zero_le_one.trans ((allocatedLiveSource s (by norm_num) cover G B).hP j.val)))) hNV
  · intro B
    have hb:=hnonneg B
    have hc:=classLambda_nonneg (boxes B) (Cg B) (Mm B) (Cb B) a J hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
    dsimp [Λ]
    exact mul_nonneg (mul_nonneg (mul_nonneg hc (sq_nonneg _))
      (Finset.prod_nonneg (fun j _=>zero_le_one.trans ((allocatedLiveSource s (by norm_num) cover G B).hP j.val)))) hNV
  · exact hNV
  · exact hopp
  · exact hpack
  · exact hG
  · intro B ζ
    have hb:=hnonneg B
    exact lambda_of_class_bound _ _ _ _ _ _ _ _ _ _ _ J hb.1 hb.2.1
      (sourceVolume_pos _).le hb.2.2.1 hb.2.2.2 hNV
      (Finset.prod_nonneg (fun j _=>zero_le_one.trans ((allocatedLiveSource s (by norm_num) cover G B).hP j.val)))
      (hB₀ B) (hphysical B ζ)
  · exact hp.2 ι s hN hMs G opp hG hGcap A (Cm*Z^δ) Kl hA (by positivity)
      (by dsimp [Kl];positivity) le_rfl le_rfl

#print axioms eventual_part_of_class_frames
end
end QRH.Cycle092.ActualStageFrameBudget
