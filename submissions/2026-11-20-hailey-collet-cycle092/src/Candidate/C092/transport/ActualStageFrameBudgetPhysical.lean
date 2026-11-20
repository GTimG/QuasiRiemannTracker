/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Native per-selection physical prices supply the corrected side, with
actual packing and genuine finite allocation/image costs paid internally. -/
import Candidate.C092.transport.ActualStageFrameBudgetClass
import Candidate.C092.transport.ActualStageFrameBudgetPositive
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentFirstMixedAllowance
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalAllocations MixedFirstLiveSource
open MixedInnerExceptionalBlock MixedPrincipalWindow
open QRH.SilDensitySplit.CubeFree.Second.Concrete QRH.SilDensitySplit.CubeFree.Second.Provider
open QRH.Cycle092.PairedRetainedBudget QRH.Cycle092.ColoredSelectionAverage QRH.Cycle092.TwistedRawBall
local notation "Id"=>Ideal HeckeFamily.O
local instance (priority := 2000) physicalSubtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

/-- The selected product in fixed_part is the SAME actual selected width
and occurs exactly once in the native H.25 cancellation. -/
theorem selected_product_exact {ι:Type}[Fintype ι](s:Source ι (1/4) (9/4))
    (cover:OriginalEnclosure s)(G:Id)(B:actualAllocations (tuplePools s) G)
    (J:Finset (liveIndices B.val))(Z:ℝ)(hZ:0<Z)(w:ι→ℝ)(hP:∀i,s.P i=Z^(w i)) :
    (∏j:J,(allocatedLiveSource s (by norm_num) cover G B).P j.val)=Z^(∑j∈J,w j.val) := by
  change (∏j:J,s.P j.val.val)=_
  simp_rw [hP]
  rw [←Finset.sum_coe_sort,Real.rpow_sum_of_pos hZ]

/-- J and the source fee are fixed before all positive diagonal constants.
The analytic premises are only the literal fixed and regular selected
physical sums. No retained side or full-ball budget is assumed. -/
theorem eventual_sides_of_native_prices (N J:ℕ)(K Cfee δ loss:ℝ)
    (hK:1 ≤ K)(hCfee:0 ≤ Cfee)(hδ:0<δ)(hgap:3*δ<loss) :
    ∃Cm:ℝ,0<Cm ∧ ∀ᶠZ:ℝ in atTop,3 ≤ Z ∧
    ∀(ι:Type)[Fintype ι](s:Source ι (1/4) (9/4)),Fintype.card ι ≤ N → (∀i,s.M i ≤ K) →
    ∀(cover:OriginalEnclosure s)(w:ι→ℝ),(∀i,0 ≤ w i) → (∀i,s.P i=Z^(w i)) →
    ∀(G opp:Id),G≠0 → (G.absNorm:ℝ) ≤ Z^(8:ℝ) → opp≠0 →
    ∀Js:∀B:actualAllocations (tuplePools s) G,Finset (liveIndices B.val),
      (∀B,(∑j∈Js B,w j.val) ≤ 3/5000) →
    ∀(η₁ η₂ τ:Character)(χ₀:RayCharacter)(Q:Id)(m:HeckeFamily.O)(t Kr ξ A NV Cz Ct:ℝ),
      0 ≤ Kr → Kr ≤ Z^(40:ℝ) → 0 ≤ A → 0 ≤ NV →
      NV*(opp.absNorm:ℝ) ≤ (τ.modulus.absNorm:ℝ)*(G.absNorm:ℝ) →
      (∀part:Bool,∀B,allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B≠0 → ∀ζ,selectedPartTerm part s cover G B (Js B) η₁ η₂ τ χ₀ Q m t Kr Z ξ ζ ≤
        (Cfee*A*Z^δ*sourceVolume (renorm (restOf s (by norm_num) cover G B (Js B)))^2*
          Z^(∑j∈Js B,w j.val)*NV)*(1+‖t‖)^(2*J)) →
      let M:=clippedMultiplicity s (by norm_num) cover G Js (fun _=>Cm*Z^δ)
      (averagedDiagonalCost s cover G Js M η₁ η₂ τ t Kr Z Cz Ct/sourceVolume s ≤
        (1/4)*(balancedBudget s τ G opp A Z loss*(1+‖t‖)^(2*J))/sourceVolume s) →
      AveragedSecondSidePrice s cover w G η₁ η₂ τ χ₀ Q m t Kr Z ξ Cz Ct
        (balancedBudget s τ G opp A Z loss*(1+‖t‖)^(2*J)) := by
  obtain ⟨Cm,hCm,hmult⟩:=actual_multBound_subpower N δ hδ
  refine ⟨Cm,hCm,?_⟩
  filter_upwards [hmult,eventual_label_payment N K Cm Cfee δ loss (3/8) hK hCm.le hCfee hδ hgap (by norm_num)]
    with Z hm hp
  refine ⟨hm.1,?_⟩
  intro ι inst s hN hMs cover w hw hP G opp hG hGcap hopp Js hJs η₁ η₂ τ χ₀ Q m t Kr ξ A NV Cz Ct
    hKr hKrcap hA hNV hpack hphysical
  have hz:0<Z:=lt_of_lt_of_le (by norm_num : (0:ℝ)<3) hm.1
  let M:=clippedMultiplicity s (by norm_num) cover G Js (fun _=>Cm*Z^δ)
  dsimp only
  intro hdiag
  have hm':=hm.2 ι s hN cover w hw hP G Js hJs Kr hKr hKrcap
  have hparts (part:Bool):averagedPartSideCost part s cover G Js M η₁ η₂ τ χ₀ Q m t Kr Z ξ ≤
      (3/8)*balancedBudget s τ G opp A Z loss*(1+‖t‖)^(2*J):=by
    let Kl:=Cfee*A*Z^δ
    let Λ:=fun B:actualAllocations (tuplePools s) G=>Kl*
      sourceVolume (renorm (restOf s (by norm_num) cover G B (Js B)))^2*
        (∏j:Js B,(allocatedLiveSource s (by norm_num) cover G B).P j.val)*NV
    have hprod (B:actualAllocations (tuplePools s) G):0 ≤ ∏j:Js B,
        (allocatedLiveSource s (by norm_num) cover G B).P j.val:=
      Finset.prod_nonneg (fun j _=>zero_le_one.trans ((allocatedLiveSource s (by norm_num) cover G B).hP j.val))
    have hKl:0 ≤ Kl:=by dsimp [Kl];positivity
    apply positive_part_le_balanced part s cover G opp Js η₁ η₂ τ χ₀ Q m t Kr Z ξ A loss (3/8)
      M Λ N J (Cm*Z^δ) Kl NV
    · intro B
      exact (Fintype.card_le_of_injective (fun j:Js B=>j.val.val) (by
        intro x y h;exact Subtype.ext (Subtype.ext h))).trans hN
    · intro B
      exact ⟨(hm' B).1,clippedMultiplicity_le s (by norm_num) cover G Js (fun _=>Cm*Z^δ) B⟩
    · exact hKl
    · intro B;exact le_rfl
    · intro B
      exact mul_nonneg (mul_nonneg (mul_nonneg hKl (sq_nonneg _)) (hprod B)) hNV
    · exact hNV
    · exact hopp
    · exact hpack
    · exact hG
    · intro B hB ζ
      have hh:=hphysical part B hB ζ
      rw [←selected_product_exact s cover G B (Js B) Z hz w hP] at hh
      exact hh
    · exact hp.2 ι s hN hMs G opp hG hGcap A (Cm*Z^δ) Kl hA (by positivity) hKl le_rfl le_rfl
  apply averagedSecondSidePrice_of_normalized_shares s cover w G Js M η₁ η₂ τ χ₀ Q m t Kr Z ξ Cz Ct
    (balancedBudget s τ G opp A Z loss*(1+‖t‖)^(2*J)) hJs hm'
    (clippedMultiplicity_le_card s (by norm_num) cover G Js (fun _=>Cm*Z^δ)) hdiag
  · exact div_le_div_of_nonneg_right (by convert hparts true using 1 <;> ring) (sourceVolume_pos s).le
  · exact div_le_div_of_nonneg_right (by convert hparts false using 1 <;> ring) (sourceVolume_pos s).le

#print axioms selected_product_exact
#print axioms eventual_sides_of_native_prices
end
end QRH.Cycle092.ActualStageFrameBudget
