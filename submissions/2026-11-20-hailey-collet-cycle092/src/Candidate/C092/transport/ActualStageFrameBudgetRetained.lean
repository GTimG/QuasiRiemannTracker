/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal selected physical frame prices on the actual first labels supply
the corrected retained sides. All allocation/image/diagonal costs are internal. -/
import Candidate.C092.transport.ActualStageFrameBudgetPhysical
import Candidate.C092.transport.ActualStageFrameBudgetSelect
import Candidate.C092.transport.RawPairDiagonalBudgetAverageRetained
import Candidate.C092.transport.PairedRetainedBudgetOrientations
import Candidate.C092.transport.ColoredGaussFrameProviderPacking
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentCanonicalFirst
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentLogDyadic CenteredMomentCompleteCommon
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalAllocations MixedFirstLiveSource
open MixedInnerExceptionalBlock MixedPrincipalWindow MixedFirstExceptionalWindow MixedFirstProfileEnvelope
open RepairedSourceSideSupply
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentActiveSource CenteredMomentFirstMixedAllowance
open MixedFirstPhysicalApplication MixedFirstRetainedFixed MixedFirstPhysicalBudget
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstSectorTransform
open QRH.SilDensitySplit.CubeFree.Second.Concrete QRH.SilDensitySplit.CubeFree.Second.Provider
open QRH.SilDensitySplit.CubeFree.Second.ProviderGeometry
open QRH.Cycle092.PairedRetainedBudget QRH.Cycle092.ColoredSelectionAverage QRH.Cycle092.TwistedRawBall
open QRH.Cycle092.FixedFramePacking QRH.Cycle092.ColoredGaussFrameProvider QRH.Cycle092.RawPairDiagonalBudget
open QRH.Cycle090 QRH.SourceCertificate ActualEisensteinCubic
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
local instance (priority := 2000) retainedSubtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
variable {ι:Type}[Fintype ι]

def FirstSelection (s:Source ι (1/4) (9/4))(G:Id)(w:ι→ℝ)(mesh cap:ℝ)
    (Js:∀B:actualAllocations (tuplePools s) G,Finset (liveIndices B.val)) : Prop :=
  ∀B,(∑j∈Js B,w j.val) ≤ (QRH.SourceCertificate.u:ℝ) ∧ (∑j∈Js B,w j.val) ≤ 3/5000 ∧
    (∑j:Rest (Js B),w j.val.val) ≤ cap-(QRH.SourceCertificate.u:ℝ) ∧
    ((Js B=Finset.univ ∧ Fintype.card (Rest (Js B))=0) ∨
      (QRH.SourceCertificate.u:ℝ)-mesh ≤ ∑j∈Js B,w j.val)

/-- Only genuine positive physical selected terms occur in this premise;
it contains no averaged side, retained budget or whole-ball energy. -/
def SelectedFramePrices (s:Source ι (1/4) (9/4))(cover:OriginalEnclosure s)(w:ι→ℝ)
    (G:Id)(τ η₁ η₂:Character)(χ₀:RayCharacter)(Q:Id)(m:O)
    (Js:∀B:actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (t Kr Z ξ A Cfee δ NV:ℝ)(J:ℕ) : Prop :=
  ∀part:Bool,∀B,allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B≠0 → ∀ζ,
    selectedPartTerm part s cover G B (Js B) η₁ η₂ τ χ₀ Q m t Kr Z ξ ζ ≤
      (Cfee*A*Z^δ*sourceVolume (renorm (restOf s (by norm_num) cover G B (Js B)))^2*
        Z^(∑j∈Js B,w j.val)*NV)*(1+‖t‖)^(2*J)

/-- The two actual first orientations use their own packed generator.
The whole-slot selections are independent of all later class labels. -/
def BalancedFramePrices (s:Source ι (1/4) (9/4))(cover:OriginalEnclosure s)(w:ι→ℝ)
    (η₁ η₂ η:Character)(χ₀:RayCharacter)(Q:Id)(m:O)
    (C D:Id)(hC:Supported C)(E:Finset (CommonIndex C D))
    (Kr Z ξ A Cfee δ mesh cap:ℝ)(J:ℕ) : Prop :=
  ∀χ ζ:RayCharacter,∀v:ℝ,
    (∀JL,FirstSelection s C w mesh cap JL → SelectedFramePrices s cover w C
      (fixedPair η C D hC E χ (ζ⁻¹)).left η₁ η₂ χ₀ Q m JL v Kr Z ξ A Cfee δ
      ((Ideal.span {QRH.SilDensitySplit.CubeFree.Packet.firstPacked C D hC E}).absNorm:ℝ) J) ∧
    (∀JR,FirstSelection s D w mesh cap JR → SelectedFramePrices s cover w D
      (fixedPair η C D hC E χ (ζ⁻¹)).right η₁ η₂ χ₀ Q m JR v Kr Z ξ A Cfee δ
      ((Ideal.span {QRH.SilDensitySplit.CubeFree.Packet.firstPackedRight C D hC E}).absNorm:ℝ) J)

/-- Literal first-label physical prices at the same native retained dyad. -/
def FrameRetainedPrices (s:Source ι (1/4) (9/4))(cover:OriginalEnclosure s)(w:ι→ℝ)
    (η₁ η₂ η:Character)(χ₀:RayCharacter)(Q:Id)(m:O)
    (Kroot Z κ H ξsecond A Cfee δ mesh cap:ℝ)(J:ℕ) : Prop :=
  ∀p:Labels s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) 1,
    ∀E∈inactiveSubsets p.val.1 p.val.2,
    ∀b:Blocks (effectiveScale p.val.1 p.val.2 E Kroot)
      (firstRadius s p.val.1 p.val.2 E Kroot Z κ) (H/p.val.1.absNorm) (H/p.val.2.absNorm),
    1/2 ≤ dyadicScale (b 1) → childScale Z κ (b 1) ≤ Z^(40:ℝ) ∧
      BalancedFramePrices s cover w η₁ η₂ η χ₀ Q m p.val.1 p.val.2
        (commonLabels_supported _ p).1 E (childScale Z κ (b 1)) Z ξsecond A Cfee δ mesh cap J

/-- The only analytic input left is a literal per-frame price on each
actual selected child. The zero/tail share and all finite costs are proved
by their checked native suppliers at the same actual retained dyad. -/
theorem retained_of_native_frames (N J degree:ℕ)(K Cfee δ loss mesh n₀ y₀ l κ:ℝ)
    (hK:1 ≤ K)(hCfee:0 ≤ Cfee)(hδ:0<δ)(hgap:3*δ<loss)(hloss:0 ≤ loss)
    (hmesh:0 ≤ mesh)(hy:y₀ ≤ sourceY)(hn:n₀ ≤ sourceRatio*y₀)
    (hκ:κ ≤ 1/1500)(hwidth:l+mesh ≤ sourceWidth n₀ y₀)
    (controls:Finset (ℕ×ℕ))(h00:(0,0)∈controls)(Cz Ct:ℝ)(hCz:0 ≤ Cz)(hCt:0 ≤ Ct) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(s:Source ι (1/4) (9/4)),Fintype.card ι ≤ N → (∀i,s.M i ≤ K) →
    ∀(cover:OriginalEnclosure s)(w:ι→ℝ),(∀i,0 ≤ w i) → (∀i,w i ≤ mesh) →
      (∀i,s.P i=Z^(w i)) → (∑i,w i) ≤ l →
    ∀(η₁ η₂ η:Character)(χ₀:RayCharacter)(Q:Id)(m:O)(Kroot H ξsecond height:ℝ),
      Z ≤ Kroot → 0 ≤ height →
      (∀I∈RootColoredSeed.active s (by norm_num) (idealCoeff η₁) (idealCoeff η₂),(I.absNorm:ℝ) ≤ Z^(8:ℝ)) →
      (sourceVolume s)⁻¹ ≤ Z^(2:ℝ) →
      let A:=amplitude s 0 height degree controls 1
      (∀p:Labels s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) 1,
        ∀E∈inactiveSubsets p.val.1 p.val.2,
        ∀b:Blocks (effectiveScale p.val.1 p.val.2 E Kroot)
          (firstRadius s p.val.1 p.val.2 E Kroot Z κ) (H/p.val.1.absNorm) (H/p.val.2.absNorm),
        1/2 ≤ dyadicScale (b 1) → childScale Z κ (b 1) ≤ Z^(40:ℝ) ∧
          BalancedFramePrices s cover w η₁ η₂ η χ₀ Q m p.val.1 p.val.2
            (commonLabels_supported _ p).1 E (childScale Z κ (b 1)) Z ξsecond A Cfee δ mesh
              (sourceWidth n₀ y₀) J) →
      AveragedRetainedSidesQ s cover w η₁ η₂ η χ₀ Q m Kroot Z κ κ H A loss ξsecond Cz Ct J := by
  obtain ⟨Cm,hCm,hside⟩:=eventual_sides_of_native_prices N J K Cfee δ loss hK hCfee hδ hgap
  filter_upwards [hside,uniform_retained_average_diagonal_share (ι:=ι) N K Cz Ct (1/4)
    hK hCz hCt (by norm_num)] with Z hs hd
  refine ⟨hd.1,?_⟩
  intro s hN hM cover w hw hwm hP hws η₁ η₂ η χ₀ Q m Kroot H ξsecond height hKroot hh hactive hinv
  dsimp only
  intro hprices p
  obtain ⟨JL,hJL⟩:=stage_whole_selection s p.val.1 w hy hn hw hwm hmesh hws hwidth
  obtain ⟨JR,hJR⟩:=stage_whole_selection s p.val.2 w hy hn hw hwm hmesh hws hwidth
  intro E hE b hb χ ζ v
  have hc:=(commonLabels_supported _ p)
  have hdata:=commonLabels_data _ _ p.val.1 p.val.2 p.property
  have hcpC:=commonPart_of_equal_support p.val.1 p.val.2 hc.1.1 hdata.2.2
  have hcpD:=commonPart_of_equal_support p.val.2 p.val.1 hc.2.1 hdata.2.2.symm
  have hcf:=lab_cubeFree η₁ η₂ s (by norm_num) ⟨p,E⟩
  have hpack:=actual_packed_norms η p.val.1 p.val.2 hc.1 E hcf hcpC hcpD χ ζ
  have hcaps:=QRH.SilDensitySplit.CubeFree.Second.ProviderGeometry.lab_cols_le
    (RootColoredSeed.active s (by norm_num) (idealCoeff η₁) (idealCoeff η₂)) (Z^(8:ℝ)) hactive ⟨p,E⟩
  have hprice:=(hprices p E hE b hb)
  have hp:=(hprice.2 χ ζ v)
  have hA:0 ≤ amplitude s 0 height degree controls 1:=amplitude_nonneg s 0 height hh degree controls 1 (by norm_num)
  have hKr:0 ≤ childScale Z κ (b 1):=Real.rpow_nonneg (zero_lt_one.trans hd.1).le _
  have hret:Retained (frequencyRadius
      (firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) Kroot (sourceVolume s)) Z κ) (b 1):=by
    exact ((mem_retainedIndices _ _).mp (b 1).property).1
  let ML:=clippedMultiplicity s (by norm_num) cover p.val.1 JL (fun _=>Cm*Z^δ)
  let MR:=clippedMultiplicity s (by norm_num) cover p.val.2 JR (fun _=>Cm*Z^δ)
  have hML0:∀B,0 ≤ ML B:=by
    intro B;dsimp [ML,clippedMultiplicity]
    exact le_min (mul_nonneg hCm.le (Real.rpow_nonneg (zero_lt_one.trans hd.1).le _)) (Nat.cast_nonneg _)
  have hMR0:∀B,0 ≤ MR B:=by
    intro B;dsimp [MR,clippedMultiplicity]
    exact le_min (mul_nonneg hCm.le (Real.rpow_nonneg (zero_lt_one.trans hd.1).le _)) (Nat.cast_nonneg _)
  have hdiagL:=hd.2 s hN hM cover w hw hP p.val.1 p.val.2 hc.1 hc.2 hcpC hcpD hcaps.1 hcaps.2 hinv JL
    ML hML0 (clippedMultiplicity_le_card s (by norm_num) cover p.val.1 JL (fun _=>Cm*Z^δ))
    (fun B=>(hJL B).2.1) η₁ η₂ (fixedPair η _ _ hc.1 E χ (ζ⁻¹)).left η E
    (fixedPair η _ _ hc.1 E χ (ζ⁻¹)).left_modulus Kroot κ hKroot hκ (b 1) hret
    v 0 height loss hh hloss degree controls h00 1 le_rfl
  let ER:=CenteredMomentFirstMixedRightTransport.swapSubset p.val.1 p.val.2 E
  have hretR:Retained (frequencyRadius
      (firstNominalScale p.val.2 p.val.1 (∏P∈ER,P.val) Kroot (sourceVolume s)) Z κ) (b 1):=by
    dsimp [ER]
    rw [CenteredMomentFirstMixedRightTransport.swapSubset_product,
      CenteredMomentFirstMixedRightTransport.nominal_swap]
    exact hret
  have hdiagR:=hd.2 s hN hM cover w hw hP p.val.2 p.val.1 hc.2 hc.1 hcpD hcpC hcaps.2 hcaps.1 hinv JR
    MR hMR0 (clippedMultiplicity_le_card s (by norm_num) cover p.val.2 JR (fun _=>Cm*Z^δ))
    (fun B=>(hJR B).2.1) η₁ η₂ (fixedPair η _ _ hc.1 E χ (ζ⁻¹)).right η ER
    (CenteredMomentFirstMixedRightTransport.right_modulus η _ _ hc.1 E χ (ζ⁻¹)
      (fixedPair η _ _ hc.1 E χ (ζ⁻¹))) Kroot κ hKroot hκ (b 1) hretR
    v 0 height loss hh hloss degree controls h00 1 le_rfl
  have hpoly:1 ≤ (1+‖v‖)^(2*J):=one_le_pow₀ (by linarith [norm_nonneg v])
  have hz:0<Z:=zero_lt_one.trans hd.1
  have hbalance (τ:Character)(G opp:Id):0 ≤ balancedBudget s τ G opp
      (amplitude s 0 height degree controls 1) Z loss:=by
    unfold balancedBudget;positivity
  constructor
  · apply hs.2 ι s hN hM cover w hw hP p.val.1 p.val.2 hc.1.1 hcaps.1 hc.2.1 JL
      (fun B=>(hJL B).2.1) η₁ η₂ (fixedPair η _ _ hc.1 E χ (ζ⁻¹)).left χ₀ Q m v
      (childScale Z κ (b 1)) ξsecond _ _ Cz Ct hKr hprice.1 hA (by positivity) hpack.1
      (hp.1 JL hJL)
    apply div_le_div_of_nonneg_right _ (sourceVolume_pos s).le
    change averagedDiagonalCost s cover p.val.1 JL ML η₁ η₂ _ v _ Z Cz Ct ≤ _
    have hhdiag:averagedDiagonalCost s cover p.val.1 JL ML η₁ η₂ _ v _ Z Cz Ct ≤
        (1/4)*balancedBudget s (fixedPair η _ _ hc.1 E χ (ζ⁻¹)).left p.val.1 p.val.2
          (amplitude s 0 height degree controls 1) Z loss:=hdiagL
    apply hhdiag.trans
    convert le_mul_of_one_le_right (mul_nonneg (by norm_num : (0:ℝ) ≤ 1/4) (hbalance _ _ _)) hpoly using 1 <;> ring
  · apply hs.2 ι s hN hM cover w hw hP p.val.2 p.val.1 hc.2.1 hcaps.2 hc.1.1 JR
      (fun B=>(hJR B).2.1) η₁ η₂ (fixedPair η _ _ hc.1 E χ (ζ⁻¹)).right χ₀ Q m v
      (childScale Z κ (b 1)) ξsecond _ _ Cz Ct hKr hprice.1 hA (by positivity) hpack.2
      (hp.2 JR hJR)
    apply div_le_div_of_nonneg_right _ (sourceVolume_pos s).le
    change averagedDiagonalCost s cover p.val.2 JR MR η₁ η₂ _ v _ Z Cz Ct ≤ _
    have hhdiag:averagedDiagonalCost s cover p.val.2 JR MR η₁ η₂ _ v _ Z Cz Ct ≤
        (1/4)*balancedBudget s (fixedPair η _ _ hc.1 E χ (ζ⁻¹)).right p.val.2 p.val.1
          (amplitude s 0 height degree controls 1) Z loss:=hdiagR
    apply hhdiag.trans
    convert le_mul_of_one_le_right (mul_nonneg (by norm_num : (0:ℝ) ≤ 1/4) (hbalance _ _ _)) hpoly using 1 <;> ring

#print axioms retained_of_native_frames
end
end QRH.Cycle092.ActualStageFrameBudget
