import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.DepthTwoHighUniversal
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainHighPayment
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The puncture and the coordinate box of the HIGH rows of all nonzero second-stage blocks of a parent of the second
step. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Cycle63MarkedPlain
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open MeasureTheory
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentNaturalFixedRaySource
open CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT Cycle63Moment
open CenteredMomentAmplificationChildInput
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
open CenteredMomentOriginalCommonHarmonic
open ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSecondHeightFamily Cycle63Moment.LowBranch
attribute [local instance] geometryAffineHighPaymentSumDecidable

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

variable [Cycle63.AffineLedger] in
include H hH in
/-- At a parent whose source gates hold, every nonzero second-stage block has a nonzero puncture of norm at most
`Z^28`, and the compensated HIGH coordinates of every live row lie in the box of half-width `148 + μ/8`. -/
theorem affine_high_universal_box {ι : Type} [Fintype ι] [DecidableEq ι]
    (η₀ : Character) (Q : Ideal O) (hQM : Q≤M) (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (μ e τ bΦ : ℝ) (hμ : 0<μ) (hμ1 : μ≤1) (he : 0<e) (hτ : 0<τ) (hbΦ : 2≤bΦ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(hZ : 1<Z)(s : Input ι)(R seed : Ideal O)(Mrow amp : ℝ),
      Endpoints (9/4) (9/4) (9/4) s → Squarefree seed → R≠0 → (R.absNorm:ℝ)≤Z^(20:ℝ) →
      ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
      sourceRadius s≤Z^(3:ℝ) → CenteredMomentAmplificationChildInput.volume s≤Z^(3:ℝ) → 0≤amp → |Mrow|≤4 →
      |Real.logb Z (CenteredMomentAmplificationChildInput.volume s)|≤4 → |amp|≤4 → |frequencyLoss Z 32 (μ/64)+μ/8|≤4 →
      ∀(reflected second : Bool)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)(χ₀ : RayCharacter),
      (∀j,(affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
        (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
          else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)≠0) ∧
      (∀j,((((affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
        (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
          else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)).absNorm:ℝ))≤Z^(28:ℝ)) ∧
      ∀r : AffineHighRows reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask,
        ∀i,-(148+μ/8)≤affineHighUniversalCoordinates second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
            (internalQ Q η₀) fixedBadMask r i ∧
          affineHighUniversalCoordinates second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
            (internalQ Q η₀) fixedBadMask r i≤148+μ/8 := by
  filter_upwards [eventually_actual_main_high_literal_admission (α:=ι) M H hH (9/4) (9/4) (μ/8) (μ/64) (1/4) τ e 28
    bΦ 20 (by norm_num) (by norm_num) (by positivity) (by linarith) (by positivity) (by norm_num) hτ he
    (by norm_num) hbΦ η₀] with Z hlit
  refine ⟨hlit.1,?_⟩
  intro hZ s R seed Mrow amp hend hseed hR hRcap hz₁ hz₂ hsource hvol hamp0 hMrow hA hamp homega reflected second
    bin t χ₀
  have hj (j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) t (Fintype.card ι) hZ bin
      hz₁ hz₂) :=
    hlit.2 hZ reflected second s R seed Mrow amp (μ/8) t hend hseed hR hRcap hz₁ hz₂ hsource hvol hamp0
      (by positivity) hMrow hA hamp homega bin χ₀ (internalQ Q η₀) hQ72 fixedBadMask fixedBadMask_ne_zero
      (dvd_mul_right _ _) (dvd_mul_left _ _) (inf_le_left.trans hQM) inf_le_right hβlo hβhi j
  have hε4 : |μ/8|≤4 := by rw [abs_of_pos (by positivity)]; linarith
  have hpun (j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) t (Fintype.card ι) hZ
      bin hz₁ hz₂) :
      (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
        (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
          else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)≠0 ∧
      ((((affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
        (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
          else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)).absNorm:ℝ))≤Z^(28:ℝ) := by
    obtain ⟨-,-,-,-,hrest⟩ := hj j
    obtain ⟨-,hP,hPN,-⟩ := hrest (μ/8) (μ/8) 0 hε4 (by norm_num)
    exact ⟨hP,hPN⟩
  refine ⟨fun j => (hpun j).1,fun j => (hpun j).2,?_⟩
  intro r i
  have hK : 0<Z^Mrow := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
  obtain ⟨h1,h2,h3,h4,-⟩ := hj r.val.1
  have hchild := (actual_geometry_high_coordinate_gates s R seed (Z^Mrow) Z (μ/64) hK bin r.val.1.val.1.1.val
    (affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask r.val.1)
    reflected (!reflected) second
    (affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask r.val.1).inactive
    Mrow (Real.logb Z (CenteredMomentExceptionalAmplitudePair.volume s.toData)) amp (μ/8) (μ/8) (μ/8) 4 hZ (by norm_num)
    ⟨h1,h2⟩ ⟨h3,h4⟩ hMrow hA hamp homega hε4).2
  have hsource4 : sourceRadius s≤Z^(4:ℝ) := hsource.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))
  have hside : |geometryHighSide reflected (Real.logb Z (CenteredMomentExceptionalAmplitudePair.volume s.toData))
      (geometryExponents s R seed (Z^Mrow) Z (μ/64) r.val.1.val.1.1.val.1.val)|≤5*4 := by
    apply geometry_high_side_box reflected _ 4 _ (by norm_num) hA
    intro j
    have hn := actual_geometry_norm_caps s R seed (Z^Mrow) Z (μ/64) 4 hseed hz₁ hz₂ hsource4
      r.val.1.val.1.1.val.1.val j
    exact ⟨Real.logb_nonneg hZ hn.1,(Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hn.1)).mpr hn.2⟩
  clear hlit hj hpun
  have hbox : ∀i,-(32*4+|μ/8|+5*4)≤affineHighUniversalCoordinates second reflected s R seed Z Mrow amp μ t hZ bin
        hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask r i ∧
      affineHighUniversalCoordinates second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
        (internalQ Q η₀) fixedBadMask r i≤32*4+|μ/8|+5*4 :=
    compensated_high_coordinate_box _ _ _ _ hchild hside
  have hb := hbox i
  rw [abs_of_pos (by positivity : 0<μ/8)] at hb
  constructor <;> linarith [hb.1,hb.2]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
