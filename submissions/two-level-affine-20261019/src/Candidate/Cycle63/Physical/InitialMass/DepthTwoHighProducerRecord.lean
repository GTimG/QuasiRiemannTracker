/- The count-form record of the HIGH part of the second step at the configuration of the largest transport. Released
under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.DepthTwoHighProducerRows
import Candidate.Cycle63.Physical.InitialMass.DepthTwoHighProducerCore

set_option autoImplicit false
set_option maxHeartbeats 1600000
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
open CenteredMomentSecondHeightFamily Cycle63Moment.LowBranch HeckeDetectorZeros
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondExceptionalFamily
attribute [local instance] geometryAffineHighPaymentSumDecidable

/-- The payment of the coordinates of a row against the reserve of the parent gives the payment of the record: with the
cone rate dropped, the density in `[0, 5/6]` and the loss that covers the frequency loss, the bin widths and the shift
of the class exponents. -/
theorem high_row_pay_arith {δ ρ A length amp ampP Mrow om μ rest loss E : ℝ}
    (hδ0 : 0≤δ) (hρ0 : 0≤ρ) (hρ : ρ≤5/6) (hom : μ/8≤om) (hA : A≤length) (hamp : amp≤ampP)
    (hloss : om+μ/4+rest≤loss+Mrow)
    (hE : E≤(1-ρ)*om+ρ*(μ/8)+μ/8-(Mrow*(1-ρ)-δ*A-amp*(5-6*ρ))) :
    E≤loss-rest+ρ*Mrow+δ*length+ampP*(5-6*ρ)-4*(μ/32) := by
  have h1 : δ*A≤δ*length := mul_le_mul_of_nonneg_left hA hδ0
  have h2 : amp*(5-6*ρ)≤ampP*(5-6*ρ) := mul_le_mul_of_nonneg_right hamp (by linarith)
  have h3 : ρ*(μ/8)≤ρ*om := mul_le_mul_of_nonneg_left hom hρ0
  nlinarith [h1,h2,h3]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

section Generic

variable {Base : Type} {base : Base → Character} {κ : Type} [Fintype κ]

/-- The count-form record of the HIGH rows of a family of labels: the labels whose buffer bin is at least `(1 + qh)/2`
are binned by their buffer bin and the exponent bins of their coordinates. The record pays the reserve of the parent
when the loss covers the frequency loss and the shift of the class exponents, it has at most the buffer bins times the
fourth power of the exponent bins of the box, and its value is the shifted binned count of the keys of the labels. -/
theorem high_record_of_facts {η₀ : Character} {Z B : ℝ} (Tz : ℝ) {left : Bool} {v₁ : O}
    {unit : FirstSourceLabel → O} {left' : Bool} {u' : O} {unit' : FirstSourceLabel → O} {e : ℝ}
    (hZ : 1<Z) (select : κ → BufferIndex e) (x : κ → Fin 4→ℝ)
    (lab : κ → NonzeroJointSourceLabel left v₁ unit) (key : κ → NonzeroJointSourceLabel left' u' unit')
    (hkey : ∀l,(lab l).val=(key l).val)
    (W : ∀l,DepthTwoHighWitness M base η₀ (nonzeroJointSourceRow (lab l)))
    (μ qh Mrow A amp shift extra : ℝ) (hμ : 0<μ) (hqh : Cycle63.Optimization.secondJunction≤qh)
    (hbox : ∀l j,-(148+μ/8)≤x l j ∧ x l j≤148+μ/8)
    (hfacts : ∀l,(1+qh)/2≤bufferValue e (select l) →
      bufferValue e (select l)≤7/8 ∧ bufferValue e (select l)≤(W l).zeroMax M H hH Tz ∧
      HighRowFacts Z B (lab l) (x l) (Real.logb Z ((Ideal.span {v₁}).absNorm:ℝ)) ∧
      highExponentValue (2*bufferValue e (select l)-1) (x l)≤
        (1-unmarkedDensity (2*bufferValue e (select l)-1))*(frequencyLoss Z 32 (μ/64)+μ/8)+
          unmarkedDensity (2*bufferValue e (select l)-1)*(μ/8)+μ/8-
          (Mrow*(1-unmarkedDensity (2*bufferValue e (select l)-1))-(2*bufferValue e (select l)-1)*A-
            amp*(5-6*unmarkedDensity (2*bufferValue e (select l)-1)))) :
    ∃Hb : SecondStepHighCount M H hH base η₀ Z B Tz left v₁ unit,
      (∀length ampP loss : ℝ,A≤length → amp≤ampP →
        (frequencyLoss Z 32 (μ/64)+μ/8)+μ/4+(extra+shift)≤loss+Mrow →
        Hb.Pays Cycle63.Optimization.secondJunction Mrow length ampP loss) ∧
      (Fintype.card Hb.Class:ℝ)≤depthTwoHighClassBound e μ ∧
      Hb.value=Z^shift*∑q : BufferIndex e,keyBinnedCount
        ((Finset.univ.filter (fun l=>(1+qh)/2≤bufferValue e (select l))).filter (fun l=>select l=q)) key x (μ/32)
        (fun k=>Z^(exponentBinUpper (μ/32) k 0+(2*bufferValue e q-1)*exponentBinUpper (μ/32) k 3+extra)) := by
  let rows := Finset.univ.filter (fun l=>(1+qh)/2≤bufferValue e (select l))
  let expo := fun (i : BufferIndex e) (b : Fin 4→ℤ) => exponentBinUpper (μ/32) b 0+
    (2*bufferValue e i-1)*exponentBinUpper (μ/32) b 3+(extra+shift)
  have hw : 0<μ/32 := by positivity
  have hthr : ∀l ∈ rows,(1+qh)/2≤bufferValue e (select l) := fun l hl => (Finset.mem_filter.mp hl).2
  let Rec := secondStepBinRecord rows select x (μ/32) lab W expo (fun i => bufferValue e i)
    (Real.logb Z ((Ideal.span {v₁}).absNorm:ℝ)) hZ.le hw (fun l hl => (hfacts l (hthr l hl)).2.1)
    (fun l hl => (hfacts l (hthr l hl)).2.2.1.row) (fun l hl => (hfacts l (hthr l hl)).2.2.1.supp)
    (fun l hl => (hfacts l (hthr l hl)).2.2.1.same) (fun l hl => (hfacts l (hthr l hl)).2.2.1.cap)
    (fun l hl => (hfacts l (hthr l hl)).2.2.1.ideal) (fun l hl => (hfacts l (hthr l hl)).2.2.1.miss)
  refine ⟨Rec,?_,?_,?_⟩
  · intro length ampP loss hlen hamp' hloss
    refine secondStepBinRecord_pays rows select x (μ/32) lab W expo (fun i => bufferValue e i)
      (Real.logb Z ((Ideal.span {v₁}).absNorm:ℝ)) hZ.le hw (fun l hl => (hfacts l (hthr l hl)).2.1)
      (fun l hl => (hfacts l (hthr l hl)).2.2.1.row) (fun l hl => (hfacts l (hthr l hl)).2.2.1.supp)
      (fun l hl => (hfacts l (hthr l hl)).2.2.1.same) (fun l hl => (hfacts l (hthr l hl)).2.2.1.cap)
      (fun l hl => (hfacts l (hthr l hl)).2.2.1.ideal) (fun l hl => (hfacts l (hthr l hl)).2.2.1.miss)
      Cycle63.Optimization.secondJunction Mrow length ampP loss (extra+shift) (fun i b => rfl) rfl ?_ ?_
    · intro l hl
      have hth := hthr l hl
      have h78 := (hfacts l hth).1
      have hq0 := Cycle63.Arithmetic.q0_bounds
      have hj := Cycle63.Optimization.secondJunction_mem
      refine ⟨by linarith,by linarith [hq0.2,hj.1],by linarith⟩
    · intro l hl
      have hth := hthr l hl
      have h78 := (hfacts l hth).1
      have hq0 := Cycle63.Arithmetic.q0_bounds
      have hj := Cycle63.Optimization.secondJunction_mem
      have hδ' : Cycle63.Arithmetic.q0≤2*bufferValue e (select l)-1 ∧ 2*bufferValue e (select l)-1≤3/4 :=
        ⟨by linarith [hq0.2,hj.1],by linarith⟩
      obtain ⟨hρlo,hρhi,-⟩ := Cycle63.Physical.high_density_bounds hδ'
      have hρ0 : 0≤unmarkedDensity (2*bufferValue e (select l)-1) := by linarith
      have hρ1 : unmarkedDensity (2*bufferValue e (select l)-1)≤5/6 := by
        have := Cycle63.Arithmetic.rho0_bounds.2
        linarith
      have hfreq := frequencyLoss_nonneg Z 32 (μ/64) hZ (by norm_num) (by positivity)
      exact high_row_pay_arith (by linarith [hq0.1]) hρ0 hρ1 (by linarith) hlen hamp' hloss (hfacts l hth).2.2.2
  · have hcard := secondStepBinRecord_card rows select x (μ/32) lab W expo (fun i => bufferValue e i)
      (Real.logb Z ((Ideal.span {v₁}).absNorm:ℝ)) hZ.le hw (fun l hl => (hfacts l (hthr l hl)).2.1)
      (fun l hl => (hfacts l (hthr l hl)).2.2.1.row) (fun l hl => (hfacts l (hthr l hl)).2.2.1.supp)
      (fun l hl => (hfacts l (hthr l hl)).2.2.1.same) (fun l hl => (hfacts l (hthr l hl)).2.2.1.cap)
      (fun l hl => (hfacts l (hthr l hl)).2.2.1.ideal) (fun l hl => (hfacts l (hthr l hl)).2.2.1.miss)
      (148+μ/8) (fun l _ j => hbox l j)
    unfold depthTwoHighClassBound
    exact_mod_cast hcard
  · refine (secondStepBinRecord_value rows select x (μ/32) lab W expo (fun i => bufferValue e i)
      (Real.logb Z ((Ideal.span {v₁}).absNorm:ℝ)) hZ.le hw (fun l hl => (hfacts l (hthr l hl)).2.1)
      (fun l hl => (hfacts l (hthr l hl)).2.2.1.row) (fun l hl => (hfacts l (hthr l hl)).2.2.1.supp)
      (fun l hl => (hfacts l (hthr l hl)).2.2.1.same) (fun l hl => (hfacts l (hthr l hl)).2.2.1.cap)
      (fun l hl => (hfacts l (hthr l hl)).2.2.1.ideal) (fun l hl => (hfacts l (hthr l hl)).2.2.1.miss)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [keyBinnedCount_eq_of_val_eq (pieceLabels rows select q) lab key hkey x (μ/32) (fun b => Z^(expo q b))]
    have e2 : (fun b : Fin 4→ℤ => Z^(expo q b)) = fun b =>
        Z^((exponentBinUpper (μ/32) b 0+(2*bufferValue e q-1)*exponentBinUpper (μ/32) b 3+extra)+shift) := by
      funext b
      congr 1
      simp only [expo]
      ring
    rw [e2,keyBinnedCount_rpow_shift _ _ _ _ Z shift (zero_lt_one.trans hZ)]
    unfold pieceLabels
    congr!

end Generic

set_option linter.constructorNameAsVariable false in
variable [Cycle63.AffineLedger] in
include M H hH in
/-- At a presented parent of the second step, the HIGH rows of all nonzero second-stage blocks of the parent at one
configuration have a count-form record whose value is the transport form shifted by `shift`, with at most the buffer bins
times the fourth power of the exponent bins of the box classes, and which pays the reserve of the parent whenever the loss
covers the frequency loss and the shift of the class exponents. -/
theorem depth_two_high_config_record {ι : Type} [Fintype ι] [DecidableEq ι]
    (η₀ : Character) (Q : Ideal O) (hQM : Q≤M) (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (μ e τ bΦ qh : ℝ) (hμ : 0<μ) (hμ1 : μ≤1) (he : 0<e) (hτ : 0<τ) (hbΦ : 2≤bΦ)
    (hqh : Cycle63.Optimization.secondJunction≤qh) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(hZ : 1<Z)(hT : 2<Z^τ)(s : Input ι)(R seed : Ideal O)(Mrow amp : ℝ),
      Endpoints (9/4) (9/4) (9/4) s → Squarefree seed → R≠0 → (R.absNorm:ℝ)≤Z^(20:ℝ) →
      ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
      sourceRadius s≤Z^(3:ℝ) → CenteredMomentAmplificationChildInput.volume s≤Z^(3:ℝ) → 0≤amp → |Mrow|≤4 →
      |Real.logb Z (CenteredMomentAmplificationChildInput.volume s)|≤4 → |amp|≤4 →
      |frequencyLoss Z 32 (μ/64)+μ/8|≤4 →
      ∀(P : DepthTwoPresentation η₀ s.η R)(B Tz shift extra : ℝ),((Ideal.span {P.mult}).absNorm:ℝ)≤Z^(B-130) →
      3*Z^τ*Z^τ≤Tz → Mrow≤1 → ∀(reflected : Bool),
      ∀(second : Bool)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)(χ₀ : RayCharacter)
            (hP : ∀j,(affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
              (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
                else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)≠0)
            (hPN : ∀j,((((affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
              (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
                else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)).absNorm:ℝ))≤
                Z^(28:ℝ)),
      ∃Hb : SecondStepHighCount M H hH (fourFixedDictionary η₀) η₀ Z B Tz (!reflected) P.mult (P.unit (!reflected)),
        (∀length ampP loss : ℝ,Real.logb Z (CenteredMomentAmplificationChildInput.volume s)≤length → amp≤ampP →
          (frequencyLoss Z 32 (μ/64)+μ/8)+μ/4+(extra+shift)≤loss+Mrow →
          Hb.Pays Cycle63.Optimization.secondJunction Mrow length ampP loss) ∧
        (Fintype.card Hb.Class:ℝ)≤depthTwoHighClassBound e μ ∧
        Hb.value=Z^shift*
          affineHighUniversalTransport M H hH η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1 one_ne_zero reflected second s R
              seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) hQ72 fixedBadMask fixedBadMask_ne_zero
              (dvd_mul_right _ _) (dvd_mul_left _ _) (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hβlo hβhi hP
              hPN qh extra := by
  filter_upwards [affine_high_universal_box (ι:=ι) M H hH η₀ Q hQM hQ72 hβlo hβhi μ e τ bΦ hμ hμ1 he hτ hbΦ,
    affine_high_universal_row_package (ι:=ι) M H hH η₀ Q hQM hQ72 hβlo hβhi μ e τ bΦ qh hμ hμ1 he hτ hbΦ hqh]
    with Z hbox hrows
  refine ⟨hbox.1,?_⟩
  intro hZ hT s R seed Mrow amp hend hseed hR hRcap hz₁ hz₂ hsource hvol hamp0 hMrow hA hamp homega P B Tz shift
    extra hvcap hTz hMrow1 reflected second bin t χ₀ hP hPN
  have hbx := (hbox.2 hZ s R seed Mrow amp hend hseed hR hRcap hz₁ hz₂ hsource hvol hamp0 hMrow hA hamp homega
    reflected second bin t χ₀).2.2
  obtain ⟨W,hW⟩ := hrows.2 hZ hT s R seed Mrow amp hend hseed hR hRcap hz₁ hz₂ hsource hvol hamp0 hMrow hA hamp
    homega P B Tz hvcap hTz hMrow1 reflected second bin t χ₀ hP hPN
  obtain ⟨Hb,hpay,hcard,hval⟩ := high_record_of_facts M H hH Tz hZ
    (affineHighUniversalSelector M H hH η₀ second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
      (internalQ Q η₀) fixedBadMask hQ72 fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
      (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hβlo hβhi hP hPN)
    (affineHighUniversalCoordinates second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
      (internalQ Q η₀) fixedBadMask)
    (depthTwoRowLabel P second reflected s seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask)
    (affineHighUniversalKey η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1 one_ne_zero second reflected s R seed Z Mrow amp
      μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask)
    (fun r => (affineHighUniversalKey_val (P.τ₁ P.j₁.2) 1 P.selfRow 1 one_ne_zero second reflected s R seed Z Mrow
      amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask r).trans
      (affineHighUniversalKey_val η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1 one_ne_zero second reflected s R seed Z
        Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask r).symm)
    W μ qh Mrow (Real.logb Z (CenteredMomentAmplificationChildInput.volume s)) amp shift extra hμ hqh
    (fun l j => hbx l j) hW
  exact ⟨Hb,hpay,hcard,hval⟩


set_option linter.constructorNameAsVariable false in
variable [Cycle63.AffineLedger] in
include M H hH in
/-- At a presented parent of the second step, the HIGH rows of all nonzero second-stage blocks of the parent are
bounded in transport form, at every configuration `(second, bin, χ₀, t)`, by the count form of one record of the
configuration of the largest transport; the record has at most the buffer bins times the fourth power of the exponent
bins of the box classes, and it pays the reserve of the parent whenever the loss covers the frequency loss and the
shift of the class exponents. -/
theorem depth_two_high_record {ι : Type} [Fintype ι] [DecidableEq ι]
    (η₀ : Character) (Q : Ideal O) (hQM : Q≤M) (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (μ e τ bΦ qh : ℝ) (hμ : 0<μ) (hμ1 : μ≤1) (he : 0<e) (hτ : 0<τ) (hbΦ : 2≤bΦ)
    (hqh : Cycle63.Optimization.secondJunction≤qh) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(hZ : 1<Z)(hT : 2<Z^τ)(s : Input ι)(R seed : Ideal O)(Mrow amp : ℝ),
      Endpoints (9/4) (9/4) (9/4) s → Squarefree seed → R≠0 → (R.absNorm:ℝ)≤Z^(20:ℝ) →
      ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
      sourceRadius s≤Z^(3:ℝ) → CenteredMomentAmplificationChildInput.volume s≤Z^(3:ℝ) → 0≤amp → |Mrow|≤4 →
      |Real.logb Z (CenteredMomentAmplificationChildInput.volume s)|≤4 → |amp|≤4 →
      |frequencyLoss Z 32 (μ/64)+μ/8|≤4 →
      ∀(P : DepthTwoPresentation η₀ s.η R)(B Tz shift extra : ℝ),((Ideal.span {P.mult}).absNorm:ℝ)≤Z^(B-130) →
      3*Z^τ*Z^τ≤Tz → Mrow≤1 → ∀(reflected : Bool),
      ∃Hb : SecondStepHighCount M H hH (fourFixedDictionary η₀) η₀ Z B Tz (!reflected) P.mult (P.unit (!reflected)),
        (∀length ampP loss : ℝ,Real.logb Z (CenteredMomentAmplificationChildInput.volume s)≤length → amp≤ampP →
          (frequencyLoss Z 32 (μ/64)+μ/8)+μ/4+(extra+shift)≤loss+Mrow →
          Hb.Pays Cycle63.Optimization.secondJunction Mrow length ampP loss) ∧
        (Fintype.card Hb.Class:ℝ)≤depthTwoHighClassBound e μ ∧
        ∀(second : Bool)(bin : ℤ×(Fin 5→ℤ)),bin∈commonGeometryBins s R seed (Z^Mrow) Z (μ/64) →
          ∀(t : ℝ)(χ₀ : RayCharacter)
            (hP : ∀j,(affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
              (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
                else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)≠0)
            (hPN : ∀j,((((affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
              (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
                else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)).absNorm:ℝ))≤
                Z^(28:ℝ)),
            affineHighUniversalTransport M H hH η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1 one_ne_zero reflected second s R
              seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) hQ72 fixedBadMask fixedBadMask_ne_zero
              (dvd_mul_right _ _) (dvd_mul_left _ _) (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hβlo hβhi hP
              hPN qh extra≤Z^(-shift)*Hb.value := by
  filter_upwards [affine_high_universal_box (ι:=ι) M H hH η₀ Q hQM hQ72 hβlo hβhi μ e τ bΦ hμ hμ1 he hτ hbΦ,
    depth_two_high_config_record (ι:=ι) M H hH η₀ Q hQM hQ72 hβlo hβhi μ e τ bΦ qh hμ hμ1 he hτ hbΦ hqh]
    with Z hbox hcfg
  refine ⟨hbox.1,?_⟩
  intro hZ hT s R seed Mrow amp hend hseed hR hRcap hz₁ hz₂ hsource hvol hamp0 hMrow hA hamp homega P B Tz shift
    extra hvcap hTz hMrow1 reflected
  have hb := fun (second : Bool) (bin : ℤ×(Fin 5→ℤ)) (t : ℝ) (χ₀ : RayCharacter) =>
    hbox.2 hZ s R seed Mrow amp hend hseed hR hRcap hz₁ hz₂ hsource hvol hamp0 hMrow hA hamp homega reflected second
      bin t χ₀
  let Idx := Bool×{bin : ℤ×(Fin 5→ℤ) // bin∈commonGeometryBins s R seed (Z^Mrow) Z (μ/64)}×RayCharacter
  let Tr : Idx→ℝ→ℝ := fun c t =>
    affineHighUniversalTransport M H hH η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1 one_ne_zero reflected c.1 s R seed Z
      Mrow amp μ t hZ c.2.1.val hz₁ hz₂ c.2.2 (internalQ Q η₀) hQ72 fixedBadMask fixedBadMask_ne_zero
      (dvd_mul_right _ _) (dvd_mul_left _ _) (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hβlo hβhi
      (hb c.1 c.2.1.val t c.2.2).1 (hb c.1 c.2.1.val t c.2.2).2.1 qh extra
  have hmax : ∀c : Idx,∃t₀ : ℝ,∀t : ℝ,Tr c t≤Tr c t₀ := fun c =>
    affine_high_transport_max M H hH η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1 one_ne_zero c.1 reflected s R seed Z Mrow
      amp μ hZ c.2.1.val hz₁ hz₂ c.2.2 (internalQ Q η₀) fixedBadMask hQ72 fixedBadMask_ne_zero
      (dvd_mul_right _ _) (dvd_mul_left _ _) (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hβlo hβhi
      (fun t => (hb c.1 c.2.1.val t c.2.2).1) (fun t => (hb c.1 c.2.1.val t c.2.2).2.1) qh extra (148+μ/8) hμ
      (fun t => (hb c.1 c.2.1.val t c.2.2).2.2)
  choose t₀ ht₀ using hmax
  by_cases hne : Nonempty Idx
  · obtain ⟨c,-,hc⟩ := Finset.exists_max_image (Finset.univ : Finset Idx) (fun c => Tr c (t₀ c))
      (Finset.univ_nonempty_iff.mpr hne)
    have hbc := hb c.1 c.2.1.val (t₀ c) c.2.2
    obtain ⟨Hb,hpay,hcard,hval⟩ := hcfg.2 hZ hT s R seed Mrow amp hend hseed hR hRcap hz₁ hz₂ hsource hvol hamp0
      hMrow hA hamp homega P B Tz shift extra hvcap hTz hMrow1 reflected c.1 c.2.1.val (t₀ c) c.2.2 hbc.1 hbc.2.1
    have hvalue : Hb.value=Z^shift*Tr c (t₀ c) := hval
    refine ⟨Hb,hpay,hcard,?_⟩
    intro second bin hbin t χ₀ hP hPN
    have h1 : affineHighUniversalTransport M H hH η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1 one_ne_zero reflected second
        s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ (internalQ Q η₀) hQ72 fixedBadMask fixedBadMask_ne_zero
        (dvd_mul_right _ _) (dvd_mul_left _ _) (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hβlo hβhi hP hPN
        qh extra=Tr (second,⟨bin,hbin⟩,χ₀) t := rfl
    rw [h1]
    calc Tr (second,⟨bin,hbin⟩,χ₀) t≤Tr (second,⟨bin,hbin⟩,χ₀) (t₀ (second,⟨bin,hbin⟩,χ₀)) :=
          ht₀ (second,⟨bin,hbin⟩,χ₀) t
      _≤Tr c (t₀ c) := hc _ (Finset.mem_univ _)
      _=Z^(-shift)*Hb.value := by
          rw [hvalue,← mul_assoc,← Real.rpow_add (zero_lt_one.trans hZ),neg_add_cancel,Real.rpow_zero,one_mul]
  · refine ⟨SecondStepHighCount.empty M H hH (fourFixedDictionary η₀) η₀ Z B Tz (!reflected) P.mult
      (P.unit (!reflected)),?_,?_,?_⟩
    · intro length ampP loss _ _ _ σ
      exact σ.elim
    · change ((Fintype.card Empty : ℕ) : ℝ)≤_
      rw [Fintype.card_eq_zero, Nat.cast_zero]
      unfold depthTwoHighClassBound
      positivity
    · intro second bin hbin t χ₀ hP hPN
      exact absurd ⟨(second,⟨bin,hbin⟩,χ₀)⟩ hne

end
end OAI.SevenEighths.Cycle63InitialMass
