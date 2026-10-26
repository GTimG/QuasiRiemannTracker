/- Copyright (c) 2026 Hailey Collet; regional-ledger source binding
(c) 2026 Zhongpai Gao. Released under Apache 2.0.
The native retained-capacity proof is retained literally, with the ledger
made explicit rather than elaborated at the original global instance. -/
import Candidate.Cycle63.Physical.InitialMass.SecondLowGeometry
import Candidate.Cycle63.Physical.InitialMass.LowChildNonunitWidth
import Candidate.Cycle63.Physical.InitialMass.LowChildPrimeReserve
import Candidate.Cycle63.Physical.InitialMass.LowChildReturned
import Candidate.Cycle63.Moment.LowBranch.DirectDeletion
import Candidate.Research.RecursiveAffine.PhysicalDaughterSource

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCompleteCommon CenteredMomentSecondHeightFamily ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonRadialData CenteredMomentCommonRawScale
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSecondCanonicalNonunit CenteredMomentRankinRadical CenteredMomentSupport
open Cycle63InitialMass Cycle63FinalLow
open Cycle63FinalNatural Cycle63FinalCapacity
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The total plain length of a live final row, with its slot capacity, exceeds the nominal width of the child by at
most the capacity of the parent's cell and the padding, less the extraction reductions that the child keeps: the
smaller of the two first ideals, and the part of the second common ideal beyond the shift of its nonunit frequency
generator. Here `unit` is the ledger unit of the parent and `Mrow` the radial scale of the child. -/
theorem actual_regional_retained_capacity [Cycle63.AffineLedger] {s : Input α} {q : Chain s} {Z unit Mrow amp omega ξ b : ℝ} {N : ℕ}
    (g : LiveMainGeometry s q Z Mrow amp omega ξ b N) (hb : 1≤b)
    (hs : s.upper≤b) (hZ : 1<Z) (hunit : 0<unit) (hP : ∀j,1≤ s.P j)
    (hz : Cycle63.AffineLedger.slotFloor*unit≤∑j,Real.logb Z (s.P j) ∧
      (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop*unit)
    (haff : CenteredMomentEnergyBands.length Z s.X₁+CenteredMomentEnergyBands.length Z s.X₂+
      Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.B*unit)
    (η : Character) (v : ℝ) (second : Bool) (L₂ : Ideal O)
    (a : CenteredMomentDivisorAllocation.Allocation L₂ (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))) (z : O)
    (hne : Cycle63.Physical.sourcePositiveRow (q.final η v).toSource second L₂ a z≠0) :
    let cell := Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/unit))
    CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ a 0)+
      CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ a 1)+
        (6*Cycle63.Optimization.slotPrice)*CenteredMomentAllocatedChildCapacity.remainingLogs L₂ a Z (q.final η v).P-
        secondNominal unit Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive ≤
      unit*Cycle63.AffineLedger.g cell+6*amp+omega+supportPadding (Fintype.card α) b s.b₁ s.b₂ Z-
        (min (Real.logb Z (q.C₁.absNorm:ℝ)) (Real.logb Z (g.D₁.absNorm:ℝ))+
          (Real.logb Z (q.E₂.absNorm:ℝ)-
            (Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D))-
              Real.logb Z ((∏j∈g.datum.inactive,j.val).absNorm:ℝ)))) := by
  have shift : Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D))-
      Real.logb Z ((∏j∈g.datum.inactive,j.val).absNorm:ℝ)≤Real.logb Z (q.E₂.absNorm:ℝ) := by
    rcases g.label with h|h
    · rw [h]; exact actual_common_shift_le g.datum.C g.datum.D g.datum.hC g.datum.hD g.datum.sameSupport g.datum.inactive Z hZ
    · rw [h]; exact actual_common_shift_le_right g.datum.C g.datum.D g.datum.hC g.datum.hD g.datum.sameSupport g.datum.inactive Z hZ
  let X := Cycle63.Physical.sourcePlainScales (q.final η v).toSource second
  have hp : X 0*X 1=(q.final η v).X₁*(q.final η v).X₂ := by
    cases second; rfl; exact (q.final η v).same_product
  have ht := two_stage_supported_capacity s q.C₁ q.R₁ q.B₁ η v q.E₂ q.R₂ q.B₂ L₂ a Z hZ hP
    (X 0) (X 1) (Cycle63Moment.LowBranch.source_plain_positive _ second 0)
    (Cycle63Moment.LowBranch.source_plain_positive _ second 1) hp z hne
  have hr₁ := common_reduction_log_lower (Fintype.card α) b hb s le_rfl hs q.C₁ q.R₁ q.B₁ g.first_nonzero Z hZ
  have hr₂ := common_reduction_log_lower (Fintype.card α) b hb q.first (live_card_le q.B₁.val) hs
    q.E₂ q.R₂ q.B₂ g.second_nonzero Z hZ
  have hc := original_affine_capacity s Z unit hZ hunit hz haff
  have hmm : min (Real.logb Z (q.C₁.absNorm:ℝ)) (Real.logb Z (g.D₁.absNorm:ℝ))+
      max (Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (g.D₁.absNorm:ℝ)) 0=Real.logb Z (q.C₁.absNorm:ℝ) := by
    rcases le_total (Real.logb Z (q.C₁.absNorm:ℝ)) (Real.logb Z (g.D₁.absNorm:ℝ)) with h|h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  have he : CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ a 0)+
      CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ a 1)=
      CenteredMomentAllocatedChildCapacity.plainLogs L₂ a Z (X 0) (X 1) := by
    change Real.logb Z (max 1 (CenteredMomentRetainedProfile.clippedScale (_/_)))+
      Real.logb Z (max 1 (CenteredMomentRetainedProfile.clippedScale (_/_)))=_
    rw [max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _),
      max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _)]; rfl
  dsimp only at hc ht ⊢
  rw [he]; unfold secondNominal supportPadding
  change Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume s.toData)+(6*Cycle63.Optimization.slotPrice-1)*(∑j,Real.logb Z (s.P j))≤_ at hc
  change _≤_ at ht hr₂
  dsimp only [Chain.first,Chain.final,CenteredMomentCommonRadialData.commonData,
    CenteredMomentCommonHeightEnvelope.withHeight,CenteredMomentAmplificationChildInput.child] at ht hr₂ ⊢
  linarith



/-- The log norms of the ideals of a live LOW child: its own first ideal, the other one, its own second ideal and the
inactive set are nonnegative; the inactive set is below the common frequency generator, which exceeds the own second
ideal by at most the inactive set; the active conductor is below the other first ideal and the common radical below the
own second ideal. -/
theorem actual_live_child_log_facts {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b : ℝ} {N : ℕ}
    (g : LiveMainGeometry s q Z Mrow amp omega ξ b N) (hZ : 1 < Z) :
    0 ≤ Real.logb Z (q.C₁.absNorm : ℝ) ∧ 0 ≤ Real.logb Z (g.D₁.absNorm : ℝ) ∧
    0 ≤ Real.logb Z (q.E₂.absNorm : ℝ) ∧
    0 ≤ Real.logb Z ((∏ j ∈ g.datum.inactive, j.val).absNorm : ℝ) ∧
    Real.logb Z ((∏ j ∈ g.datum.inactive, j.val).absNorm : ℝ) ≤
      Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D)) ∧
    Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D)) -
      Real.logb Z ((∏ j ∈ g.datum.inactive, j.val).absNorm : ℝ) ≤ Real.logb Z (q.E₂.absNorm : ℝ) ∧
    Real.logb Z (normValue (activeConductor q.C₁ g.D₁)) ≤ Real.logb Z (g.D₁.absNorm : ℝ) ∧
    Real.logb Z ((commonRadical g.datum.C g.datum.D).absNorm : ℝ) ≤ Real.logb Z (q.E₂.absNorm : ℝ) := by
  have nn : ∀ I : Ideal O, Supported I → 0 ≤ Real.logb Z (I.absNorm : ℝ) := fun I hI =>
    Real.logb_nonneg hZ (by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1))
  have hE : Supported q.E₂ := by
    rcases g.label with h | h
    · rw [h]; exact g.datum.hC
    · rw [h]; exact g.datum.hD
  have hU : (∏ p ∈ g.datum.inactive, p.val) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun p _ => (commonPrime_supported_ideal _ _ g.datum.hC p).1)
  refine ⟨nn _ g.hC₁, nn _ g.hD₁, nn _ hE, ?_,
    CenteredMomentSecondActualWidth.actual_common_log_ge_unit g.datum.C g.datum.D g.datum.hC g.datum.inactive Z hZ,
    ?_, logb_activeConductor_le_right q.C₁ g.D₁ g.hC₁ g.hD₁ Z hZ,
    logb_commonRadical_le g.datum.C g.datum.D q.E₂ g.datum.hC g.datum.hD g.datum.sameSupport g.label Z hZ⟩
  · exact Real.logb_nonneg hZ (by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hU))
  · rcases g.label with h | h
    · rw [h]; exact actual_common_shift_le g.datum.C g.datum.D g.datum.hC g.datum.hD g.datum.sameSupport
        g.datum.inactive Z hZ
    · rw [h]; exact actual_common_shift_le_right g.datum.C g.datum.D g.datum.hC g.datum.hD g.datum.sameSupport
        g.datum.inactive Z hZ


/-- The actual nonzero live row supplies the prime reserve used by the
narrow branch. No prime-wise reserve or source-energy bound is assumed. -/
theorem actual_live_prime_reserve {s : Input α} {q : Chain s}
    {Z Mrow amp omega ξ b rate : ℝ} {N : ℕ}
    (g : LiveMainGeometry s q Z Mrow amp omega ξ b N) (hZ : 1 < Z)
    (hrate : 0 ≤ rate) (hrate2 : rate ≤ 1/2) :
    rate*(Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D))-
      Real.logb Z ((∏ j ∈ g.datum.inactive,j.val).absNorm:ℝ)-
      Real.logb Z (normValue (nonunitFrequencyGenerator g.datum.C g.datum.D g.datum.inactive))) ≤
      (Real.logb Z (q.E₂.absNorm:ℝ)-Real.logb Z ((commonRadical g.datum.C g.datum.D).absNorm:ℝ))+
      rate*((Real.logb Z (q.E₂.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D)))+
          Real.logb Z ((∏ j ∈ g.datum.inactive,j.val).absNorm:ℝ)) := by
  have hne : idealCorrelation g.datum.C g.datum.D g.datum.hC g.datum.hD
      (commonFrequencyGenerator g.datum.C g.datum.D*
        (nonunitFrequencyGenerator g.datum.C g.datum.D g.datum.inactive*g.row.val.2.2.2.val)) ≠ 0 := by
    simpa only [SecondInputDatum.block,originalSecondBlock,SecondBlockSource.frequency,mul_assoc]
      using actual_second_live_correlation (fun _ : Unit => g.datum.block) g.row
  exact second_pair_prime_reserve g.datum.C g.datum.D q.E₂ g.datum.hC g.datum.hD
    g.datum.sameSupport g.label g.datum.inactive _ hne Z hZ hrate hrate2

open Cycle63Moment.LowBranch
/-- A first-level LOW child of the unit width whose nominal width `ν`, widened by `δ`, is below the least width `Mstar`
of the second step is paid by the direct deletion at the rate `κq`. The log norms are those of the own first ideal
`c`, the other first ideal `d`, the active conductor `R`, the own second ideal `e`, the common radical `p₂`, the common
frequency generator `g₂`, the inactive set `t₂` and the nonunit frequency generator `V`. The child has the capacity
`x₁ + x₂ + 6 κ rem - ν` at most `gbar + 6 a + omega + spad` less its extraction `min c d + (e - g₂) + t₂`. The deficit
of the deletion at zero extraction, the reserve `L` and the slacks fit in the room of the cell. The overshoot of the
deletion, the amplifier `a`, the allowance `Bσ + e - p₂` of the labels and the reserve `L` then satisfy the conditions
of the direct deletion with the padding `omega + εpad`. -/
theorem actual_direct_branch_facts {κq κ a gbar L c d R e p₂ g₂ t₂ V x₁ x₂ rem ν δ omega spad εpad ωmax δmax Mstar : ℝ}
    (hκq : 0 ≤ κq) (hκq2 : κq ≤ 1 / 2)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hRd : R ≤ d) (hp₂ : p₂ ≤ e) (hL : L ≤ a)
    (ht₂ : 0 ≤ t₂) (homega : 0 ≤ omega) (hεpad : 0 ≤ εpad) (hδ : 0 ≤ δ) (hspad : spad ≤ εpad)
    (hωmax : omega ≤ ωmax) (hδmax : δ ≤ δmax)
    (hνdef : ν = 1 - (max (c - d) 0 + g₂ - t₂) - 6 * a - omega)
    (hV : V + t₂ ≤ ν + δ)
    (hprime : κq * (g₂ - t₂ - V) ≤ (e - p₂) + κq * ((e - g₂) + t₂))
    (hN4 : x₁ + x₂ + 6 * κ * rem - ν ≤ gbar + 6 * a + omega + spad - (min c d + ((e - g₂) + t₂)))
    (hnarrow : ν + δ < Mstar)
    (hcert : (κq * (gbar + 6 * a) - a) + L + κq * (δmax + εpad) + 2 * κq * ωmax ≤
      κq * (1 - 6 * a - 2 * Mstar)) :
    0 ≤ max (gbar + 6 * a - (min c d + ((e - g₂) + t₂))) 0 ∧
    x₁ + x₂ + 6 * κ * rem - ν ≤ max (gbar + 6 * a - (min c d + ((e - g₂) + t₂))) 0 + (omega + εpad) ∧
    κq * max (gbar + 6 * a - (min c d + ((e - g₂) + t₂))) 0 ≤
      a + (max (3 * c - 5 * d - R) 0 / 6 + (e - p₂)) - L := by
  have hεs : 0 ≤ omega + εpad := add_nonneg homega hεpad
  set v := max (c - d) 0 + g₂ - t₂ with hv
  set G := max (gbar + 6 * a - (min c d + ((e - g₂) + t₂))) 0 with hG
  -- the selection of the width reduction
  have hsel : (κq * (gbar + 6 * a) - a) + κq * (omega + εpad) + L ≤ κq * (max (c - d) 0 + g₂ - t₂ - V) := by
    have hnum : (κq * (gbar + 6 * a) - a) + (L + κq * (δ + εpad)) ≤ κq * (1 - 6 * a - 2 * (Mstar + omega - δ)) := by
      have h1 := mul_le_mul_of_nonneg_left hδmax hκq
      have h2 := mul_le_mul_of_nonneg_left hωmax hκq
      have h3 := mul_nonneg hκq hδ
      nlinarith [h1, h2, h3, hcert]
    have h := direct_deletion_selection (κq := κq) (a := a) (gbar := gbar) (ω := omega + εpad)
      (L := L + κq * (δ + εpad)) (Mstar := Mstar + omega - δ) (v := v) (vN := V - δ - εpad)
      (M1 := ν - εpad) hκq (by rw [hνdef]; ring) (by linarith) (by rw [hνdef] at hnarrow; linarith) hnum
    have h4 : κq * (v - (V - δ - εpad)) = κq * (max (c - d) 0 + g₂ - t₂ - V) + κq * (δ + εpad) := by
      rw [hv]; ring
    linarith only [h, h4]
  -- the reserve of the direct deletion
  have hres := direct_deletion_slack_nonneg (κq := κq) (a := a) (gbar := gbar) (ω := omega + εpad) (L := L)
    (c := c) (d := d) (R := R) (s := e) (p₂ := p₂) (g := g₂) (t := t₂) (vN := V) (r := 0) (f := 0) (κ6 := 0)
    hκq hκq2 le_rfl le_rfl le_rfl hc hd hRd hp₂ hL hprime hsel
  have hGle : G ≤ max (gbar + 6 * a + (omega + εpad) - (min c d + (e - g₂) + t₂ + 0 + 0 * 0)) 0 := by
    apply max_le_max _ le_rfl
    linarith only [hεs]
  have hκG := mul_le_mul_of_nonneg_left hGle hκq
  refine ⟨le_max_right _ _, ?_, ?_⟩
  · have := le_max_left (gbar + 6 * a - (min c d + ((e - g₂) + t₂))) 0
    linarith only [hN4, hspad, this]
  · have h2 : κq * max (gbar + 6 * a + (omega + εpad) - (min c d + (e - g₂) + t₂ + 0 + 0 * 0)) 0 ≤
        a + (max (3 * c - 5 * d - R) 0 / 6 + (e - p₂)) - L := by
      linarith only [hres]
    exact hκG.trans h2

/-- The genuine direct-source capacity and payment at an arbitrary
regional ledger. The nonunit bound and prime payment are proved from the
SAME live source. The remaining certificate is the exact scalar room
proved for the actual rounded regional/root cell. -/
theorem actual_regional_direct_source [Cycle63.AffineLedger]
    {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b εwidth εpad
      omegaMax deltaMax leastWidth rate : ℝ} {N : ℕ}
    (g : LiveMainGeometry s q Z Mrow amp omega ξ b N)
    (hb : 1 ≤ b) (hs : s.upper ≤ b) (hZ : 1 < Z)
    (hP : ∀j,1 ≤ s.P j)
    (hz : Cycle63.AffineLedger.slotFloor ≤ ∑j,Real.logb Z (s.P j) ∧
      (∑j,Real.logb Z (s.P j)) ≤ Cycle63.AffineLedger.slotTop)
    (haff : CenteredMomentEnergyBands.length Z s.X₁+CenteredMomentEnergyBands.length Z s.X₂+
      Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j)) ≤ Cycle63.AffineLedger.B)
    (hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ) ≤ 1+εwidth/2)
    (hconstants : Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+
      2*(N:ℝ)*Real.logb Z b+
      Real.logb Z (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)) ≤ εwidth/2)
    (hwidth0 : 0 ≤ εwidth) (hxi : 0 ≤ ξ) (homega : 0 ≤ omega)
    (hpad0 : 0 ≤ εpad)
    (hpad : supportPadding (Fintype.card α) b s.b₁ s.b₂ Z ≤ εpad)
    (homegaMax : omega ≤ omegaMax) (hdeltaMax : εwidth+ξ/2 ≤ deltaMax)
    (hrate : 0 ≤ rate) (hrateHalf : rate ≤ 1/2)
    (hreserve : Cycle63.AffineLedger.lowReserve ≤ amp)
    (η : Character) (v : ℝ) (second : Bool) (L₂ : Ideal O)
    (alloc : CenteredMomentDivisorAllocation.Allocation L₂ (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices q.B₂.val ⊕ Fin 2)))
    (row : O)
    (hne : Cycle63.Physical.sourcePositiveRow (q.final η v).toSource second L₂ alloc row ≠ 0)
    (hnarrow : secondNominal 1 Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive+
      (εwidth+ξ/2) < leastWidth)
    (hcert : (rate*(Cycle63.AffineLedger.g (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j))))+6*amp)-amp)+Cycle63.AffineLedger.lowReserve+
        rate*(deltaMax+εpad)+2*rate*omegaMax ≤ rate*(1-6*amp-2*leastWidth)) :
    let cell := Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j)))
    let nominal := secondNominal 1 Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
    let G := max (Cycle63.AffineLedger.g cell+6*amp-
      (min (Real.logb Z (q.C₁.absNorm:ℝ)) (Real.logb Z (g.D₁.absNorm:ℝ))+
        ((Real.logb Z (q.E₂.absNorm:ℝ)-
          Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D)))+
            Real.logb Z ((∏j∈g.datum.inactive,j.val).absNorm:ℝ)))) 0
    0 ≤ G ∧
    (CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ alloc 0)+
      CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ alloc 1)+
      6*Cycle63.Optimization.slotPrice*
        CenteredMomentAllocatedChildCapacity.remainingLogs L₂ alloc Z (q.final η v).P-nominal ≤
          G+(omega+εpad)) ∧
    rate*G ≤ amp+lowAllowance Z q.C₁ g.D₁ g.datum.C g.datum.D q.E₂-
      Cycle63.AffineLedger.lowReserve := by
  dsimp only
  obtain ⟨hc,hd,he,ht,-,-,hRd,hp⟩ := actual_live_child_log_facts g hZ
  have hprime := actual_live_prime_reserve g hZ hrate hrateHalf
  have hnonunit := live_main_nonunit_width (unit:=1) g hZ (zero_lt_one.trans_le hb)
    (by simpa only [mul_one] using hfit) (by simpa only [mul_one] using hconstants)
  simp only [mul_one] at hnonunit
  have hN4 := actual_regional_retained_capacity (unit:=1) g hb hs hZ one_pos hP
    (by simpa only [mul_one] using hz) (by simpa only [mul_one] using haff)
    η v second L₂ alloc row hne
  dsimp only at hN4
  simp only [div_one,one_mul] at hN4
  have hνdef : secondNominal 1 Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive =
      1-(max (Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (g.D₁.absNorm:ℝ)) 0+
        Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D))-
        Real.logb Z ((∏j∈g.datum.inactive,j.val).absNorm:ℝ))-6*amp-omega := by
    unfold secondNominal
    ring
  have hout := actual_direct_branch_facts
    (κ:=Cycle63.Optimization.slotPrice)
    (gbar:=Cycle63.AffineLedger.g (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j)))))
    (x₁:=CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ alloc 0))
    (x₂:=CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ alloc 1))
    (rem:=CenteredMomentAllocatedChildCapacity.remainingLogs L₂ alloc Z (q.final η v).P) hrate hrateHalf hc hd hRd hp hreserve ht homega hpad0
    (by positivity : 0 ≤ εwidth+ξ/2) hpad homegaMax hdeltaMax hνdef hnonunit hprime
    (by linarith only [hN4]) hnarrow hcert
  have hRR : Real.logb Z ((Ideal.span {activeConductor q.C₁ g.D₁}).absNorm:ℝ)=
      Real.logb Z (normValue (activeConductor q.C₁ g.D₁)) := rfl
  unfold lowAllowance lowSurplus
  rw [hRR]
  exact hout

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_regional_retained_capacity
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_live_prime_reserve
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_direct_branch_facts

#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_regional_direct_source
