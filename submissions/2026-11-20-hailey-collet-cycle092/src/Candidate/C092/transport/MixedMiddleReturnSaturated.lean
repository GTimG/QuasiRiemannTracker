/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Earlier actual PairAt -> genuine witness Fourier columns -> original Y/N
numerator. The full P15 max-one dilation divisor occurs EXACTLY once. -/
import Candidate.C092.transport.MixedMiddleReturnMain

import Candidate.C092.transport.MixedPacketWitnessMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification
open ConcretePrimeRowBridge CanonicalRowCompletion ProbeHighRowFamily HeckeRowClosure ProbePhysical
open ProbeRowRadicalConductor Cycle25.Weighted.Numerator
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorDictionary
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization CenteredMomentLattice
open CenteredMomentEnergyBands CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainFiberSource
open HeckeDetectorRawFiber Cycle25WeightedNumeratorPhysical
open HeckeDetectorPhysicalSelection Cycle25DetectorRowCount
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair QRH.Cycle092.WitnessRowSup
open QRH.Cycle092.MixedPacketScale QRH.Cycle092.MixedPacketWitness
local notation "O" => HeckeFamily.O

/-- Actual numerator-only middle return. Earlier PairAt pays the complete
true-dilation tuple series; main-only whole-slot selection and the genuine
ordinary spike are derived. The strongest centered bank supplier feeds its
cardinality input in the native endpoint wrapper. -/
theorem saturated_packet_return {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (reverse : Bool) (controls : Finset (ℕ×ℕ))
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S)
    (G : 𝓢(ℝ,ℂ)) (degree : ℕ) (Csource epsilon tau xi loss b : ℝ)
    (hCsource : 0   ≤   Csource) (hepsilon : 0   ≤   epsilon) (htau : 0   ≤   tau)
    (hxi : 0<xi) (hloss : 0<loss) (hb : 0<b) :
    ∃ Jw : ℕ,∃ Cfourier Cscale : ℝ,0<Cfourier ∧ 0<Cscale ∧
    ∀ᶠ U : ℝ in atTop,1<U ∧
    ∀{M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
      (hH : RayOrthogonality.globalUnits M   ≤   H)
      {Label : Type} {a ε cutoff T allowance : ℝ} {i : ℕ}
      (F : Fiber M H Label Slot U a ε cutoff T allowance i) (ηW : Character),
      F.reverse=reverse → F.rowData=momentData ηW →
    ∀P : WholePresentation M H hH S hS F ηW controls,
      P.seed.degree=degree → P.seed.C=Csource → P.seed.epsilon=epsilon →
      1/2 ≤ a → 0 ≤ T → 0 ≤ allowance → 0 ≤ P.seed.N → length U (U^F.m) ≤ P.seed.Y →
      1+P.seed.height ≤ U^tau → 1+(2*Real.pi*allowance+(3*i : ℕ)*T) ≤ U^tau →
      F.slots=Finset.univ →
    ∀(main : Finset Slot),0 ≤ P.seed.l → P.seed.l ≤ ∑s∈F.slots,F.widths s →
    ∀ (data : ∀u : F.rows,PhysicalReflectionData S hS u.val)
      (Index : F.rows→Type) (base : ∀u,Index u)
      (A : ∀u,Index u→ℂ) (N : ∀u,Index u→ℝ) (Active : ∀u,Index u→Prop)
      (Y mWindow v Mass : ℝ),
      0<Y → (∀u e,0<N u e) → 0 ≤ mWindow → mWindow+xi ≤ P.seed.N → 0 ≤ v → 0<Mass →
      (∀u e,Active u e → N u e ≤ b*Y) →
      (∀u e,Active u e → (data u).combinedConductor ≤ (fixedConductorConstant S:ℝ)*U^mWindow*(Y/N u e)) →
      (∀u e,Active u e → U^v ≤ max 1 ((data u).combinedConductor/
        ((fixedConductorConstant S:ℝ)*rowNorm u.val)*N u e)) →
    let Lc := fun u : F.rows=>(data u).combinedConductor/((fixedConductorConstant S:ℝ)*rowNorm u.val)
    (∀u,Summable (fun e=>‖A u e‖*(N u e)^(-(1/2:ℝ))*max 1 (Lc u*N u e)^((2*a-1)/2))) →
    (∀u,(∑' e,‖A u e‖*(N u e)^(-(1/2:ℝ))*max 1 (Lc u*N u e)^((2*a-1)/2)) ≤ Mass) →
    ∀(common : Finset FreeRow),common⊆F.rows →
    ∀(R pen mBase countLoss p cap n0 nref decrement g₀ g₁ Ccount : ℝ),
      1 ≤ Ccount → 0 ≤ p → p ≤ 1 → F.q=(2*a-1)*p →
      R=1-(2*a-1)*(p*(1+2*g₀)+2*(1-p*(1+2*g₁))*mBase) →
      cap ≤ n0-1/2 → nref ≤ 1-n0+v+QRH.Cycle090.witnessCollar →
      QRH.Cycle090.sourceWidth nref F.m-decrement ≤ P.seed.l →
      (common.card:ℝ) ≤ Ccount*U^(R-(2*a-1)*(pen-(1-p*(1+2*g₁))*(F.m-mBase))+countLoss) →
      (∀u∈common,∀s∈main,‖physical M H (fun w : FreeRow=>w.val)
        F.profile F.upper F.widths F.external U u s‖ ≤ U^(F.widths s*(F.bin s+F.binWidth))) →
    let L := ∑s∈F.slots,F.widths s
    let Cmoment := max 1 (Cscale*((1+2*((mWindow+xi)*Real.log U))*
      (Cfourier*Csource*QuadraticInitialBound.diagonalControl radialMajorant*
        (1+P.seed.height)^degree*(1+(2*Real.pi*allowance+(3*i : ℕ)*T))^(2*Jw+1))+1))
    let fee := (2*a-1)*p*decrement+F.binWidth*L+(2*a-1)*F.mesh/2+ε+(countLoss+epsilon+loss)/2
    (∑u∈commonIndices F.rows common,‖(∑' e,A u e*(N u e:ℂ)^(-(1/2:ℂ))*
        (if Active u e then polynomial (rowCharacter S hS u.val) false G (Y/N u e) 0 0 else 0))*
        F.physicalProduct main u.val‖) ≤ Mass*Ccount*Cmoment*
      U^((2*a-1)*p*(L-cap/2)+(3*R+1)/4-
        (2*a-1)*(p*(g₁*F.m-g₀/2+QRH.Cycle090.sourceGain F.m)+pen/2-p*QRH.Cycle090.witnessCollar/2)+
        fee-(2*a-1)*(1-p)*v/2) := by
  classical
  obtain ⟨Jw,Cf,Cs,hCf,hCs,hpacket⟩ := earlier_pair_packet_bound (Slot:=Slot) reverse controls
    S hS hbad G degree Csource epsilon tau xi loss b hCsource hepsilon htau hxi hloss hb
  refine ⟨Jw,Cf,Cs,hCf,hCs,?_⟩
  filter_upwards [hpacket] with U hpacket
  refine ⟨hpacket.1,?_⟩
  intro M _ H hH Label a ε cutoff T allowance i F ηW hrev hdata
    P hdegree hC heps ha hT hall hN hXY hheight hwit hslots main hl hlL
    data Index base A N Active Y mWindow v Mass hY hNs hm hMN hv hMass hactive hcombined hbox
  dsimp only
  intro hs hmass common hcommon R pen mBase countLoss p cap n0 nref decrement g₀ g₁ Ccount
    hc hp hp' hq hR hcap href hquota hcount hupper
  let δ := 2*a-1
  let L := ∑s∈F.slots,F.widths s
  let qMain := weightedMean F.slots F.widths (Cycle25DetectorRowCount.maskedGain main F.bin)
  have hδ : 0 ≤ δ := by dsimp [δ];linarith
  obtain ⟨hq0,hqfull,sel,hsel,hselMain,hlen,hspike⟩ := saturated_main_selection F hpacket.1 ha main
    (hslots ▸ Finset.subset_univ main) P.seed.l hl hlL
  let D := P.select sel hsel hlen
  have hmark (u : F.rows) : (∏k∈D.selected,D.mark k u.val)=F.physicalProduct sel u.val := by
    apply Finset.prod_congr rfl
    intro k hk
    exact P.mark k (hsel hk) u.val u.property
  have hselLower (u : F.rows) (hu : u∈commonIndices F.rows common) :
      U^(qMain*P.seed.l-δ*F.mesh/2) ≤ ‖∏k∈D.selected,D.mark k u.val‖ := by
    rw [hmark u]
    exact hspike u.val u.property
  have hfull (u : F.rows) (hu : u∈commonIndices F.rows common) :
      ‖F.physicalProduct main u.val‖ ≤ U^(qMain*L+F.binWidth*L) :=
    main_product_upper F hpacket.1 hslots main u.val
      (hupper u.val (Finset.mem_filter.mp hu).2)
  have hc' : (common.card:ℝ) ≤ Ccount*U^((R+countLoss)-δ*(pen-(1-p*(1+2*g₁))*(F.m-mBase))) := by
    convert hcount using 1
    congr 2
    dsimp [δ]
    ring
  have hh := hpacket.2 hH F ηW hrev hdata D hdegree hC heps (by linarith) hT hall hN hXY hheight hwit
    data Index base A N Active Y mWindow (δ/2) v Mass hY hNs hm hMN
    (by positivity) hv hMass.le hactive hcombined hbox hs hmass common hcommon
    (fun u=>F.physicalProduct main u.val) (fun _=>1) (R+countLoss)
    (δ*(pen-(1-p*(1+2*g₁))*(F.m-mBase))) (qMain*L+F.binWidth*L) 0
    (qMain*P.seed.l-δ*F.mesh/2) Ccount hc hMass hc' hselLower hfull
    (fun u _=>by rw [Real.rpow_zero];norm_num)
  simp only [mul_one] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hpacket.1.le
  have hmask : qMain*(L-P.seed.l) ≤ δ*p*(L-QRH.Cycle090.sourceWidth nref F.m+decrement) := by
    have hlower : 0 ≤ L-QRH.Cycle090.sourceWidth nref F.m+decrement := by dsimp [L];linarith only [hquota,hlL]
    have h1 := mul_le_mul_of_nonneg_left hquota hq0
    have h2 := mul_le_mul_of_nonneg_right hqfull hlower
    rw [hq] at h2
    change qMain ≤ F.q at hqfull
    nlinarith only [h1,h2]
  have hgain := middle_gain_of_reference hδ hp hp' hv hcap href hR
    (L:=L) (inv:=0) (pen:=pen) (z:=F.m) (m:=mBase)
  dsimp [δ] at hmask hgain ⊢
  nlinarith only [hmask,hgain]

#print axioms saturated_packet_return
end
end QRH.Cycle092.MixedMiddleReturn
