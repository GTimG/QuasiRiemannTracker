/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Earlier P.1 pays the full original OLD-small numerator on a true common subclass.
The original coefficient boxes, phase count, profile constants and two tiny
powers are paid internally; the true lower dilation is charged once. -/
import Candidate.C092.transport.MixedMiddleReturnPaidSliceInput
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true
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
open HeckeDetectorRawFiber Cycle25WeightedNumeratorPhysical HeckeDetectorPhysicalSelection Cycle25DetectorRowCount
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.MixedOffsetCount QRH.Cycle090 QRH.Cycle092.SelectedNonfloor
open Cycle25.Numerator Cycle25.Weighted.Numerator
attribute [local reducible] BaselineData.toMomentData
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- Per original mask and actual common subclass. The only analytic supplier
is the earlier strong P.1 source. Constants/degree and the finite box envelope
are fixed before Z and all live physical banks. Four times 1e-13 of the final
power remains available for subsequent descriptor/bin/mask summation. -/
theorem earlier_P1_paid_small_slice
    (h : ℝ) (hh : hLower ≤ h) (hh' : h ≤ hUpper)
    (hgeometry : (inferInstance : Geometry.Parameters)=ActualGeometry.parameters h hh hh')
    (hP1 : RawTicket.EarlierP1) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {decrement epsilon : ℝ} (hdec : 0<decrement ∧ decrement ≤ 1/1000) (hepsilon : 0<epsilon) :
    ∃mesh : ℝ→ℝ,∃sourceMesh : ℝ,(∀t,0<t → 0 < mesh t) ∧ 0<sourceMesh ∧
    ∀(D : BaselineData) (F : BaselineSourceData D),
      (∀s,D.length s ≤ mesh D.t/200) → (∀s,D.length s ≤ Cycle25.sourceMesh D.t/200) →
      D.ε ≤ 1/10000000 → D.t ≤ 1/10000000 →
    ∀κplain : ℝ,7/10 ≤ κplain → κplain ≤ 3/4 → 2*HeckeZeroSupremum.beta-1 ≤ κplain →
    ∀(J : Finset (Fin D.N)) (massEps : ℝ),0 < massEps →
    ∀(reverse : Bool) (xi ann loss wmin : ℝ),0<xi → 0 ≤ ann →
      2*xi+ann ≤ witnessCollar → 0<loss → 0<wmin →
    ∀η : Character,∃M : ℕ,∃C : ℝ,0<C ∧
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀P : PaidSliceInput h decrement epsilon xi ann loss massEps sourceMesh wmin reverse D F J η Z,
    mainFront D J Z*(∑u∈commonIndices P.bank.currentSlice.fiber.rows P.bank.common,
      ‖paidOriginalSmall D F J η Z P.x P.z (Z^Geometry.y) P.bank.baseScale P.r u.val (P.data u)*
        mainProduct D F J u.val Z P.z‖) ≤
    C*(1+P.bank.height)^M*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-4*Geometry.ell/25)*
      P.bank.baseScale^(SelectedNonfloor.finalPower P.bank.a P.bank.d sourceCost P.outerFee
        (theta-1/2500000000000)) := by
  classical
  cases hgeometry
  letI := ActualGeometry.parameters h hh hh'
  obtain ⟨mesh,sourceMesh,hmesh,hsm,hpacket⟩ :=
    earlier_P1_middle_bank_final h hh hh' rfl hP1 hβ hdec hepsilon
  refine ⟨mesh,sourceMesh,hmesh,hsm,?_⟩
  intro D F hfine hstd heD htD κplain hk hk' hkβ J massEps hmass reverse xi ann loss wmin hxi hann hcollar hloss hwmin η
  obtain ⟨b0,hb0,hPhi0⟩ := radialMajorant_support_bound
  let bPhi := max 2 b0
  have hbPhi : 2 ≤ bPhi := le_max_left _ _
  have hPhi : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bPhi :=
    hPhi0.trans (Iic_subset_Iic.mpr (le_max_right _ _))
  obtain ⟨degree,controls,Csource,Jw,Cf,Cs,Cm,K,hC,hCf,hCs,hCm,hpacket⟩ :=
    hpacket D F hfine hstd heD htD κplain hk hk' hkβ J massEps hmass reverse 1 xi loss 2 bPhi wmin
      (by norm_num) hxi hloss (by norm_num) hbPhi hPhi hwmin η
  let labels := Fintype.card (Sum Bool (RayQuotient.Characters F.modulus ⊤))
  have hphase : 0 ≤ PacketJoin.phaseCardBound D := by unfold PacketJoin.phaseCardBound;positivity
  obtain ⟨Ccoef,hCcoef,hcoef⟩ := paid_coefficient_envelope labels (PacketJoin.phaseCardBound D) K
    Cs Cf Csource (QuadraticInitialBound.diagonalControl radialMajorant) degree Jw hphase hCs hCf hC
    (QuadraticInitialBound.diagonalControl_nonneg radialMajorant)
  let M := paidCountDegree K+paidMomentDegree degree Jw
  let C := (paidBoxUniformLast xi+1:ℕ)*Cm*Ccoef
  refine ⟨M,C,by dsimp [C];positivity,?_⟩
  filter_upwards [hpacket,hcoef] with Z hpacket hcoef
  refine ⟨hpacket.1,?_⟩
  intro P
  let B := P.bank
  let G := B.currentSlice.fiber
  let U := B.baseScale
  let Y := Z^Geometry.y
  let n0 := Geometry.y/B.d
  let E := SelectedNonfloor.finalPower B.a B.d sourceCost P.outerFee (theta-1/2000000000000)
  let E' := SelectedNonfloor.finalPower B.a B.d sourceCost P.outerFee (theta-1/2500000000000)
  let H := (1+B.height)^M
  let prime := ∏k : J,(Z^(D.length k.val))^(-(4/25:ℝ))
  let R := Y^(-(1/2:ℝ))*Cm*prime*Ccoef*H*U^E'
  have hZ : 0<Z := zero_lt_one.trans hpacket.1
  have hU : 1<U := B.baseScale_gt_one hpacket.1
  have hY : 0<Y := by dsimp [Y];positivity
  have hD : 0<B.d := by linarith [P.d_min]
  have hYeq : Y=U^n0 := paid_numerator_scale hZ hD.ne'
  have hHw : 0 ≤ 2*Real.pi*B.allowance+(3*B.i:ℕ)*B.T := by
    positivity [P.allowance_nonneg,P.T_nonneg]
  have hheight : 1+B.height ≤ U^(1:ℝ) := by simpa only [Real.rpow_one] using P.height_bound
  have hwit : 1+(2*Real.pi*B.allowance+(3*B.i:ℕ)*B.T) ≤ U^(1:ℝ) := by
    rw [Real.rpow_one]
    have hp : 1+B.height ≤ U := P.height_bound
    linarith only [B.frequency,hp]
  have hcap : Physical.Selection.zeroCapacity Geometry.y sourceCost B.d ≤ n0-1/2 :=
    paid_capacity hh hD P.d_max
  have hbasebins := paid_native_phase_card D F B P.base_slots P.base_bin
  have ha0 : (51/100:ℝ) ≤ B.a := B.a_min.le
  have ha1 : B.a ≤ 7/8 := by linarith [B.delta_max]
  have hx : (51/100:ℝ) ≤ P.x.re := by rw [P.x_re];linarith [D.e_pos]
  have hz : (17/50:ℝ) ≤ P.z.re := P.z_re.ge
  have hR : 0 ≤ R := by dsimp [R,H,prime];positivity [B.height_nonneg]
  have hbox (j : ℕ) (hj : j∈paidSmallBoxes P.r xi) :
      (∑u∈commonIndices G.rows B.common,‖originalSmallBoxPacket D F J η u.val Z P.x P.z (P.data u) Y U xi
        (MixedTicketTails.originalVcut P.r) (paidBoxLast P.r xi) j*mainProduct D F J u.val Z P.z‖) ≤ R := by
    let v : ℝ := (j:ℝ)*xi
    let nref := paidReference n0 v xi ann
    let mw := paidWindow n0 v xi ann
    have hv : 0 ≤ v := by dsimp [v];positivity
    have hvcut : v ≤ MixedTicketTails.originalVcut P.r := (paidSmallBoxes_mem hj).2.le
    have href := paid_reference h ⟨hh,hh'⟩ P.row ⟨P.d_old,P.d_max⟩ ⟨hv,hvcut⟩ hxi.le hann hcollar
    change RawTicket.nLo ≤ nref ∧ nref ≤ RawTicket.nHi ∧ 0 ≤ mw ∧ mw+xi=nref ∧
      nref ≤ 1-n0+v+witnessCollar at href
    let data : ∀u : G.rows,PhysicalReflectionData F.S F.exclusions.prime u.val := P.data
    let N := fun (u : G.rows) (e : LabelPacketIndex F.S u.val (fun k : J=>sourcePrimePool F Z k.val))=>
      (labelPacketScale F.S u.val (fun k : J=>sourcePrimePool F Z k.val) e:ℝ)
    let Active := fun (u : G.rows) (e : LabelPacketIndex F.S u.val (fun k : J=>sourcePrimePool F Z k.val))=>
      N u e≤2*Y ∧ max 1 ((data u).combinedConductor/((fixedConductorConstant F.S:ℝ)*rowNorm u.val)*N u e)<U^(MixedTicketTails.originalVcut P.r) ∧
      dilationBox U xi (paidBoxLast P.r xi) (max 1 ((data u).combinedConductor/((fixedConductorConstant F.S:ℝ)*rowNorm u.val)*N u e))=j
    have hbounds u e (he : Active u e) := small_true_box_bounds hU hxi.le (paidBox_cover P.r hxi)
      (le_max_left _ _) he.2.1 he.2.2
    have hcombined u e (he : Active u e) :
        (data u).combinedConductor ≤ (fixedConductorConstant F.S:ℝ)*U^mw*(Y/N u e) := by
      have hN : 0<N u e := by
        dsimp [N]
        have hn := labelPacketScale_one_le F.S u.val (fun k : J=>sourcePrimePool F Z k.val) e
        exact lt_of_lt_of_le zero_lt_one (by exact_mod_cast hn)
      apply paid_tuple_window F.S F.exclusions.prime u.val (data u) hU hN hYeq
        (P.row_upper u.val u.property) hann
      convert (hbounds u e he).2.1 using 1 <;> dsimp [v] <;> congr 1 <;> ring
    have hs := hpacket.2 B P.reverse_eq P.T_nonneg P.allowance_nonneg hheight hwit P.current_slots P.fine
      P.widths P.row_lower (Finset.univ\J) nref href.1 href.2.1 P.ordinary_min P.ordinary_max
      P.x P.z ha0 ha1 P.x_re P.z_re data Active Y mw v hY href.2.2.1
      href.2.2.2.1.le hv P.row_upper (fun u e he=>he.1) hcombined (fun u e he=>(hbounds u e he).1)
      P.r P.row P.point P.d_min P.d_max P.gamma P.collar P.factor P.offset_nonneg P.offset_max
      n0 hcap href.2.2.2.2 P.slot_upper P.outerFee P.fee_paid
    have hc := hcoef.2 B.d B.height (2*Real.pi*B.allowance+(3*B.i:ℕ)*B.T) (mw+xi)
      (Fintype.card B.base.batch.Bin) P.d_min B.height_nonneg hHw B.frequency
      (href.2.2.2.1.le.trans href.2.1) hbasebins
    change max 1 (B.coefficient K)*paidMoment Cs Cf Csource (QuadraticInitialBound.diagonalControl radialMajorant)
      degree Jw U B.height (2*Real.pi*B.allowance+(3*B.i:ℕ)*B.T) (mw+xi) ≤ Ccoef*H*U^(1/50000000000000:ℝ) at hc
    have hsum : (∑u∈commonIndices G.rows B.common,‖originalSmallBoxPacket D F J η u.val Z P.x P.z (P.data u) Y U xi
        (MixedTicketTails.originalVcut P.r) (paidBoxLast P.r xi) j*mainProduct D F J u.val Z P.z‖) =
      ∑u∈commonIndices G.rows B.common,‖originalSmallBoxPacket D F J η u.val Z P.x P.z (data u) Y U xi
        (MixedTicketTails.originalVcut P.r) (paidBoxLast P.r xi) j*G.physicalProduct (Finset.univ\J) u.val‖ := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [native_original_main D F B hZ J P.z P.external_eq]
    rw [hsum]
    have hs' : (∑u∈commonIndices G.rows B.common,‖originalSmallBoxPacket D F J η u.val Z P.x P.z (data u) Y U xi
      (MixedTicketTails.originalVcut P.r) (paidBoxLast P.r xi) j*G.physicalProduct (Finset.univ\J) u.val‖) ≤
      Y^(-(1/2:ℝ))*(Cm*prime)*(max 1 (B.coefficient K))*
      paidMoment Cs Cf Csource (QuadraticInitialBound.diagonalControl radialMajorant)
        degree Jw U B.height (2*Real.pi*B.allowance+(3*B.i:ℕ)*B.T) (mw+xi)*U^E := by
      simpa only [originalSmallBoxPacket,Active,N,data,paidMoment,prime,E,mul_assoc] using hs
    apply hs'.trans
    let A := Y^(-(1/2:ℝ))*(Cm*prime)
    have hA : 0 ≤ A := by dsimp [A,prime];positivity
    calc
      _ = A*(max 1 (B.coefficient K)*paidMoment Cs Cf Csource (QuadraticInitialBound.diagonalControl radialMajorant)
        degree Jw U B.height (2*Real.pi*B.allowance+(3*B.i:ℕ)*B.T) (mw+xi))*U^E := by dsimp [A];ring
      _ ≤ A*(Ccoef*H*U^(1/50000000000000:ℝ))*U^E :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hA) (by positivity)
      _ = Y^(-(1/2:ℝ))*Cm*prime*Ccoef*H*U^(E+1/50000000000000:ℝ) := by
        rw [Real.rpow_add (zero_lt_one.trans hU)];dsimp [A];ring
      _ ≤ R := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hU.le (paid_power_absorb hD P.d_hi)) (by dsimp [H,prime];positivity [B.height_nonneg])
  have hnorm : (∑u∈commonIndices G.rows B.common,‖paidOriginalSmall D F J η Z P.x P.z Y U P.r u.val (P.data u)*
      mainProduct D F J u.val Z P.z‖) ≤ (paidBoxUniformLast xi+1:ℕ)*R := by
    calc
      _ ≤ ∑u∈commonIndices G.rows B.common,∑j∈paidSmallBoxes P.r xi,
          ‖originalSmallBoxPacket D F J η u.val Z P.x P.z (P.data u) Y U xi
            (MixedTicketTails.originalVcut P.r) (paidBoxLast P.r xi) j*mainProduct D F J u.val Z P.z‖ := by
        apply Finset.sum_le_sum
        intro u hu
        unfold paidOriginalSmall
        rw [small_packet_paid_boxes D F J η u.val Z P.x P.z (P.data u) Y U xi P.r hU hxi hY
          (P.nonprincipal u.val u.property) hx hz P.margin,Finset.sum_mul]
        exact norm_sum_le _ _
      _ = ∑j∈paidSmallBoxes P.r xi,∑u∈commonIndices G.rows B.common,
          ‖originalSmallBoxPacket D F J η u.val Z P.x P.z (P.data u) Y U xi
            (MixedTicketTails.originalVcut P.r) (paidBoxLast P.r xi) j*mainProduct D F J u.val Z P.z‖ := Finset.sum_comm
      _ ≤ ∑_j∈paidSmallBoxes P.r xi,R := Finset.sum_le_sum hbox
      _ = ((paidSmallBoxes P.r xi).card:ℝ)*R := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (paidSmallBoxes_card P.row hxi)) hR
  have hfront : 0 ≤ mainFront D J Z := by unfold mainFront;positivity
  apply (mul_le_mul_of_nonneg_left hnorm hfront).trans_eq
  have hp := original_prime_front D J hZ
  change mainFront D J Z*prime=Z^(-4*Geometry.ell/25) at hp
  change mainFront D J Z*((paidBoxUniformLast xi+1:ℕ)*(Y^(-(1/2:ℝ))*Cm*prime*Ccoef*H*U^E'))=_
  rw [show mainFront D J Z*((paidBoxUniformLast xi+1:ℕ)*(Y^(-(1/2:ℝ))*Cm*prime*Ccoef*H*U^E'))=
      ((paidBoxUniformLast xi+1:ℕ)*Cm*Ccoef)*H*Y^(-(1/2:ℝ))*(mainFront D J Z*prime)*U^E' by ring,hp]

#print axioms earlier_P1_paid_small_slice
end
end QRH.Cycle092.MixedMiddleReturn
