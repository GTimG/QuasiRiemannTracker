/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Earlier actual PairAt -> genuine witness Fourier columns -> original Y/N
numerator. The full P15 max-one dilation divisor occurs EXACTLY once. -/
import Candidate.C092.transport.MixedMiddleReturnEarlier
import Candidate.C092.transport.MixedMiddleReturnPhysical
import Candidate.C092.transport.SourceWindowCompactOriginal
import Candidate.C092.transport.MixedOffsetCountBankFacts



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

open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.SelectedNonfloor Cycle25.Numerator Cycle25.Weighted.Numerator
set_option allowUnsafeReducibility true
attribute [local reducible] BaselineData.toMomentData

variable [Geometry.Parameters]

/-- Original true-bank middle packet at the final Q.2 numerator power.
EarlierP1 is its only conditional analytic supplier. All component source
metadata, moving mixed moments, P15 mass, centered count and physical reserve
are derived; explicit premises are literal physical/contour/event guards. -/
theorem earlier_P1_middle_bank_final
    (h : ℝ) (hh : QRH.Cycle090.hLower ≤ h) (hh' : h ≤ QRH.Cycle090.hUpper)
    (hgeometry : (inferInstance : Geometry.Parameters)=ActualGeometry.parameters h hh hh')
    (hP1 : RawTicket.EarlierP1) (hβ : (51/100:ℝ)  ≤  HeckeZeroSupremum.beta)
    {decrement epsilon : ℝ} (hd : 0<decrement ∧ decrement ≤ 1/1000) (hepsilon : 0<epsilon) :
    ∃mesh : ℝ→ℝ,∃sourceMesh : ℝ,(∀t,0<t → 0 < mesh t) ∧ 0 < sourceMesh ∧
    ∀(D₀ : BaselineData) (F₀ : BaselineSourceData D₀),
      (∀s,D₀.length s  ≤  mesh D₀.t/200) →
      (∀s,D₀.length s  ≤  Cycle25.sourceMesh D₀.t/200) →
      D₀.ε  ≤  1/10000000 → D₀.t  ≤  1/10000000 →
    ∀κplain : ℝ,7/10  ≤  κplain → κplain  ≤  3/4 → 2*HeckeZeroSupremum.beta-1  ≤  κplain →
    ∀(J : Finset (Fin D₀.N)) (massEps : ℝ),0 < massEps →
    ∀(reverse : Bool) (tau xi loss b bPhi wmin : ℝ),
      0  ≤  tau → 0<xi → 0<loss → 0<b → 2 ≤ bPhi →
      Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi → 0<wmin →
    ∀η : Character,
    ∃degree : ℕ,∃controls : Finset (ℕ×ℕ),∃Csource : ℝ,∃Jw : ℕ,
    ∃Cfourier Cscale Cmass : ℝ,∃K : MixedOffsetCount.CountConstants,
      0<Csource ∧ 0<Cfourier ∧ 0<Cscale ∧ 0<Cmass ∧
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀B : MixedOffsetCount.MiddleBank D₀.toMomentData F₀ η Z,
    let U := B.baseScale
    let a := B.a
    let ε := D₀.ε
    let T := B.T
    let allowance := B.allowance
    let i := B.i
    let F := B.currentSlice.fiber
    F.reverse=reverse → 0  ≤  T → 0  ≤  allowance →
      1+B.height  ≤  U^tau → 1+(2*Real.pi*allowance+(3*i : ℕ)*T)  ≤  U^tau →
      F.slots=Finset.univ → F.mesh ≤ sourceMesh → (∀s∈F.slots,wmin ≤ F.widths s) →
      (∀u∈F.rows,Z^(1/100:ℝ) ≤ rowNorm u) →
    ∀(main : Finset (Fin D₀.N)) (nref : ℝ),RawTicket.nLo ≤ nref → nref ≤ RawTicket.nHi →
      Mixed.widthLo ≤ F.m → F.m ≤ Mixed.widthHi →
    ∀(x z : ℂ),51/100  ≤  a → a  ≤  7/8 → x.re=a+16*D₀.e → z.re=17/50 →
    ∀ (data : ∀u : F.rows,PhysicalReflectionData F₀.S F₀.exclusions.prime u.val),
    let Index := fun u : F.rows=>LabelPacketIndex F₀.S u.val (fun k : J=>sourcePrimePool F₀ Z k.val)
    let A := fun u : F.rows=>labelPacketCoefficient F₀.S F₀.exclusions η u.val
      (fun k : J=>sourcePrimePool F₀ Z k.val) (fun k=>source_prime_pool_outside F₀ Z k.val)
      (fun k P=>physicalSlotWeight P.val F₀.W (Z^(D₀.length k.val)) z) x z
    let N := fun (u : F.rows) (e : Index u)=>(labelPacketScale F₀.S u.val (fun k : J=>sourcePrimePool F₀ Z k.val) e:ℝ)
    ∀(Active : ∀u,Index u→Prop) (Y mWindow v : ℝ),
      0<Y → 0  ≤  mWindow → mWindow+xi  ≤  nref → 0  ≤  v →
      (∀u∈F.rows,rowNorm u ≤ U) →
      (∀u e,Active u e → N u e  ≤  b*Y) →
      (∀u e,Active u e → (data u).combinedConductor  ≤  (fixedConductorConstant F₀.S:ℝ)*U^mWindow*(Y/N u e)) →
      (∀u e,Active u e → U^v  ≤  max 1 ((data u).combinedConductor/
        ((fixedConductorConstant F₀.S:ℝ)*rowNorm u.val)*N u e)) →
    ∀(r : TopData.Row),r∈TopData.rows → r.box.Contains (B.delta,B.p) →
      (1/100:ℝ)  ≤  B.d → B.d  ≤  h+Cycle090.rowPad →
      B.γ=(Mixed.rowGamma r.box r.B:ℝ) → B.εa=Cycle090.witnessCollar →
      B.factor=(Mixed.rowV r.box:ℝ)/(r.box.uHi:ℝ) →
      0  ≤  B.xi → B.xi  ≤  (Mixed.rowGamma r.box r.B:ℝ) →
    ∀n0 : ℝ,Physical.Selection.zeroCapacity Geometry.y Cycle090.sourceCost B.d  ≤  n0-1/2 →
      nref  ≤  1-n0+v+Cycle090.witnessCollar →
      (∀u∈(B.common),∀s∈main,‖physical F₀.modulus ⊤ (fun w : FreeRow=>w.val)
        F.profile F.upper F.widths F.external U u s‖  ≤  U^(F.widths s*(F.bin s+F.binWidth))) →
    let L := ∑s∈F.slots,F.widths s
    let Cmoment := max 1 (Cscale*((1+2*((mWindow+xi)*Real.log U))*
      (Cfourier*Csource*QuadraticInitialBound.diagonalControl radialMajorant*
        (1+B.height)^degree*(1+(2*Real.pi*allowance+(3*i : ℕ)*T))^(2*Jw+1))+1))
    let fee := (2*a-1)*(B.p)*decrement+F.binWidth*L+(2*a-1)*F.mesh/2+ε+((B.loss)+epsilon+loss)/2
    ∀outerFee : ℝ,B.d*(fee+massEps)+outerFee  ≤  Cycle090.paddingDebit+(1/100000000000000:ℝ) →
    (∑u∈commonIndices F.rows (B.common),‖((Y:ℂ)^(-(1/2:ℂ))*(∑' e,A u e*(N u e:ℂ)^(-(1/2:ℂ))*
        (if Active u e then polynomial (rowCharacter F₀.S F₀.exclusions.prime u.val) false F₀.W (Y/N u e) 0 0 else 0)))*
        F.physicalProduct main u.val‖)  ≤  Y^(-(1/2:ℝ))*(Cmass*(∏k : J,(Z^(D₀.length k.val))^(-(4/25:ℝ))))*(max 1 (B.coefficient K))*Cmoment*
      U^(SelectedNonfloor.finalPower a B.d Cycle090.sourceCost outerFee (Cycle090.theta-1/2000000000000)) := by
  classical
  cases hgeometry
  letI := ActualGeometry.parameters h hh hh'
  obtain ⟨mesh,sourceMesh,hmesh,hsm,hpacket⟩ := earlier_P1_middle_bank_packet hP1 hβ hd hepsilon
  refine ⟨mesh,sourceMesh,hmesh,hsm,?_⟩
  intro D₀ F₀ hfine hstd heD htD κplain hk hk' hkβ J massEps he
    reverse tau xi loss b bPhi wmin htau hxi hloss hb hbPhi hPhi hwmin η
  obtain ⟨degree,controls,Csource,Jw,Cf,Cs,Cm,K,hC,hCf,hCs,hCm,hpacket⟩ :=
    hpacket D₀ F₀ hfine hstd heD htD κplain hk hk' hkβ J massEps he
      reverse tau xi loss b bPhi wmin htau hxi hloss hb hbPhi hPhi hwmin η
  refine ⟨degree,controls,Csource,Jw,Cf,Cs,Cm,K,hC,hCf,hCs,hCm,?_⟩
  filter_upwards [hpacket] with Z hpacket
  refine ⟨hpacket.1,?_⟩
  intro B
  dsimp only
  let F := B.currentSlice.fiber
  intro hrev hT hall hheight hwit hslots hmesh hwidth hlower main nref hn0 hn1 hz0 hz1
    x z ha0 ha1 hx hz data
  intro Active Y mWindow v hY hm hMN hv hrow hactive hcombined hbox
    r hr hp hD hDh hgamma hcollar hfactor hξ hξ' n0 hcap href hupper
  intro outerFee hfee
  have hg := native_directed_guards B hr hp
  let cap := Physical.Selection.zeroCapacity Geometry.y Cycle090.sourceCost B.d
  let pen := B.penalty (Mixed.rowKLower r.box) (Mixed.rowKUpper r.box) ((Mixed.rowM r.box:ℝ)+Cycle090.witnessCollar)
  let L := ∑s∈F.slots,F.widths s
  let fee := (2*B.a-1)*B.p*decrement+F.binWidth*L+(2*B.a-1)*F.mesh/2+D₀.ε+(B.loss+epsilon+loss)/2
  let gain := B.p*(PacketJoinE49.Return.line.g1*F.m-PacketJoinE49.Return.line.g0/2+Cycle090.sourceGain F.m)+pen/2-B.p*Cycle090.witnessCollar/2
  let Cmoment := max 1 (Cs*((1+2*((mWindow+xi)*Real.log B.baseScale))*
    (Cf*Csource*QuadraticInitialBound.diagonalControl radialMajorant*
      (1+B.height)^degree*(1+(2*Real.pi*B.allowance+(3*B.i:ℕ)*B.T))^(2*Jw+1))+1))
  have hL : L=Geometry.ell/B.d := by
    change (∑s∈F.slots,F.widths s)=_
    rw [hslots]
    change (∑s : Fin D₀.N,B.current.batch.widths s)=_
    rw [B.current.widths,←Finset.sum_div,D₀.slots_sum]
  have hpow := native_middle_power_le_final B hr hp hh hh' hD hDh hgamma hcollar hfactor
    hξ hξ' hz0 hz1 (fee:=fee) (massEps:=massEps) (outerFee:=outerFee) hv hfee
  have hbound := hpacket.2 B hrev hT hall hheight hwit hslots hmesh hwidth hlower main nref hn0 hn1 hz0 hz1
    x z ha0 ha1 hx hz data Active Y mWindow v hY hm hMN hv hrow hactive hcombined hbox
    (Mixed.rowKLower r.box) (Mixed.rowKUpper r.box) ((Mixed.rowM r.box:ℝ)+Cycle090.witnessCollar) cap n0
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 hcap href hupper
  let pref := Y^(-(1/2:ℝ))*(Cm*(∏k : J,(Z^(D₀.length k.val))^(-(4/25:ℝ))))*
    (max 1 (B.coefficient K))*Cmoment
  have hUp : 1<B.baseScale := B.baseScale_gt_one hpacket.1
  let E := (2*B.a-1)*B.p*(L-cap/2)+(3*B.R+1)/4-(2*B.a-1)*gain+fee-(2*B.a-1)*(1-B.p)*v/2
  have hE : SelectedNonfloor.packetPower B.a B.p B.R B.d Cycle090.sourceCost 0
      (fee+massEps-B.delta*gain-B.delta*(1-B.p)*v/2)=massEps+E := by
    dsimp only [SelectedNonfloor.packetPower,E,MixedOffsetCount.MiddleBank.delta]
    rw [←hL]
    ring
  have hpref : 0 ≤ pref := by
    dsimp only [pref]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hY.le _) (mul_nonneg hCm.le
      (Finset.prod_nonneg (fun k _=>Real.rpow_nonneg (Real.rpow_nonneg (zero_lt_one.trans hpacket.1).le _) _))))
      (zero_le_one.trans (le_max_left _ _))) (zero_le_one.trans (le_max_left _ _))
  apply hbound.trans
  calc
    _ = pref*B.baseScale^(SelectedNonfloor.packetPower B.a B.p B.R B.d Cycle090.sourceCost 0
      (fee+massEps-B.delta*gain-B.delta*(1-B.p)*v/2)) := by
      rw [hE,Real.rpow_add (zero_lt_one.trans hUp)]
      change Y^(-(1/2:ℝ))*(Cm*B.baseScale^massEps*(∏k : J,(Z^(D₀.length k.val))^(-(4/25:ℝ))))*
        (max 1 (B.coefficient K))*Cmoment*B.baseScale^E=pref*(B.baseScale^massEps*B.baseScale^E)
      dsimp only [pref]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hUp.le hpow) hpref

#print axioms earlier_P1_middle_bank_final
end
end QRH.Cycle092.MixedMiddleReturn
