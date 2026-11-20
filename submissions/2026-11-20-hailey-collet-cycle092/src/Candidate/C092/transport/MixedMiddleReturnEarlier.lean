/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Earlier actual PairAt -> genuine witness Fourier columns -> original Y/N
numerator. The full P15 max-one dilation divisor occurs EXACTLY once. -/
import Candidate.C092.transport.MixedMiddleReturnBank
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
variable [Geometry.Parameters]
set_option allowUnsafeReducibility true
attribute [local reducible] BaselineData.toMomentData

/-- Genuine full original middle-bank numerator from EarlierP1 alone. The
finite source bank, fixed metadata, actual prime dictionaries and keeps,
whole-slot selection, mixed moment, P15 mass and centered count are all
proved internally before the live reference pair and true-dilation slice. -/
theorem earlier_P1_middle_bank_packet
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
    ∀(lo hi Mbound cap n0 : ℝ),
      0  ≤  lo → lo  ≤  B.k → B.k  ≤  hi → B.m  ≤  Mbound →
      cap  ≤  n0-1/2 → nref  ≤  1-n0+v+QRH.Cycle090.witnessCollar →
      (∀u∈(B.common),∀s∈main,‖physical F₀.modulus ⊤ (fun w : FreeRow=>w.val)
        F.profile F.upper F.widths F.external U u s‖  ≤  U^(F.widths s*(F.bin s+F.binWidth))) →
    let L := ∑s∈F.slots,F.widths s
    let Cmoment := max 1 (Cscale*((1+2*((mWindow+xi)*Real.log U))*
      (Cfourier*Csource*QuadraticInitialBound.diagonalControl radialMajorant*
        (1+B.height)^degree*(1+(2*Real.pi*allowance+(3*i : ℕ)*T))^(2*Jw+1))+1))
    let fee := (2*a-1)*(B.p)*decrement+F.binWidth*L+(2*a-1)*F.mesh/2+ε+((B.loss)+epsilon+loss)/2
    (∑u∈commonIndices F.rows (B.common),‖((Y:ℂ)^(-(1/2:ℂ))*(∑' e,A u e*(N u e:ℂ)^(-(1/2:ℂ))*
        (if Active u e then polynomial (rowCharacter F₀.S F₀.exclusions.prime u.val) false F₀.W (Y/N u e) 0 0 else 0)))*
        F.physicalProduct main u.val‖)  ≤  Y^(-(1/2:ℝ))*(Cmass*U^massEps*(∏k : J,(Z^(D₀.length k.val))^(-(4/25:ℝ))))*(max 1 (B.coefficient K))*Cmoment*
      U^((2*a-1)*(B.p)*(L-cap/2)+(3*(B.R)+1)/4-
        (2*a-1)*((B.p)*((PacketJoinE49.Return.line.g1)*F.m-(PacketJoinE49.Return.line.g0)/2+QRH.Cycle090.sourceGain F.m)+(B.penalty lo hi Mbound)/2-(B.p)*QRH.Cycle090.witnessCollar/2)+
        fee-(2*a-1)*(1-(B.p))*v/2) := by
  classical
  obtain ⟨mesh,hmesh,hbank⟩ := actual_middle_bank_packet hβ
  obtain ⟨sourceMesh,hsm,hsource⟩ := SourceWindowCompact.uniform_original_presentations hP1 hd hepsilon
  refine ⟨mesh,sourceMesh,hmesh,hsm,?_⟩
  intro D₀ F₀ hfine hstd heD htD κplain hk hk' hkβ J massEps he
    reverse tau xi loss b bPhi wmin htau hxi hloss hb hbPhi hPhi hwmin η
  obtain ⟨degree,controls,Csource,hC,hsource⟩ := hsource (Fin D₀.N) F₀ η bPhi hbPhi hPhi
    (1/200) wmin (by norm_num) hwmin
  obtain ⟨Jw,Cf,Cs,Cm,Umin,hCf,hCs,hCm,hbank⟩ := hbank D₀ F₀ hfine hstd heD htD κplain hk hk' hkβ
    J massEps he reverse controls F₀.W (fun _=>rfl) degree Csource epsilon tau xi loss b
    hC.le hepsilon.le htau hxi hloss hb
  obtain ⟨K,hbank⟩ := hbank η
  refine ⟨degree,controls,Csource,Jw,Cf,Cs,Cm,K,hC,hCf,hCs,hCm,?_⟩
  filter_upwards [hbank,hsource,(tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/200)).eventually
    (eventually_ge_atTop Umin)] with Z hbank hsource hUmin
  refine ⟨hbank.1,?_⟩
  intro B
  dsimp only
  let F := B.currentSlice.fiber
  intro hrev hT hall hheight hwit hslots hmesh hwidth hlower main nref hn0 hn1 hz0 hz1
    x z ha0 ha1 hx hz data
  intro Active Y mWindow v hY hm hMN hv hrow hactive hcombined hbox
    lo hi Mbound cap n0 hlo hkl hkh hM hcap href hupper
  let ηW := sourceMomentBase F₀.modulus ⊤ le_top F₀.S F₀.exclusions.prime η B.currentSlice.label
  have hdata : F.rowData=momentData ηW := source_fiber_data le_top F₀.S F₀.exclusions.prime η
    B.current.batch B.current.data B.currentSlice.bin B.currentSlice.label B.currentSlice.left
    B.currentSlice.right B.currentSlice.nonempty
  have hprofile (s : Fin D₀.N) (_hs : s∈F.slots) : F.profile s=F₀.W := by
    change B.current.batch.profile s=F₀.W
    rw [B.current.profile]
    funext x
    exact (F₀.complex_eq x).symm
  have hupp (s : Fin D₀.N) (_hs : s∈F.slots) : F.upper s=2 := congrFun B.current.upper s
  have hreal (s : Fin D₀.N) (_hs : s∈F.slots) : (F.external s).re=17/50 := B.current.real s
  have hq := RawTicket.true_source_quota ⟨hn0,hn1⟩ ⟨hz0,hz1⟩ hd
  obtain ⟨P,hPN,hPY,hPl,hdegree,hPC,heps,hPh⟩ := hsource.2 B.d B.d_min nref F.m
    (QRH.Cycle090.sourceWidth nref F.m-decrement) hn0 hn1 hz0 hz1 hq.1 (le_max_right _ _)
    B.currentSlice.label F hlower hmesh hwidth hprofile hupp hreal B.height B.height_nonneg
    (fun s _=>B.current_height s)
  have hlarge : Umin ≤ B.baseScale := hUmin.trans
    (Real.rpow_le_rpow_of_exponent_le hbank.1.le B.d_min)
  have hUp : 1<B.baseScale := B.baseScale_gt_one hbank.1
  have hXY : length B.baseScale (B.baseScale^F.m) ≤ P.seed.Y := by
    rw [hPY]
    unfold length
    rw [max_eq_right (Real.one_le_rpow hUp.le (by norm_num [Mixed.widthLo] at hz0;linarith)),
      Real.logb_rpow (zero_lt_one.trans hUp) (ne_of_gt hUp)]
  have hn : 0 ≤ P.seed.N := by rw [hPN];norm_num [RawTicket.nLo] at hn0;linarith
  have hPlL : P.seed.l ≤ ∑s∈F.slots,F.widths s := by rw [hPl];exact hq.2.2.trans F.supply
  have hquota : QRH.Cycle090.sourceWidth nref F.m-decrement ≤ P.seed.l := hPl.ge
  have hh := hbank.2 B hlarge ηW hrev hdata P hdegree hPC heps (by linarith [B.a_min]) hT hall hn hXY
    (hPh ▸ hheight) hwit hslots main (hPl ▸ hq.1) hPlL x z ha0 ha1 hx hz data
    Active Y mWindow v hY hm (hPN ▸ hMN) hv hrow hactive hcombined hbox
    lo hi Mbound cap n0 nref decrement hlo hkl hkh hM hcap href hquota hupper
  simpa only [hPh] using hh

#print axioms earlier_P1_middle_bank_packet
end
end QRH.Cycle092.MixedMiddleReturn
