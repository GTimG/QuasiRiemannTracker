/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Earlier actual PairAt -> genuine witness Fourier columns -> original Y/N
numerator. The full P15 max-one dilation divisor occurs EXACTLY once. -/
import Candidate.C092.transport.MixedMiddleReturnOriginal
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

/-- Genuine actual middle-bank packet. Its count and complete original P15
mass are proved internally; only the earlier P.1 presentation and physical
window/event guards remain inputs. -/
theorem actual_middle_bank_packet (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃mesh : ℝ→ℝ,(∀t,0<t → 0 < mesh t) ∧
    ∀(D₀ : BaselineData) (F₀ : BaselineSourceData D₀),
      (∀s,D₀.length s ≤ mesh D₀.t/200) →
      (∀s,D₀.length s ≤ Cycle25.sourceMesh D₀.t/200) →
      D₀.ε ≤ 1/10000000 → D₀.t ≤ 1/10000000 →
    ∀κplain : ℝ,7/10 ≤ κplain → κplain ≤ 3/4 → 2*HeckeZeroSupremum.beta-1 ≤ κplain →
    ∀(J : Finset (Fin D₀.N)) (massEps : ℝ),0 < massEps →
    ∀(reverse : Bool) (controls : Finset (ℕ×ℕ))
      (G : 𝓢(ℝ,ℂ)),(∀x,G x=F₀.W x) →
    ∀(degree : ℕ) (Csource epsilon tau xi loss b : ℝ),
      0 ≤ Csource → 0 ≤ epsilon → 0 ≤ tau → 0<xi → 0<loss → 0<b →
    ∃ Jw : ℕ,∃ Cfourier Cscale Cmass Umin : ℝ,0<Cfourier ∧ 0<Cscale ∧ 0<Cmass ∧
    ∀η : Character,∃K : MixedOffsetCount.CountConstants,∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀B : MixedOffsetCount.MiddleBank D₀.toMomentData F₀ η Z,Umin ≤ B.baseScale →
    let U := B.baseScale
    let a := B.a
    let ε := D₀.ε
    let T := B.T
    let allowance := B.allowance
    let i := B.i
    let F := B.currentSlice.fiber
    ∀ηW : Character,F.reverse=reverse → F.rowData=momentData ηW →
    ∀P : WholePresentation F₀.modulus ⊤ le_top F₀.S F₀.exclusions.prime F ηW controls,
      P.seed.degree=degree → P.seed.C=Csource → P.seed.epsilon=epsilon →
      1/2 ≤ a → 0 ≤ T → 0 ≤ allowance → 0 ≤ P.seed.N → length U (U^F.m) ≤ P.seed.Y →
      1+P.seed.height ≤ U^tau → 1+(2*Real.pi*allowance+(3*i : ℕ)*T) ≤ U^tau →
      F.slots=Finset.univ →
    ∀(main : Finset (Fin D₀.N)),0 ≤ P.seed.l → P.seed.l ≤ ∑s∈F.slots,F.widths s →
    ∀(x z : ℂ),51/100 ≤ a → a ≤ 7/8 → x.re=a+16*D₀.e → z.re=17/50 →
    ∀ (data : ∀u : F.rows,PhysicalReflectionData F₀.S F₀.exclusions.prime u.val),
    let Index := fun u : F.rows=>LabelPacketIndex F₀.S u.val (fun k : J=>sourcePrimePool F₀ Z k.val)
    let A := fun u : F.rows=>labelPacketCoefficient F₀.S F₀.exclusions η u.val
      (fun k : J=>sourcePrimePool F₀ Z k.val) (fun k=>source_prime_pool_outside F₀ Z k.val)
      (fun k P=>physicalSlotWeight P.val F₀.W (Z^(D₀.length k.val)) z) x z
    let N := fun (u : F.rows) (e : Index u)=>(labelPacketScale F₀.S u.val (fun k : J=>sourcePrimePool F₀ Z k.val) e:ℝ)
    ∀(Active : ∀u,Index u→Prop) (Y mWindow v : ℝ),
      0<Y → 0 ≤ mWindow → mWindow+xi ≤ P.seed.N → 0 ≤ v →
      (∀u∈F.rows,rowNorm u≤U) →
      (∀u e,Active u e → N u e ≤ b*Y) →
      (∀u e,Active u e → (data u).combinedConductor ≤ (fixedConductorConstant F₀.S:ℝ)*U^mWindow*(Y/N u e)) →
      (∀u e,Active u e → U^v ≤ max 1 ((data u).combinedConductor/
        ((fixedConductorConstant F₀.S:ℝ)*rowNorm u.val)*N u e)) →
    ∀(lo hi Mbound cap n0 nref decrement : ℝ),
      0 ≤ lo → lo ≤ B.k → B.k ≤ hi → B.m ≤ Mbound →
      cap ≤ n0-1/2 → nref ≤ 1-n0+v+QRH.Cycle090.witnessCollar →
      QRH.Cycle090.sourceWidth nref F.m-decrement ≤ P.seed.l →
      (∀u∈(B.common),∀s∈main,‖physical F₀.modulus ⊤ (fun w : FreeRow=>w.val)
        F.profile F.upper F.widths F.external U u s‖ ≤ U^(F.widths s*(F.bin s+F.binWidth))) →
    let L := ∑s∈F.slots,F.widths s
    let Cmoment := max 1 (Cscale*((1+2*((mWindow+xi)*Real.log U))*
      (Cfourier*Csource*QuadraticInitialBound.diagonalControl radialMajorant*
        (1+P.seed.height)^degree*(1+(2*Real.pi*allowance+(3*i : ℕ)*T))^(2*Jw+1))+1))
    let fee := (2*a-1)*(B.p)*decrement+F.binWidth*L+(2*a-1)*F.mesh/2+ε+((B.loss)+epsilon+loss)/2
    (∑u∈commonIndices F.rows (B.common),‖((Y:ℂ)^(-(1/2:ℂ))*(∑' e,A u e*(N u e:ℂ)^(-(1/2:ℂ))*
        (if Active u e then polynomial (rowCharacter F₀.S F₀.exclusions.prime u.val) false F₀.W (Y/N u e) 0 0 else 0)))*
        F.physicalProduct main u.val‖) ≤ Y^(-(1/2:ℝ))*(Cmass*U^massEps*(∏k : J,(Z^(D₀.length k.val))^(-(4/25:ℝ))))*(max 1 (B.coefficient K))*Cmoment*
      U^((2*a-1)*(B.p)*(L-cap/2)+(3*(B.R)+1)/4-
        (2*a-1)*((B.p)*((PacketJoinE49.Return.line.g1)*F.m-(PacketJoinE49.Return.line.g0)/2+QRH.Cycle090.sourceGain F.m)+(B.penalty lo hi Mbound)/2-(B.p)*QRH.Cycle090.witnessCollar/2)+
        fee-(2*a-1)*(1-(B.p))*v/2) := by
  classical
  obtain ⟨mesh,hmesh,hcount⟩ := MixedOffsetCount.actual_middle_bank_count hβ
  refine ⟨mesh,hmesh,?_⟩
  intro D₀ F₀ hfine hstd heD htD κplain hk hk' hkβ J massEps he
    reverse controls G hG degree Csource epsilon tau xi loss b hCsource hepsilon htau hxi hloss hb
  obtain ⟨Jw,Cf,Cs,hCf,hCs,hpacket⟩ := saturated_packet_return (Slot:=Fin D₀.N) reverse controls
    F₀.S F₀.exclusions.prime F₀.exclusions.bad G degree Csource epsilon tau xi loss b
    hCsource hepsilon htau hxi hloss hb
  obtain ⟨Umin,hUmin⟩ := eventually_atTop.mp hpacket
  obtain ⟨Cm,hCm,hmass⟩ := original_packet_mass D₀ F₀ J massEps he
  refine ⟨Jw,Cf,Cs,Cm,Umin,hCf,hCs,hCm,?_⟩
  intro η
  obtain ⟨K,hcount⟩ := hcount D₀.toMomentData F₀ hfine hstd heD htD κplain hk hk' hkβ η
  refine ⟨K,?_⟩
  filter_upwards [hcount,hmass η] with Z hcount hmass
  refine ⟨hcount.1,?_⟩
  intro B hBU
  dsimp only
  let F := B.currentSlice.fiber
  have hpacket := hUmin B.baseScale hBU
  intro ηW hrev hdata P hdegree hC heps ha hT hall hN hXY hheight hwit hslots main hl hlL
    x z ha0 ha1 hx hz data
  intro Active Y mWindow v hY hm hMN hv hrow hactive hcombined hbox
    lo hi Mbound cap n0 nref decrement hlo hkl hkh hM hcap href hquota hupper
  let Index := fun u : F.rows=>LabelPacketIndex F₀.S u.val (fun k : J=>sourcePrimePool F₀ Z k.val)
  let A := fun u : F.rows=>labelPacketCoefficient F₀.S F₀.exclusions η u.val
      (fun k : J=>sourcePrimePool F₀ Z k.val) (fun k=>source_prime_pool_outside F₀ Z k.val)
      (fun k P=>physicalSlotWeight P.val F₀.W (Z^(D₀.length k.val)) z) x z
  let N := fun (u : F.rows) (e : Index u)=>(labelPacketScale F₀.S u.val (fun k : J=>sourcePrimePool F₀ Z k.val) e:ℝ)
  let base : ∀u,Index u := fun u=>labelPacketBase F₀.S u.val _
    (fun k=>⟨(hmass.1 k.val).choose,(hmass.1 k.val).choose_spec⟩)
  have hNs (u : F.rows) (e : Index u) : 0<N u e :=
    zero_lt_one.trans_le (by exact_mod_cast labelPacketScale_one_le F₀.S u.val _ e)
  obtain ⟨hMass,hms⟩ := hmass.2 B.baseScale F.rows data B.a x z (by linarith [hpacket.1]) hrow ha0 ha1 hx hz
  have hs (u : F.rows) : Summable (fun e=>‖A u e‖*(N u e)^(-(1/2:ℝ))*max 1
      ((data u).combinedConductor/((fixedConductorConstant F₀.S:ℝ)*rowNorm u.val)*N u e)^((2*B.a-1)/2)) := (hms u).1
  have hcard := B.penalty_count_with_max K (hcount.2 B) (by linarith [hpacket.1]) lo hi Mbound hlo hkl hkh hM
  have hp : 0 ≤ B.p := (show (7/16:ℝ) ≤ B.p from B.available.2.1).trans' (by norm_num)
  have hp' : B.p ≤ 1 := B.available.2.2.trans (by norm_num)
  have hR := B.R_expanded
  have hh := hpacket.2 le_top F ηW hrev hdata P hdegree hC heps ha hT hall hN hXY hheight hwit hslots
    main hl hlL data Index base A N Active Y mWindow v _ hY hNs hm hMN hv hMass hactive hcombined hbox
    hs (fun u=>(hms u).2) B.common B.common_current B.R (B.penalty lo hi Mbound) B.m B.loss B.p cap n0 nref decrement
    PacketJoinE49.Return.line.g0 PacketJoinE49.Return.line.g1 (max 1 (B.coefficient K))
    (le_max_left _ _) hp hp' B.full_mean hR hcap href hquota hcard hupper
  have hn : ‖(Y:ℂ)^(-(1/2:ℂ))‖=Y^(-(1/2:ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY];norm_num
  have heq : G=F₀.W := SchwartzMap.ext hG
  simp_rw [heq] at hh
  calc
    _ = Y^(-(1/2:ℝ))*(∑u∈commonIndices F.rows B.common,
      ‖(∑'e,A u e*(N u e:ℂ)^(-(1/2:ℂ))*(if Active u e then
        polynomial (rowCharacter F₀.S F₀.exclusions.prime u.val) false F₀.W (Y/N u e) 0 0 else 0))*
        F.physicalProduct main u.val‖) := by
      simp_rw [mul_assoc,norm_mul,hn]
      simp only [←Finset.mul_sum]
      rfl
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hY.le (-(1/2:ℝ))) using 1 <;> ring

#print axioms actual_middle_bank_packet
end
end QRH.Cycle092.MixedMiddleReturn
