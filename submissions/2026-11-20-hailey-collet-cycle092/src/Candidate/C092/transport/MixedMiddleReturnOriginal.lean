/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Earlier actual PairAt -> genuine witness Fourier columns -> original Y/N
numerator. The full P15 max-one dilation divisor occurs EXACTLY once. -/
import Candidate.C092.transport.MixedMiddleReturnActualMass



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
/-- Complete original label coefficients and full P15 mass on a genuine
marked fiber. The active tuple slice may be the exact true-dilation box. -/
theorem saturated_original_packet_return (D₀ : BaselineData) (F₀ : BaselineSourceData D₀)
    (J : Finset (Fin D₀.N)) (massEps : ℝ) (he : 0 < massEps)
    (reverse : Bool) (controls : Finset (ℕ×ℕ))
    (G : 𝓢(ℝ,ℂ)) (hG : ∀x,G x=F₀.W x) (degree : ℕ) (Csource epsilon tau xi loss b : ℝ)
    (hCsource : 0   ≤   Csource) (hepsilon : 0   ≤   epsilon) (htau : 0   ≤   tau)
    (hxi : 0<xi) (hloss : 0<loss) (hb : 0<b) :
    ∃ Jw : ℕ,∃ Cfourier Cscale Cmass : ℝ,0<Cfourier ∧ 0<Cscale ∧ 0<Cmass ∧
    ∀ᶠ U : ℝ in atTop,1<U ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,0<Z ∧
    ∀{M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
      (hH : RayOrthogonality.globalUnits M   ≤   H)
      {Label : Type} {a ε cutoff T allowance : ℝ} {i : ℕ}
      (F : Fiber M H Label (Fin D₀.N) U a ε cutoff T allowance i) (ηW : Character),
      F.reverse=reverse → F.rowData=momentData ηW →
    ∀P : WholePresentation M H hH F₀.S F₀.exclusions.prime F ηW controls,
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
    (∑u∈commonIndices F.rows common,‖((Y:ℂ)^(-(1/2:ℂ))*(∑' e,A u e*(N u e:ℂ)^(-(1/2:ℂ))*
        (if Active u e then polynomial (rowCharacter F₀.S F₀.exclusions.prime u.val) false F₀.W (Y/N u e) 0 0 else 0)))*
        F.physicalProduct main u.val‖) ≤ Y^(-(1/2:ℝ))*(Cmass*U^massEps*(∏k : J,(Z^(D₀.length k.val))^(-(4/25:ℝ))))*Ccount*Cmoment*
      U^((2*a-1)*p*(L-cap/2)+(3*R+1)/4-
        (2*a-1)*(p*(g₁*F.m-g₀/2+QRH.Cycle090.sourceGain F.m)+pen/2-p*QRH.Cycle090.witnessCollar/2)+
        fee-(2*a-1)*(1-p)*v/2) := by
  classical
  obtain ⟨Jw,Cf,Cs,hCf,hCs,hpacket⟩ := saturated_packet_return (Slot:=Fin D₀.N) reverse controls
    F₀.S F₀.exclusions.prime F₀.exclusions.bad G degree Csource epsilon tau xi loss b
    hCsource hepsilon htau hxi hloss hb
  obtain ⟨Cm,hCm,hmass⟩ := original_packet_mass D₀ F₀ J massEps he
  refine ⟨Jw,Cf,Cs,Cm,hCf,hCs,hCm,?_⟩
  filter_upwards [hpacket] with U hpacket
  refine ⟨hpacket.1,?_⟩
  intro η
  filter_upwards [hmass η,eventually_gt_atTop (0:ℝ)] with Z hmass hZ
  refine ⟨hZ,?_⟩
  intro M _ H hH Label a ε cutoff T allowance i F ηW hrev hdata
    P hdegree hC heps ha hT hall hN hXY hheight hwit hslots main hl hlL
    x z ha0 ha1 hx hz data
  dsimp only
  intro Active Y mWindow v hY hm hMN hv hrow hactive hcombined hbox
    common hcommon R pen mBase countLoss p cap n0 nref decrement g₀ g₁ Ccount
    hc hp hp' hq hR hcap href hquota hcount hupper
  let Index := fun u : F.rows=>LabelPacketIndex F₀.S u.val (fun k : J=>sourcePrimePool F₀ Z k.val)
  let A := fun u : F.rows=>labelPacketCoefficient F₀.S F₀.exclusions η u.val
      (fun k : J=>sourcePrimePool F₀ Z k.val) (fun k=>source_prime_pool_outside F₀ Z k.val)
      (fun k P=>physicalSlotWeight P.val F₀.W (Z^(D₀.length k.val)) z) x z
  let N := fun (u : F.rows) (e : Index u)=>(labelPacketScale F₀.S u.val (fun k : J=>sourcePrimePool F₀ Z k.val) e:ℝ)
  let base : ∀u,Index u := fun u=>labelPacketBase F₀.S u.val _
    (fun k=>⟨(hmass.1 k.val).choose,(hmass.1 k.val).choose_spec⟩)
  have hNs (u : F.rows) (e : Index u) : 0<N u e :=
    zero_lt_one.trans_le (by exact_mod_cast labelPacketScale_one_le F₀.S u.val _ e)
  obtain ⟨hMass,hms⟩ := hmass.2 U F.rows data a x z (by linarith [hpacket.1]) hrow ha0 ha1 hx hz
  have hs (u : F.rows) : Summable (fun e=>‖A u e‖*(N u e)^(-(1/2:ℝ))*max 1
      ((data u).combinedConductor/((fixedConductorConstant F₀.S:ℝ)*rowNorm u.val)*N u e)^((2*a-1)/2)) := (hms u).1
  have hm' (u : F.rows) := (hms u).2
  have hh := hpacket.2 hH F ηW hrev hdata P hdegree hC heps ha hT hall hN hXY hheight hwit hslots
    main hl hlL data Index base A N Active Y mWindow v _ hY hNs hm hMN hv hMass hactive hcombined hbox
    hs hm' common hcommon R pen mBase countLoss p cap n0 nref decrement g₀ g₁ Ccount
    hc hp hp' hq hR hcap href hquota hcount hupper
  have hn : ‖(Y:ℂ)^(-(1/2:ℂ))‖=Y^(-(1/2:ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY];norm_num
  have heq : G=F₀.W := SchwartzMap.ext hG
  simp_rw [heq] at hh
  calc
    _ = Y^(-(1/2:ℝ))*(∑u∈commonIndices F.rows common,
      ‖(∑'e,A u e*(N u e:ℂ)^(-(1/2:ℂ))*(if Active u e then
        polynomial (rowCharacter F₀.S F₀.exclusions.prime u.val) false F₀.W (Y/N u e) 0 0 else 0))*
        F.physicalProduct main u.val‖) := by
      simp_rw [mul_assoc,norm_mul,hn]
      simp only [←Finset.mul_sum]
      rfl
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hY.le (-(1/2:ℝ))) using 1 <;> ring

#print axioms saturated_original_packet_return
end
end QRH.Cycle092.MixedMiddleReturn
