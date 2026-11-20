/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Earlier actual PairAt -> genuine witness Fourier columns -> original Y/N
numerator. The full P15 max-one dilation divisor occurs EXACTLY once. -/
import Candidate.C092.transport.MixedMiddleReturnBudget
import Candidate.C092.transport.MixedPacketWitnessOrdinary
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
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair QRH.Cycle092.WitnessRowSup
open QRH.Cycle092.MixedPacketScale QRH.Cycle092.MixedPacketWitness
local notation "O" => HeckeFamily.O

/-- Analytic assembly lemma: earlier native PairAt supplies the moving
complete tuple second moment, followed by restriction to the common bank rows
and actual ordinary Cauchy. Native bank-count assembly consumes its hcard. -/
theorem earlier_pair_packet_bound {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (reverse : Bool) (controls : Finset (ℕ×ℕ))
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S)
    (G : 𝓢(ℝ,ℂ)) (degree : ℕ) (Csource epsilon tau xi loss b : ℝ)
    (hCsource : 0  ≤  Csource) (hepsilon : 0  ≤  epsilon) (htau : 0  ≤  tau)
    (hxi : 0<xi) (hloss : 0<loss) (hb : 0<b) :
    ∃ Jw : ℕ,∃ Cfourier Cscale : ℝ,0<Cfourier ∧ 0<Cscale ∧
    ∀ᶠ U : ℝ in atTop,1<U ∧
    ∀{M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
      (hH : RayOrthogonality.globalUnits M  ≤  H)
      {Label : Type} {a ε cutoff T allowance : ℝ} {i : ℕ}
      (F : Fiber M H Label Slot U a ε cutoff T allowance i) (ηW : Character),
      F.reverse=reverse → F.rowData=momentData ηW →
    ∀D : EarlierPair M H hH S hS F ηW controls,
      D.degree=degree → D.C=Csource → D.epsilon=epsilon →
      0  ≤  a → 0  ≤  T → 0  ≤  allowance → 0  ≤  D.N → length U (U^F.m)  ≤  D.Y →
      1+D.height  ≤  U^tau → 1+(2*Real.pi*allowance+(3*i : ℕ)*T)  ≤  U^tau →
    ∀ (data : ∀u : F.rows,PhysicalReflectionData S hS u.val)
      (Index : F.rows→Type) (base : ∀u,Index u)
      (A : ∀u,Index u→ℂ) (N : ∀u,Index u→ℝ) (Active : ∀u,Index u→Prop)
      (Y m rho v Mass : ℝ),
      0<Y → (∀u e,0<N u e) → 0 ≤ m → m+xi ≤ D.N → 0 ≤ rho → 0 ≤ v → 0 ≤ Mass →
      (∀u e,Active u e → N u e ≤ b*Y) →
      (∀u e,Active u e → (data u).combinedConductor ≤
        (fixedConductorConstant S:ℝ)*U^m*(Y/N u e)) →
    (∀u e,Active u e → U^v ≤ max 1
      ((data u).combinedConductor/((fixedConductorConstant S:ℝ)*rowNorm u.val)*N u e)) →
    let L := fun u : F.rows=>(data u).combinedConductor/((fixedConductorConstant S:ℝ)*rowNorm u.val)
    (∀u,Summable (fun e=>‖A u e‖*(N u e)^(-(1/2:ℝ))*max 1 (L u*N u e)^rho)) →
    (∀u,(∑' e,‖A u e‖*(N u e)^(-(1/2:ℝ))*max 1 (L u*N u e)^rho) ≤ Mass) →
    ∀ (common : Finset FreeRow),common⊆F.rows →
    ∀ (full reciprocal : F.rows→ℂ) (R Gcard total inverse selectedLower Ccount : ℝ),
      1≤Ccount → 0<Mass →
      (common.card:ℝ)≤Ccount*U^(R-Gcard) →
      (∀u∈commonIndices F.rows common,U^selectedLower≤‖∏k∈D.selected,D.mark k u.val‖) →
      (∀u∈commonIndices F.rows common,‖full u‖≤U^total) →
      (∀u∈commonIndices F.rows common,‖reciprocal u‖≤U^inverse) →
    let Cmoment := max 1 (Cscale*((1+2*((m+xi)*Real.log U))*
      (Cfourier*Csource*QuadraticInitialBound.diagonalControl radialMajorant*
        (1+D.height)^degree*(1+(2*Real.pi*allowance+(3*i : ℕ)*T))^(2*Jw+1))+1))
    (∑u∈commonIndices F.rows common,‖(∑' e,A u e*(N u e:ℂ)^(-(1/2:ℂ))*
        (if Active u e then polynomial (rowCharacter S hS u.val) false G (Y/N u e) 0 0 else 0))*
        full u*reciprocal u‖) ≤ Mass*Ccount*Cmoment*
      U^(total+inverse-selectedLower-((2*a-1)*F.m-2*ε)/2+
        (R+1+(epsilon+loss-2*rho*v))/2-Gcard/2) := by
  classical
  obtain ⟨Jw,Cf,Cs,hCf,hCs,hpacket⟩ := dilated_full_tuple_second (Slot:=Slot) reverse controls
    S hS hbad G degree Csource epsilon tau xi loss b hCsource hepsilon htau hxi hloss hb
  refine ⟨Jw,Cf,Cs,hCf,hCs,?_⟩
  filter_upwards [hpacket] with U hpacket
  refine ⟨hpacket.1,?_⟩
  intro M _ H hH Label a ε cutoff T allowance i F ηW hrev hdata
    D hdegree hC heps ha hT hall hN hXY hheight hwit data Index base A N Active Y m rho v Mass
    hY hNs hm hMN hrho hv hMass hactive hcombined hbox
  dsimp only
  intro hs hmass common hcommon full reciprocal R Gcard total inverse selectedLower Ccount
    hc hMp hcount hselected hfull hinverse
  let packet (u : F.rows) := ∑' e,A u e*(N u e:ℂ)^(-(1/2:ℂ))*
    (if Active u e then polynomial (rowCharacter S hS u.val) false G (Y/N u e) 0 0 else 0)
  let B := Cf*Csource*QuadraticInitialBound.diagonalControl radialMajorant*
    (1+D.height)^degree*(1+(2*Real.pi*allowance+(3*i : ℕ)*T))^(2*Jw+1)
  let Cm := max 1 (Cs*((1+2*((m+xi)*Real.log U))*B+1))
  have hup : 0<U := zero_lt_one.trans hpacket.1
  have hd := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  have hDH := D.height_nonneg
  have hB : 0≤B := by dsimp [B];positivity
  have hlog := (Real.log_pos hpacket.1).le
  have hwindow : 0≤1+2*((m+xi)*Real.log U) := by positivity
  have he := hpacket.2 hH F ηW hrev hdata D hdegree hC heps ha hT hall hN hXY hheight hwit
    data Index base A N Active Y m rho v Mass hY hNs hm hMN hrho hv hMass hactive hcombined hbox hs hmass
  have henergy : (∑u∈commonIndices F.rows common,
      ‖packet u*fiberPlain F u.val*(∏k∈D.selected,D.mark k u.val)‖^2) ≤
      Mass^2*Cm*U^(1+(epsilon+loss-2*rho*v)) := by
    apply (common_energy F.rows common _).trans
    apply he.trans
    have hb := source_energy_power (U:=U) (A:=B) (Cs:=Cs)
      (window:=1+2*((m+xi)*Real.log U)) (epsilon:=epsilon) (loss:=loss) (d:=2*rho*v)
      hpacket.1 hB hCs.le hwindow hepsilon hloss.le
    have hb' := mul_le_mul_of_nonneg_left hb (sq_nonneg Mass)
    rw [show (-2*rho*v)=-(2*rho*v) by ring]
    convert hb' using 1 <;> dsimp [B,Cm] <;> ring
  have hcard : ((commonIndices F.rows common).card:ℝ)≤Ccount*U^(R-Gcard) := by
    rw [commonIndices_card F.rows common hcommon]
    exact hcount
  exact packet_second_cauchy (commonIndices F.rows common) packet
    (fun u=>fiberPlain F u.val) (fun u=>∏k∈D.selected,D.mark k u.val) full reciprocal
    U R Gcard total inverse ((2*a-1)*F.m-2*ε) selectedLower
    (epsilon+loss-2*rho*v) Ccount Cm Mass hup hc (le_max_left _ _) hMp hcard
    (fun u hu=>MixedPacketWitness.fiber_plain_lower F hpacket.1 u.val u.property)
    hselected hfull hinverse henergy

#print axioms earlier_pair_packet_bound
end
end QRH.Cycle092.MixedMiddleReturn
