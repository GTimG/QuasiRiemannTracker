/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Earlier actual PairAt -> genuine witness Fourier columns -> original Y/N
numerator. The full P15 max-one dilation divisor occurs EXACTLY once. -/
import Candidate.C092.transport.MixedPacketScaleActive
import Candidate.C092.transport.MixedPacketWitnessMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.MixedPacketScale
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
open QRH.Cycle092.MixedPacketWitness
local notation "O" => HeckeFamily.O

/-- The complete tuple coefficient series is paid by P15 only once.
Every independent tuple-choice moment is proved from the earlier PairAt,
not supplied as a moving-source estimate. Active supports may depend on
both row and tuple. The original witness and marks are retained. -/
theorem full_tuple_second {Slot : Type} [Fintype Slot] [DecidableEq Slot]
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
      (Y m rho Mass : ℝ),
      0<Y → (∀u e,0<N u e) → 0 ≤ m → m+xi ≤ D.N → 0 ≤ rho → 0 ≤ Mass →
      (∀u e,Active u e → N u e ≤ b*Y) →
      (∀u e,Active u e → (data u).combinedConductor ≤
        (fixedConductorConstant S:ℝ)*U^m*(Y/N u e)) →
    let L := fun u : F.rows=>(data u).combinedConductor/((fixedConductorConstant S:ℝ)*rowNorm u.val)
    (∀u,Summable (fun e=>‖A u e‖*(N u e)^(-(1/2:ℝ))*max 1 (L u*N u e)^rho)) →
    (∀u,(∑' e,‖A u e‖*(N u e)^(-(1/2:ℝ))*max 1 (L u*N u e)^rho) ≤ Mass) →
    (∑u : F.rows,‖(∑' e,A u e*(N u e:ℂ)^(-(1/2:ℂ))*
        (if Active u e then polynomial (rowCharacter S hS u.val) false G (Y/N u e) 0 0 else 0))*
      fiberPlain F u.val*(∏k∈D.selected,D.mark k u.val)‖^2) ≤ Mass^2*(
      Cscale*(U^loss*(1+2*((m+xi)*Real.log U))*
        (Cfourier*(Csource*QuadraticInitialBound.diagonalControl radialMajorant*
          (1+D.height)^degree*U^(1+epsilon))*
          (1+(2*Real.pi*allowance+(3*i : ℕ)*T))^(2*Jw+1))+1)) := by
  classical
  obtain ⟨Jw,Cf,Cs,hCf,hCs,hmove⟩ := moving_scale_active_second (Slot:=Slot) reverse controls
    S hS hbad G degree Csource epsilon tau xi loss b hCsource hepsilon htau hxi hloss hb
  refine ⟨Jw,Cf,Cs,hCf,hCs,?_⟩
  filter_upwards [hmove] with U hmove
  refine ⟨hmove.1,?_⟩
  intro M _ H hH Label a ε cutoff T allowance i F ηW hrev hdata
    D hdegree hC heps ha hT hall hN hXY hheight hwit data Index base A N Active Y m rho Mass
    hY hNs hm hMN hrho hMass hactive hcombined
  dsimp only
  intro hs hmass
  let L := fun u : F.rows=>(data u).combinedConductor/((fixedConductorConstant S:ℝ)*rowNorm u.val)
  let Sp (u : F.rows) (e : Index u) :=
    if Active u e then polynomial (rowCharacter S hS u.val) false G (Y/N u e) 0 0 else 0
  let E := Cs*(U^loss*(1+2*((m+xi)*Real.log U))*
    (Cf*(Csource*QuadraticInitialBound.diagonalControl radialMajorant*
      (1+D.height)^degree*U^(1+epsilon))*
      (1+(2*Real.pi*allowance+(3*i : ℕ)*T))^(2*Jw+1))+1)
  apply packet_second_selection base A Sp N hNs L rho
    (fun u=>fiberPlain F u.val) (fun u=>∏k∈D.selected,D.mark k u.val)
    Mass E hMass hs hmass
  intro e
  have hh := hmove.2 hH F ηW hrev hdata D hdegree hC heps ha hT hall hN hXY hheight hwit data
    (fun u=>N u (e u)) (fun u=>Active u (e u)) Y m rho hY
    (fun u hu=>⟨hNs u (e u),hactive u (e u) hu⟩) hm hMN hrho
    (fun u hu=>hcombined u (e u) hu)
  apply le_trans (le_of_eq ?_) hh
  apply Finset.sum_congr rfl
  intro u _
  dsimp only [Sp,L]
  by_cases hu : Active u (e u)
  · simp only [hu,ite_true]
  · simp only [hu,ite_false,zero_div,zero_mul,norm_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]

#print axioms full_tuple_second
end
end QRH.Cycle092.MixedPacketScale
