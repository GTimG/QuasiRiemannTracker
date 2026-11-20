/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Earlier actual PairAt -> genuine witness Fourier columns -> original Y/N
numerator. The full P15 max-one dilation divisor occurs EXACTLY once. -/
import Candidate.C092.transport.MixedPacketScaleMoving

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

/-- Keep the TRUE lower edge of the complete-label dilation. The
normalizing divisor is present exactly once, and its box saving is retained. -/
theorem dilated_choice_second {Slot : Type} [Fintype Slot] [DecidableEq Slot]
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
      (N : F.rows→ℝ) (Active : F.rows→Prop) (Y m rho v : ℝ),
      0<Y → (∀u,Active u → 0<N u ∧ N u  ≤  b*Y) → 0  ≤  m → m+xi  ≤  D.N → 0 ≤ rho → 0 ≤ v →
      (∀u,Active u → (data u).combinedConductor   ≤   (fixedConductorConstant S:ℝ)*U^m*(Y/N u)) →
    (∀u,Active u → U^v ≤ max 1
      ((data u).combinedConductor/((fixedConductorConstant S:ℝ)*rowNorm u.val)*N u)) →
    let dilation := fun u : F.rows=>max 1
      ((data u).combinedConductor/((fixedConductorConstant S:ℝ)*rowNorm u.val)*N u)^rho
    (∑u : F.rows,‖if Active u then (polynomial (rowCharacter S hS u.val) false G (Y/N u) 0 0 /
        (dilation u:ℂ))*fiberPlain F u.val*(∏k∈D.selected,D.mark k u.val) else 0‖^2)   ≤  
      U^(-2*rho*v)*(Cscale*(U^loss*(1+2*((m+xi)*Real.log U))*
        (Cfourier*(Csource*QuadraticInitialBound.diagonalControl radialMajorant*
          (1+D.height)^degree*U^(1+epsilon))*
          (1+(2*Real.pi*allowance+(3*i : ℕ)*T))^(2*Jw+1))+1)) := by
  classical
  obtain ⟨Jw,Cf,Cs,hCf,hCs,hmove⟩ := moving_scale_second (Slot:=Slot) reverse controls
    S hS hbad G degree Csource epsilon tau xi loss b hCsource hepsilon htau hxi hloss hb
  refine ⟨Jw,Cf,Cs,hCf,hCs,?_⟩
  filter_upwards [hmove] with U hmove
  refine ⟨hmove.1,?_⟩
  intro M _ H hH Label a ε cutoff T allowance i F ηW hrev hdata
    D hdegree hC heps ha hT hall hN hXY hheight hwit data N Active Y m rho v
    hY hNs hm hMN hrho hv hcombined hbox
  dsimp only
  let K : ℝ := fixedConductorConstant S
  have hK : 0<K := by dsimp [K];exact_mod_cast fixedConductorConstant_pos S hS
  have hup : 0<U := zero_lt_one.trans hmove.1
  let X (u : F.rows) := max (1/b) ((data u).combinedConductor/(K*U^m))
  have hX (u : F.rows) : 0<X u := (div_pos zero_lt_one hb).trans_le (le_max_left _ _)
  let Neff (u : F.rows) := if Active u then N u else Y/X u
  let dil (u : F.rows) := max 1
    ((data u).combinedConductor/((fixedConductorConstant S:ℝ)*rowNorm u.val)*N u)^rho
  have hdil (u : F.rows) : 0<dil u :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le (le_max_left _ _)) _
  let scalar := U^(rho*v)
  have hspos : 0<scalar := Real.rpow_pos_of_pos hup _
  have hsdil (u : F.rows) (hu : Active u) : scalar ≤ dil u := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hup.le v) (hbox u hu) hrho
    rw [←Real.rpow_mul hup.le] at h
    simpa only [scalar,dil,mul_comm] using h
  let mask (u : F.rows) : ℂ := if Active u then (scalar/dil u:ℝ) else 0
  have hmask (u : F.rows) : ‖mask u‖ ≤ 1 := by
    dsimp only [mask]
    split
    · rw [Complex.norm_real,Real.norm_of_nonneg (div_nonneg hspos.le (hdil u).le)]
      exact (div_le_one (hdil u)).mpr (hsdil u ‹Active u›)
    · norm_num
  have hNeff (u : F.rows) : 0<Neff u ∧ Neff u ≤ b*Y := by
    dsimp only [Neff]
    split
    · exact hNs u ‹Active u›
    · refine ⟨div_pos hY (hX u),(div_le_iff₀ (hX u)).mpr ?_⟩
      have hbx : 1 ≤ b*X u := by
        have hh : 1 ≤ X u*b := (div_le_iff₀ hb).mp (show 1/b ≤ X u from le_max_left _ _)
        simpa only [mul_comm] using hh
      nlinarith only [mul_le_mul_of_nonneg_right hbx hY.le]
  have hc (u : F.rows) : (data u).combinedConductor ≤ (fixedConductorConstant S:ℝ)*U^m*(Y/Neff u) := by
    dsimp only [Neff]
    split
    · exact hcombined u ‹Active u›
    · rw [div_div_cancel₀ hY.ne']
      have hp : 0<K*U^m := mul_pos hK (Real.rpow_pos_of_pos hup _)
      have hh : (data u).combinedConductor ≤ X u*(K*U^m) :=
        (div_le_iff₀ hp).mp (show (data u).combinedConductor/(K*U^m) ≤ X u from le_max_right _ _)
      simpa only [K,mul_comm,mul_left_comm,mul_assoc] using hh
  have hh := hmove.2 hH F ηW hrev hdata D hdegree hC heps ha hT hall hN hXY
    hheight hwit data Neff mask Y m 0 hmask hY hNeff hm hMN le_rfl hc
  let value (u : F.rows) : ℂ := if Active u then
    (polynomial (rowCharacter S hS u.val) false G (Y/N u) 0 0/(dil u:ℂ))*
      fiberPlain F u.val*(∏k∈D.selected,D.mark k u.val) else 0
  have heq (u : F.rows) :
    (polynomial (rowCharacter S hS u.val) false G (Y/Neff u) 0 0 /
        ((max 1 ((data u).combinedConductor/((fixedConductorConstant S:ℝ)*rowNorm u.val)*Neff u)^(0:ℝ):ℝ):ℂ))*
      fiberPlain F u.val*(∏k∈D.selected,D.mark k u.val)*mask u = (scalar:ℂ)*value u := by
    dsimp only [value,Neff,mask]
    by_cases hu : Active u
    · simp only [hu,ite_true,Real.rpow_zero,Complex.ofReal_one,div_one,Complex.ofReal_div]
      ring
    · simp only [hu,ite_false,mul_zero]
  have hsumeq : (∑u : F.rows,‖(polynomial (rowCharacter S hS u.val) false G (Y/Neff u) 0 0 /
        ((max 1 ((data u).combinedConductor/((fixedConductorConstant S:ℝ)*rowNorm u.val)*Neff u)^(0:ℝ):ℝ):ℂ))*
      fiberPlain F u.val*(∏k∈D.selected,D.mark k u.val)*mask u‖^2) =
      scalar^2*∑u : F.rows,‖value u‖^2 := by
    simp_rw [heq,norm_mul,Complex.norm_real,Real.norm_of_nonneg hspos.le,mul_pow]
    exact (Finset.mul_sum _ _ _).symm
  have hh' := hsumeq.symm.le.trans hh
  have hcan : U^(-2*rho*v)*scalar^2=1 := by
    dsimp [scalar]
    rw [←Real.rpow_natCast,←Real.rpow_mul hup.le,←Real.rpow_add hup]
    convert Real.rpow_zero U using 1
    congr 1
    ring
  have h := mul_le_mul_of_nonneg_left hh' (Real.rpow_nonneg hup.le (-2*rho*v))
  rw [←mul_assoc,hcan,one_mul] at h
  exact h

#print axioms dilated_choice_second
end
end QRH.Cycle092.MixedMiddleReturn
