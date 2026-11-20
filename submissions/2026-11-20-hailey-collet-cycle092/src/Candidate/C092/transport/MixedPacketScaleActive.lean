/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Earlier actual PairAt -> genuine witness Fourier columns -> original Y/N
numerator. The full P15 max-one dilation divisor occurs EXACTLY once. -/
import Candidate.C092.transport.MixedPacketScaleMoving

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

/-- A tuple may activate an arbitrary subset of the same physical fiber.
Inactive rows use a harmless positive scale and zero mask; witnesses,
labels and marks remain the original ones on every active row. -/
theorem moving_scale_active_second {Slot : Type} [Fintype Slot] [DecidableEq Slot]
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
      (N : F.rows→ℝ) (Active : F.rows→Prop) (Y m rho : ℝ),
      0<Y → (∀u,Active u → 0<N u ∧ N u  ≤  b*Y) → 0  ≤  m → m+xi  ≤  D.N → 0  ≤  rho →
      (∀u,Active u → (data u).combinedConductor   ≤   (fixedConductorConstant S:ℝ)*U^m*(Y/N u)) →
    let dilation := fun u : F.rows=>max 1
      ((data u).combinedConductor/((fixedConductorConstant S:ℝ)*rowNorm u.val)*N u)^rho
    (∑u : F.rows,‖if Active u then (polynomial (rowCharacter S hS u.val) false G (Y/N u) 0 0 /
        (dilation u:ℂ))*fiberPlain F u.val*(∏k∈D.selected,D.mark k u.val) else 0‖^2)   ≤  
      Cscale*(U^loss*(1+2*((m+xi)*Real.log U))*
        (Cfourier*(Csource*QuadraticInitialBound.diagonalControl radialMajorant*
          (1+D.height)^degree*U^(1+epsilon))*
          (1+(2*Real.pi*allowance+(3*i : ℕ)*T))^(2*Jw+1))+1) := by
  classical
  obtain ⟨Jw,Cf,Cs,hCf,hCs,hmove⟩ := moving_scale_second (Slot:=Slot) reverse controls
    S hS hbad G degree Csource epsilon tau xi loss b hCsource hepsilon htau hxi hloss hb
  refine ⟨Jw,Cf,Cs,hCf,hCs,?_⟩
  filter_upwards [hmove] with U hmove
  refine ⟨hmove.1,?_⟩
  intro M _ H hH Label a ε cutoff T allowance i F ηW hrev hdata
    D hdegree hC heps ha hT hall hN hXY hheight hwit data N Active Y m rho
    hY hNs hm hMN hrho hcombined
  dsimp only
  let K : ℝ := fixedConductorConstant S
  have hK : 0<K := by dsimp [K];exact_mod_cast fixedConductorConstant_pos S hS
  have hup : 0<U := zero_lt_one.trans hmove.1
  let X (u : F.rows) := max (1/b) ((data u).combinedConductor/(K*U^m))
  have hX (u : F.rows) : 0<X u := (div_pos zero_lt_one hb).trans_le (le_max_left _ _)
  let Neff (u : F.rows) := if Active u then N u else Y/X u
  let mask (u : F.rows) : ℂ := if Active u then 1 else 0
  have hmask (u : F.rows) : ‖mask u‖  ≤  1 := by dsimp [mask];split <;> norm_num
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
    hheight hwit data Neff mask Y m rho hmask hY hNeff hm hMN hrho hc
  apply le_trans (le_of_eq ?_) hh
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : Active u
  · simp only [hu,ite_true,Neff,mask,mul_one]
  · simp only [hu,ite_false,Neff,mask,mul_zero,norm_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]

#print axioms moving_scale_active_second
end
end QRH.Cycle092.MixedPacketScale
