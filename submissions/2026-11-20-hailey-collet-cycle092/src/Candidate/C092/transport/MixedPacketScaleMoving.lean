/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Earlier actual PairAt -> genuine witness Fourier columns -> original Y/N
numerator. The full P15 max-one dilation divisor occurs EXACTLY once. -/
import Candidate.C092.transport.MixedPacketScaleOuter

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

lemma norm_le_power_of_square {z : ℂ} {A U q : ℝ}
    (_hA : 0 ≤ A) (hU : 1 ≤ U) (hq : 0 ≤ q) (h : ‖z‖^2  ≤  A*U^q) :
    ‖z‖  ≤  (A+1)*U^q := by
  have hp : 1 ≤ U^q := Real.one_le_rpow hU hq
  have hz : ‖z‖  ≤  ‖z‖^2+1 := by nlinarith only [sq_nonneg (‖z‖-1/2)]
  nlinarith only [hz,h,hp]

/-- No moving-source estimate is assumed. The only analytic source stored
in D is an actual earlier PairAt, with native keeps/marks. The multiplier's
outer bound is also derived from that PairAt using the fixed unit test. -/
theorem moving_scale_second {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (reverse : Bool) (controls : Finset (ℕ×ℕ))
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S)
    (G : 𝓢(ℝ,ℂ)) (degree : ℕ) (Csource epsilon tau xi loss b : ℝ)
    (hCsource : 0 ≤ Csource) (hepsilon : 0 ≤ epsilon) (htau : 0 ≤ tau)
    (hxi : 0<xi) (hloss : 0<loss) (hb : 0<b) :
    ∃ Jw : ℕ,∃ Cfourier Cscale : ℝ,0<Cfourier ∧ 0<Cscale ∧
    ∀ᶠ U : ℝ in atTop,1<U ∧
    ∀{M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
      (hH : RayOrthogonality.globalUnits M ≤ H)
      {Label : Type} {a ε cutoff T allowance : ℝ} {i : ℕ}
      (F : Fiber M H Label Slot U a ε cutoff T allowance i) (ηW : Character),
      F.reverse=reverse → F.rowData=momentData ηW →
    ∀D : EarlierPair M H hH S hS F ηW controls,
      D.degree=degree → D.C=Csource → D.epsilon=epsilon →
      0 ≤ a → 0 ≤ T → 0 ≤ allowance → 0 ≤ D.N → length U (U^F.m) ≤ D.Y →
      1+D.height ≤ U^tau → 1+(2*Real.pi*allowance+(3*i : ℕ)*T) ≤ U^tau →
    ∀ (data : ∀u : F.rows,PhysicalReflectionData S hS u.val)
      (N : F.rows→ℝ) (mask : F.rows→ℂ) (Y m rho : ℝ),
      (∀u,‖mask u‖ ≤ 1) →
      0<Y → (∀u,0<N u ∧ N u ≤ b*Y) → 0 ≤ m → m+xi ≤ D.N → 0 ≤ rho →
      (∀u,(data u).combinedConductor  ≤  (fixedConductorConstant S:ℝ)*U^m*(Y/N u)) →
    let dilation := fun u : F.rows=>max 1
      ((data u).combinedConductor/((fixedConductorConstant S:ℝ)*rowNorm u.val)*N u)^rho
    (∑u : F.rows,‖(polynomial (rowCharacter S hS u.val) false G (Y/N u) 0 0 /
        (dilation u:ℂ))*fiberPlain F u.val*(∏k∈D.selected,D.mark k u.val)*mask u‖^2)  ≤ 
      Cscale*(U^loss*(1+2*((m+xi)*Real.log U))*
        (Cfourier*(Csource*QuadraticInitialBound.diagonalControl radialMajorant*
          (1+D.height)^degree*U^(1+epsilon))*
          (1+(2*Real.pi*allowance+(3*i : ℕ)*T))^(2*Jw+1))+1) := by
  obtain ⟨Jf,Jw,Cf,hCf,hfourier⟩ := earlier_pair_fourier (Slot:=Slot) reverse controls
  obtain ⟨Ju,Cu,hCu,houter⟩ := witness_outer (Slot:=Slot) reverse controls
  let A := Cu*Csource*QuadraticInitialBound.diagonalControl radialMajorant
  have hA : 0 ≤ A := by
    have hd := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
    dsimp [A];positivity
  let q := 1+epsilon+tau*((degree:ℝ)+(2*Ju+1:ℕ))
  have hq : 0 ≤ q := by dsimp [q];positivity
  obtain ⟨Cs,hCs,hscale⟩ := MixedScale.rowwise_scale_second S hS G Jf xi loss b q (A+1)
    hxi hloss hb (by linarith)
  refine ⟨Jw,Cf,Cs,hCf,hCs,?_⟩
  filter_upwards [hscale] with U hscale
  refine ⟨hscale.1,?_⟩
  intro M _ H hH Label a ε cutoff T allowance i F ηW hrev hdata
    D hdegree hC heps ha hT hall hN hXY hheight hwit data N mask Y m rho hmask hY hNs hm hMN hrho hcombined
  dsimp only
  have hup : 0<U := zero_lt_one.trans hscale.1
  let dil (u : F.rows) := max 1
    ((data u).combinedConductor/((fixedConductorConstant S:ℝ)*rowNorm u.val)*N u)^rho
  have hdil (u : F.rows) : 1 ≤ dil u := Real.one_le_rpow (le_max_left _ _) hrho
  have hdilpos (u : F.rows) : 0<dil u := zero_lt_one.trans_le (hdil u)
  let Praw (u : F.rows) := fiberPlain F u.val*∏k∈D.selected,D.mark k u.val
  let P (u : F.rows) := Praw u/(dil u:ℂ)*mask u
  have hPsmall (u : F.rows) : ‖P u‖ ≤ ‖Praw u‖ := by
    apply (le_of_eq (norm_mul _ _)).trans
    apply (mul_le_of_le_one_right (norm_nonneg _) (hmask u)).trans
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (hdilpos u).le]
    apply (div_le_iff₀ (hdilpos u)).mpr
    exact le_mul_of_one_le_right (norm_nonneg _) (hdil u)
  have hDH0 := D.height_nonneg
  have hdiag0 := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  have hPraw (u : F.rows) : ‖Praw u‖ ≤ (A+1)*U^q := by
    have hsq := houter hH S hS hbad F ηW hrev hdata D hscale.1 ha hT hall
      (by rw [hC];exact hCsource) hN hXY u.val u.property
    rw [hC,hdegree,heps] at hsq
    have hsq' : ‖Praw u‖^2  ≤  A*U^q := by
      apply hsq.trans
      calc
        _  ≤  Cu*(Csource*QuadraticInitialBound.diagonalControl radialMajorant*
            (U^tau)^degree*U^(1+epsilon))*(U^tau)^(2*Ju+1) := by
          gcongr
        _ = A*U^q := by
          have hd : (U^tau)^degree = U^(tau*(degree:ℝ)) := by
            rw [←Real.rpow_natCast,←Real.rpow_mul hup.le]
          have hw : (U^tau)^(2*Ju+1) = U^(tau*(2*Ju+1:ℕ)) := by
            rw [←Real.rpow_natCast,←Real.rpow_mul hup.le]
          rw [hd,hw]
          calc
            _ = A*((U^(tau*(degree:ℝ))*U^(1+epsilon))*U^(tau*(2*Ju+1:ℕ))) := by
              dsimp [A];ring
            _ = A*U^q := by
              rw [←Real.rpow_add hup,←Real.rpow_add hup]
              congr 2
              dsimp [q]
              ring
    exact norm_le_power_of_square hA hscale.1.le hq hsq'
  let E := Cf*(Csource*QuadraticInitialBound.diagonalControl radialMajorant*
    (1+D.height)^degree*U^(1+epsilon))*
      (1+(2*Real.pi*allowance+(3*i : ℕ)*T))^(2*Jw+1)
  have hE : 0 ≤ E := by
    have hd := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
    have hh := D.height_nonneg
    dsimp [E];positivity
  have hmoment (v : ℝ) (j : Fin 2) (x : ℝ) (hx : x∈Icc 0 ((m+xi)*Real.log U)) :
      (∑u : F.rows,‖polynomial (rowCharacter S hS u.val) false
        (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*P u‖^2)  ≤ 
      E*(1+‖v‖)^(2*Jf) := by
    have hlength : length U (Real.exp x) ≤ D.N := by
      rw [length,max_eq_right (Real.one_le_exp_iff.mpr hx.1),Real.logb,Real.log_exp]
      apply (div_le_iff₀ (Real.log_pos hscale.1)).mpr
      exact hx.2.trans (mul_le_mul_of_nonneg_right hMN (Real.log_pos hscale.1).le)
    have hfixed := hfourier hH S hS hbad F ηW hrev hdata D hscale.1 ha hT hall
      (by rw [hC];exact hCsource) hXY (Real.exp x) (Real.exp_pos _) hlength j v
    rw [hC,hdegree,heps] at hfixed
    calc
      _  ≤  ∑u : F.rows,‖polynomial (rowCharacter S hS u.val) false
          (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*Praw u‖^2 := by
        apply Finset.sum_le_sum
        intro u _
        simp only [norm_mul,mul_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hPsmall u) 2) (sq_nonneg _)
      _ = ∑u∈F.rows,‖polynomial (rowCharacter S hS u) false
          (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*
          fiberPlain F u*∏k∈D.selected,D.mark k u‖^2 := by
        simpa only [Praw,mul_assoc] using Finset.sum_coe_sort F.rows
          (fun u=>‖polynomial (rowCharacter S hS u) false
          (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*
          fiberPlain F u*∏k∈D.selected,D.mark k u‖^2)
      _  ≤  _ := hfixed
  have hh := hscale.2 F.rows (fun u hu=>F.row_norm u hu) data N P Y m E
    hY hNs hm hE hcombined (fun u=>(hPsmall u).trans (hPraw u)) hmoment
  have heq (u : F.rows) : (polynomial (rowCharacter S hS u.val) false G (Y/N u) 0 0 /
      (dil u:ℂ))*fiberPlain F u.val*(∏k∈D.selected,D.mark k u.val)*mask u =
      polynomial (rowCharacter S hS u.val) false G (Y/N u) 0 0*P u := by
    dsimp [P,Praw]
    ring
  apply le_trans (le_of_eq ?_) hh
  exact Finset.sum_congr rfl (fun u _=>congrArg (fun z : ℂ=>‖z‖^2) (heq u))

#print axioms moving_scale_second
end
end QRH.Cycle092.MixedPacketScale
