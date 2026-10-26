/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.RegionalAtState
import Candidate.Research.RecursiveAffine.ActualReachableHigh

set_option autoImplicit false
set_option maxHeartbeats 650000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open HeckeFamily CanonicalQuadraticSieve QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentAllocatedRayDictionary
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open Cycle63InitialMass Cycle153Reachable Cycle153RegionalState Cycle153SourceReturn

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable (hH : RayOrthogonality.globalUnits M ≤ H)
variable {C : SourceContext (α:=alpha) M H} {j : Fin 4}(N : ReachableNode C j)

/-- The exact source-wide LOW obligation left by the real AtState theorem
at this actual node. The whole-forest attainer must prove this predicate;
no energy or returned-count estimate is stored in the node itself. -/
def NativeNodeLowAt
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)
    (Cs : ℝ)(Sp : Finset alpha→Finset (ℕ×ℕ))(degreeLow : Finset alpha→ℕ)
    (Klow : Finset alpha→ℝ)(hT : 2<N.localBase^g.τ)
    (hbetaHi : HeckeZeroSupremum.beta ≤ 7/8)(EL : ℝ) : Prop := by
  letI : Cycle63.AffineLedger := N.ledger
  exact ∀(caps : GeometryAffineLowSourceGates (N.input hH) N.profiles Cs N.localBase)
    (hm : Matches M H hH (N.input hH) C.etaSeed
      (fun i=>C.theta i) (fun i=>C.originalWeight i/N.unit)
      (fun i=>C.sigma i) (fun i=>C.frequency i) C.W 2 N.localBase)
    (hrow : N.state.rowWidth ≤ 1)
    (hfit : N.state.rowWidth+Real.logb N.localBase ((N.input hH).η.modulus.absNorm:ℝ) ≤ 1+g.μ/16)
    (hwL : ∀i : N.slots,C.originalWeight i/N.unit ≤ Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))
    (hwr : ∀i : N.slots,(C.originalWeight i/N.unit)/31 ≤ 1)
    (hslots : Cycle63.AffineLedger.slotFloor ≤ ∑i,Real.logb N.localBase ((N.input hH).P i) ∧
      (∑i,Real.logb N.localBase ((N.input hH).P i)) ≤ Cycle63.AffineLedger.slotTop)
    (haff : length N.localBase (N.input hH).X₁+length N.localBase (N.input hH).X₂+
      Cycle63.AffineLedger.lam*(∑i,Real.logb N.localBase ((N.input hH).P i)) ≤ Cycle63.AffineLedger.B),
    RegionalLowSelectedAt M H hH C.W hbeta g 2
      (Cycle25.Energy.commonMesh 2 28 1 (g.μ/8)) Cs (fun _ _ _=>True)
      (fun _ _ _ _ _=>True) (Sp N.slots) (degreeLow N.slots) (Klow N.slots)
      C.etaSeed C.Q C.Q_le_M C.fixed_small N.localBase EL N.localBase_gt_one
      (N.input hH) N.profiles caps (fun i=>C.theta i) (fun i=>C.originalWeight i/N.unit)
      (fun i=>C.sigma i) (fun i=>C.frequency i) hm N.state.puncture 1 20 N.state.rowWidth
      N.state.puncture_ne_zero squarefree_one (by norm_num) N.state.puncture_bound
      N.state.row_nonneg hrow hfit trivial N.height C.slotMesh
      (fun i=>div_nonneg (C.originalWeight_nonneg i) N.unit_pos.le)
      hwL hwr C.slotMesh_pos.le N.weight_mesh (fun i=>C.sigma_fixed i)
      N.height_nonneg N.frequency_bound hT hbetaHi hslots haff

/-- Apply the genuine regional AtState theorem to the actual node input.
The same whole forest pays normalized LOW and, with the explicit factor
two from its genuine source-wide attainer, pays own HIGH. The raw
row-scale factor is retained until its exact cancellation against the
normalized returns; its remaining `+1` costs the old power. This is the
final energy field for a NodeOutput once the actual source-wide LOW
predicate and forest provenance have been constructed. -/
theorem actual_node_at_state_from_whole_forest
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)(hbetaHi : HeckeZeroSupremum.beta ≤ 7/8)
    (g : GeometryAffineLowSchedule)(epsilon : ℝ)(Psi : 𝓢(ℝ,ℂ))
    (SH : Finset (ℕ×ℕ))(dh degree : ℕ)(S : Finset (ℕ×ℕ))
    (Cenergy Chigh Cs : ℝ)(Sp : Finset alpha→Finset (ℕ×ℕ))
    (degreeLow : Finset alpha→ℕ)(Klow : Finset alpha→ℝ)
    (hT : 2<N.localBase^g.τ)(hCenergy : 0 ≤ Cenergy)(hChigh : 0 ≤ Chigh)
    (hAt : letI : Cycle63.AffineLedger := N.ledger
      RegionalAtState (α:=alpha) M H hH C.W C.W_smooth C.W_support hbeta hbetaHi
        g 2 20 C.slotMesh epsilon (by norm_num) Psi SH dh degree S Cenergy Chigh Cs
        Sp degreeLow Klow (by norm_num) C.slotMesh_pos.le C.etaSeed C.Q C.Q_le_M
        C.fixed_small N.localBase)
    (own : ReturnedPartAt M H hH (innerStage j.val).q (prefixDictionary (j.val+1))
      C.etaSeed N.localBase C.Bnorm C.Tz N.presentation.mult)
    (F : N.Family hH)(Kh Kreturn : ℝ)(hKh : 0 ≤ Kh)(hKreturn : 0 ≤ Kreturn)
    (hOwn : own.value ≤ 2*F.value) :
    letI : Cycle63.AffineLedger := N.ledger
    let amp := Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑i : N.slots,C.originalWeight i/N.unit)))
    let outer := N.state.rowWidth+3*g.δ-amp+epsilon
    3*g.δ ≤ amp →
    NativeNodeLowAt hH N hbeta g Cs Sp degreeLow Klow hT hbetaHi
      (Kreturn*N.localBase^(-outer)*F.value) →
    GeometryAffineHighGiven (α:=N.slots) M H hH g C.etaSeed C.Q C.Q_le_M C.fixed_small
      hbeta hbetaHi N.localBase N.localBase_gt_one hT (1/4) (9/4)
      (N.input hH) N.profiles N.state.puncture 1 N.state.rowWidth amp Psi
      (profile_zero_of_pos N.profiles (by norm_num) 0)
      (profile_zero_of_pos N.profiles (by norm_num) 1) SH dh N.height
      (Kh*(N.localBase^(-outer)*own.value+1)) →
    N.sourceEnergy hH ≤
      (Cenergy*(1+Chigh*(Kreturn+2*Kh)))*diagonalControl N.state.radial.profile*
        (N.profiles.control S)^2*(1+|N.t|+N.height)^degree*
        (N.localBase^(1+epsilon)+F.value) := by
  letI : Cycle63.AffineLedger := N.ledger
  intro amp outer hamp hlow hhigh
  have hZ : 0<N.localBase := zero_lt_one.trans N.localBase_gt_one
  have hF := F.value_nonneg hZ.le
  have hown0 := own.value_nonneg hZ.le
  have hEL : 0 ≤ Kreturn*N.localBase^(-outer)*F.value := by positivity
  have hEH : 0 ≤ Kh*(N.localBase^(-outer)*own.value+1) := by positivity
  have he := hAt N.localBase_gt_one hT N.slots (fun i=>C.theta i)
    (fun i=>C.originalWeight i/N.unit) (fun i=>C.sigma i) (fun i=>C.frequency i)
    (fun i=>C.sigma_fixed i) N.t N.height
    (fun i=>div_nonneg (C.originalWeight_nonneg i) N.unit_pos.le)
    N.weight_mesh N.height_nonneg N.frequency_bound N.state N.fixedModulus N.width_le_one
    N.profiles N.X1 N.X2 N.X1_pos N.X2_pos N.window N.overshoot
    (Kreturn*N.localBase^(-outer)*F.value) hEL hlow
    (Kh*(N.localBase^(-outer)*own.value+1)) hEH hhigh
  have hrow : N.state.rowWidth ≤ 1 := by
    have hw := N.width_le_one
    have hc := N.state.character_nonneg
    unfold NaturalState.width at hw
    linarith only [hw,hc]
  have houter : outer ≤ 1+epsilon := by dsimp only [outer];linarith only [hrow,hamp]
  have hpower := Real.rpow_le_rpow_of_exponent_le N.localBase_gt_one.le houter
  have hcancel : N.localBase^outer*N.localBase^(-outer)=(1:ℝ) := by
    rw [←Real.rpow_add hZ]
    simp only [add_neg_cancel,Real.rpow_zero]
  have hraw : N.localBase^outer*
      (Kreturn*N.localBase^(-outer)*F.value+Kh*(N.localBase^(-outer)*own.value+1))=
      Kreturn*F.value+Kh*own.value+Kh*N.localBase^outer := by
    calc
      _=(N.localBase^outer*N.localBase^(-outer))*(Kreturn*F.value+Kh*own.value)+Kh*N.localBase^outer := by ring
      _=_ := by rw [hcancel];ring
  have hbudget : N.localBase^(1+epsilon)+Chigh*N.localBase^outer*
      (Kreturn*N.localBase^(-outer)*F.value+Kh*(N.localBase^(-outer)*own.value+1)) ≤
      (1+Chigh*(Kreturn+2*Kh))*(N.localBase^(1+epsilon)+F.value) := by
    rw [show Chigh*N.localBase^outer*(Kreturn*N.localBase^(-outer)*F.value+
      Kh*(N.localBase^(-outer)*own.value+1))=
      Chigh*(N.localBase^outer*(Kreturn*N.localBase^(-outer)*F.value+
      Kh*(N.localBase^(-outer)*own.value+1))) by ring,hraw]
    have h1 := mul_le_mul_of_nonneg_left hOwn hKh
    have h2 := mul_le_mul_of_nonneg_left hpower hKh
    have hpow0 : 0 ≤ N.localBase^(1+epsilon) := Real.rpow_nonneg hZ.le _
    have hinner : Kreturn*F.value+Kh*own.value+Kh*N.localBase^outer ≤
        (Kreturn+2*Kh)*F.value+Kh*N.localBase^(1+epsilon) := by
      nlinarith only [h1,h2]
    apply (add_le_add le_rfl (mul_le_mul_of_nonneg_left hinner hChigh)).trans
    have hremaining := mul_nonneg (mul_nonneg hChigh (add_nonneg hKreturn hKh)) hpow0
    nlinarith only [hremaining,hF]
  change N.sourceEnergy hH ≤ _ at he
  apply he.trans
  have hcontrol : 0 ≤ Cenergy*diagonalControl N.state.radial.profile*
      (N.profiles.control S)^2*(1+|N.t|+N.height)^degree := by
    have hd := diagonalControl_nonneg N.state.radial.profile
    have hh := N.height_nonneg
    positivity
  apply (mul_le_mul_of_nonneg_left hbudget hcontrol).trans_eq
  ring

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_node_at_state_from_whole_forest
