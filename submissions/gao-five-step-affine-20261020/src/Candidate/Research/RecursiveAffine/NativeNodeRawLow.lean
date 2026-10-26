/- Normalize the actual native physical source into the regional LOW interface.
Copyright (c)2026 Zhongpai Gao. Native physical source by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.RegionalRawLowSelectedAt
import Candidate.Research.RecursiveAffine.NativeInnerLowNormalization
import Candidate.Research.RecursiveAffine.NativeNodeAtState

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 5000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open HeckeFamily CanonicalQuadraticSieve QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentAllocatedRayDictionary
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open Cycle63InitialMass Cycle153Reachable Cycle153RegionalState Cycle153SourceReturn
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable (hH : RayOrthogonality.globalUnits M ≤ H)
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}(N : ReachableNode C j)
/-- The exact source-wide LOW obligation left by the real AtState theorem
at this actual node. The whole-forest attainer must prove this predicate;
no energy or returned-count estimate is stored in the node itself. -/
def NativeNodeRawLowAt
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)
    (Cs : ℝ)(Sp : Finset alpha→Finset (ℕ×ℕ))(degreeLow : Finset alpha→ℕ)
    (Klow : Finset alpha→ℝ)(hT : 2<N.localBase^g.τ)
    (hbetaHi : HeckeZeroSupremum.beta ≤ 7/8)(outer Kreturn Bsrc : ℝ)
    (boxes : ℕ→Finset (Fin 4→ℤ)) : Prop := by
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
    RegionalRawLowSelectedAt M H hH C.W hbeta g 2
      (Cycle25.Energy.commonMesh 2 28 1 (g.μ/8)) Cs (fun _ _ _=>True)
      (fun _ _ _ _ _=>True) (Sp N.slots) (degreeLow N.slots) (Klow N.slots)
      C.etaSeed C.Q C.Q_le_M C.fixed_small N.localBase outer Kreturn (NativeNodeForestReceipt hH N Bsrc boxes)
      (fun receipt=>receipt.family.value) N.localBase_gt_one
      (N.input hH) N.profiles caps (fun i=>C.theta i) (fun i=>C.originalWeight i/N.unit)
      (fun i=>C.sigma i) (fun i=>C.frequency i) hm N.state.puncture 1 20 N.state.rowWidth
      N.state.puncture_ne_zero squarefree_one (by norm_num) N.state.puncture_bound
      N.state.row_nonneg hrow hfit trivial N.height C.slotMesh
      (fun i=>div_nonneg (C.originalWeight_nonneg i) N.unit_pos.le)
      hwL hwr C.slotMesh_pos.le N.weight_mesh (fun i=>C.sigma_fixed i)
      N.height_nonneg N.frequency_bound hT hbetaHi hslots haff

/-- Every actual source configuration is normalized against one whole
licensed arithmetic envelope. The source hypothesis is a literal raw
physical estimate with an actual receipt, not a normalized LOW or energy
conclusion. The native OLD target comparison stays explicit in it. -/
theorem native_node_low_at_of_actual_raw_source
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)(hbetaHi : HeckeZeroSupremum.beta ≤ 7/8)
    (g : GeometryAffineLowSchedule)(Cs : ℝ)
    (Sp : Finset alpha→Finset (ℕ×ℕ))(degreeLow : Finset alpha→ℕ)
    (Klow : Finset alpha→ℝ)(hKlow : ∀J,0 ≤ Klow J)
    (hT : 2<N.localBase^g.τ)(outer Kreturn Bsrc : ℝ)
    (boxes : ℕ→Finset (Fin 4→ℤ))(hKreturn : 0 ≤ Kreturn)
    (envelope : NativeArithmeticEnvelope hH N Bsrc boxes)
    (hsource : NativeNodeRawLowAt hH N hbeta g Cs Sp degreeLow Klow hT hbetaHi
      outer Kreturn Bsrc boxes) :
    NativeNodeLowAt hH N hbeta g Cs Sp degreeLow Klow hT hbetaHi
      ((2*Kreturn)*N.localBase^(-outer)*envelope.receipt.family.value) := by
  letI : Cycle63.AffineLedger:=N.ledger
  intro caps hm hrow hfit hwL hwr hslots haff
  intro Label inst reflected second bin t firstIndex
  dsimp only
  intro hamp0 hamp homega htarget hf₁ hinj hfirstproj
  intro χ₀ m hm₀ hml hm₂ Ψ t₀ u
  obtain ⟨hP,hPN,hPNc,raw⟩:=@hsource caps hm hrow hfit hwL hwr hslots haff Label inst reflected second bin t firstIndex
    hamp0 hamp homega htarget hf₁ hinj hfirstproj χ₀ m hm₀ hml hm₂ Ψ t₀ u
  refine ⟨hP,hPN,hPNc,?_⟩
  intro left₁ u₀ unit₁ Tz hleft hu₀ hunits hpresented
  obtain ⟨actual,rawOld,hOld,hraw⟩:=raw left₁ u₀ unit₁ Tz hleft hu₀ hunits hpresented
  have hcontrol : 0 ≤ (N.profiles.control (Sp N.slots))^2*
      geometryHighFactor reflected (geometrySupportConstant (Fintype.card N.slots) 1 (1/4) (1/4)) bin*
      (1+|t|+N.height)^(degreeLow N.slots)*(1+|t₀|)^(degreeLow N.slots)*
      (1+|u|)^(degreeLow N.slots) := by
    have hh:=N.height_nonneg
    have hf:=(geometry_high_factor_pos reflected
      (geometrySupportConstant (Fintype.card N.slots) 1 (1/4) (1/4)) bin
      (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
    positivity
  simpa only [mul_assoc] using (actual_inner_low_raw_normalization envelope actual outer _ rawOld
    (Klow N.slots) Kreturn _ _ (hKlow N.slots) hKreturn hcontrol
    (by simpa only [add_assoc] using hOld) hraw)

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.native_node_low_at_of_actual_raw_source
