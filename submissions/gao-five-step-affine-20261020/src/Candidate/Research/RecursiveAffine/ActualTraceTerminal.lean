/- The own-HIGH terminal of a literal reachable source has zero LOW edges. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ActualReachableHigh
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AddedZero

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentCanonicalFirst CenteredMomentFirstDiscardedEnergy
open CenteredMomentAmplificationChildInput Cycle153JointCount Cycle63InitialSource
open CenteredMomentEnergyBands

def terminalDummyFirst : FirstSourceLabel :=
  ⟨(1,1),⟨∅,by simp only [inactiveSubsets,Finset.empty_mem_powerset]⟩⟩

/-- A dummy node used only outside the empty range of a terminal path.
It carries no physical estimate and never participates in a sum/product. -/
def terminalDummyNode (Z : ℝ) (hZ : 1<Z) : NativePaidPathNode Z where
  unit := 1
  unit_pos := zero_lt_one
  local_base := by simpa only [Real.rpow_one] using hZ
  reflected := false
  second := false
  first := terminalDummyFirst
  firstC := CenteredMomentAddedZero.supported_one_ideal
  firstD := CenteredMomentAddedZero.supported_one_ideal
  firstSupport := rfl
  C := 1
  D := 1
  hC := CenteredMomentAddedZero.supported_one_ideal
  hD := CenteredMomentAddedZero.supported_one_ideal
  secondSupport := rfl
  inactive := ∅
  rowWidth := 0
  length := 0
  amp := 0
  xi := 0
  reserve := 0
  eps := 0
  massLoss := 0
  sideError := lowLabelSide false (Z^1) 0 terminalDummyFirst
  side := le_of_eq (zero_add (lowLabelSide false (Z^1) 0 terminalDummyFirst))

def terminalDummyFee : NativePathFee where
  driverDelta := 0
  driverError := 0
  coefficientError := 0
  shellCost := 0
  sourcePad := 0
  slotLoss := 0
  junction := 0
  actualDeletion := 0
  nativeTargetDeletion := 0
  modelDeletion := 0
  primeMesh := 0
  primeMesh_nonneg := le_rfl
  deletion_upper := by norm_num
  roundingError := 0
  roundingError_nonneg := le_rfl
  target_eq := by norm_num

theorem pathStage_fin (j : Fin 4) : pathStage j.val=j := by
  apply Fin.ext
  change min j.val 3 = j.val
  exact Nat.min_eq_left (by omega)

variable {α : Type} [Fintype α] [DecidableEq α]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=α) M H} {j : Fin 4}

/-- Literal normalized affine volume at the actual fixed-stage source. -/
theorem ReachableNode.volume_model (N : ReachableNode C j) :
    N.unit*Real.logb N.localBase (volume (N.input hH))=modelLength j N.coordinates := by
  letI : Cycle63.AffineLedger := N.ledger
  have hv := affine_volume_log_exact M H hH C.etaSeed (fun i : N.slots=>C.theta i)
    C.W C.W_smooth.continuous 1 2 (33/50) (33/50) (by norm_num) C.W_support
    (fun i : N.slots=>C.originalWeight i/N.unit) (fun i=>C.sigma i) (fun i=>C.frequency i)
    (fun i=>C.sigma_fixed i) N.state N.profiles (by norm_num)
    (Cycle63.AffineLedger.comparisonLength (length N.localBase N.X1) (length N.localBase N.X2)
      (∑i : N.slots,C.originalWeight i/N.unit)) 1 N.t N.X1 N.X2 N.X1_pos N.X2_pos
    N.localBase_gt_one (by norm_num) (by simpa only [mul_one] using N.window.left_ge)
    (by simpa only [mul_one] using N.window.right_ge)
  change Real.logb N.localBase (volume (N.input hH))=_ at hv
  rw [hv]
  exact N.length_eq

/-- Construct the own-HIGH path from the SAME native terminal record.
Its carrier identities are those of the native `none` attachment; the
only arithmetic input is the actual rounded amplifier discrepancy. -/
def ActualPathTrace.terminal (N : ReachableNode C j)
    {F : N.Family hH} {d : SuffixDepth (4-j.val)} {p : F.Prefix d}
    (hcount : suffixOffset (4-j.val) d=0)
    (hscale : (F.part d p).scale=N.state.rowWidth)
    (hlength : (F.part d p).length=Real.logb N.localBase (volume (N.input hH)))
    (hmult : F.multiplier d p=N.presentation.mult)
    (hweight : F.weight d p=1) (hmissing : F.historyMissing d p=0)
    (ampError : ℝ) (hampError : 0≤ampError)
    (hfineAmp : ampError≤1/1000000000000)
    (hamp : N.unit*(F.part d p).amp ≤
      ![Cycle153Geometry.Coordinates.a1 N.coordinates,Cycle153Geometry.Coordinates.a2 N.coordinates,
        Cycle153Geometry.Coordinates.a3 N.coordinates,Cycle153Geometry.Coordinates.a4 N.coordinates] j+ampError) :
    ActualPathTrace hH N N.unit F d p where
  representedBase_eq := N.localBase_eq
  representedUnit_pos := N.unit_pos
  count := 0
  count_eq := hcount.symm
  node := fun _=>terminalDummyNode C.globalBase C.globalBase_gt_one
  scale := fun _=>N.unit*N.state.rowWidth
  volumeLength := fun _=>N.unit*Real.logb N.localBase (volume (N.input hH))
  amplification := fun _=>N.unit*(F.part d p).amp
  prefixLog := fun _=>Real.logb C.globalBase ((Ideal.span {N.presentation.mult}).absNorm:ℝ)
  fee := fun _=>terminalDummyFee
  missingCoordinate := fun _=>0
  reductionCoordinate := fun _=>0
  residualF := fun _=>0
  capacityPad := fun _=>0
  scalePad := fun _=>0
  sourceGates := by intro i hi; omega
  fineSource := by intro i hi; omega
  fineFee := by intro i hi; omega
  fineScalePad := by intro i hi; omega
  fineCapacityPad := by intro i hi; omega
  remainingFee := by intro i hi; omega
  node_eq := by intro i hi; omega
  root_scale := rfl
  root_length := rfl
  root_prefix := rfl
  terminal_scale := by rw [hscale]
  terminal_length := by rw [hlength]
  terminal_amp := rfl
  terminal_prefix := by rw [hmult]
  relative_scale := by intro i hi; omega
  length_step := by intro i hi; omega
  residualF_nonneg := by intro i hi; omega
  capacity := by intro i hi; omega
  weight := by simpa only [Finset.range_zero,Finset.prod_empty] using hweight
  missing := by simp only [hmissing,mul_zero,Finset.range_zero,Finset.sum_empty]
  coordinates := N.coordinates
  physical_prefix := by simpa only [Nat.add_zero] using N.prefixRows
  prefix_preserved := by intro i hi; rfl
  length_model := by
    intro i hi
    have : i=0 := by omega
    subst i
    simpa only [Nat.add_zero,pathStage_fin] using N.volume_model (hH:=hH)
  unit_model := by intro i hi; omega
  junction_model := by intro i hi; omega
  deletion_model := by intro i hi; omega
  missing_model := by intro i hi; omega
  reduction_model := by intro i hi; omega
  amplifierError := fun _=>ampError
  amplifierError_nonneg := by intro i hi; exact hampError
  fineAmplifierError := by intro i hi; exact hfineAmp
  amplifier_model := by
    intro i hi
    have : i=0 := by omega
    subst i
    simpa only [Nat.add_zero,pathStage_fin] using hamp

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.ActualPathTrace.terminal
