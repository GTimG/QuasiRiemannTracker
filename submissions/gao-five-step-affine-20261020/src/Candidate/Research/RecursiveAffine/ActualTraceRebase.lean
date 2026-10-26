/- Exact representation changes for physical returned-path provenance. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ReachableNode

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153SourceReturn Cycle153RegionalLow

variable {α : Type} [Fintype α] [DecidableEq α]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=α) M H} {j : Fin 4} {N : ReachableNode C j}

/-- All true global-source facts survive a representation rebase. The
local count fields acquire the relative unit, while physical nodes,
source weights, actual fees and selected geometry remain identical. -/
def ActualPathTrace.rebasePower {Z power oldUnit newUnit : ℝ}
    (hZ : 1 < Z) (hpower : 0 < power) (hpower1 : power ≤ 1)
    (hnewUnit : 0 < newUnit) (hbase : Z=C.globalBase^newUnit)
    (hunit : oldUnit=newUnit*power)
    (F : SuffixFamily (hH:=hH) j.val (4-j.val) C.etaSeed (Z^power) C.Bnorm C.Tz N.presentation.mult)
    (d : SuffixDepth (4-j.val)) (p : F.Prefix d)
    (trace : ActualPathTrace hH N oldUnit F d p) :
    ActualPathTrace hH N newUnit
      (rebaseDepthReturnedFamily hZ hpower hpower1 C.normCap_nonneg F) d p where
  representedBase_eq := hbase
  representedUnit_pos := hnewUnit
  count := trace.count
  count_eq := trace.count_eq
  node := trace.node
  scale := trace.scale
  volumeLength := trace.volumeLength
  amplification := trace.amplification
  prefixLog := trace.prefixLog
  fee := trace.fee
  missingCoordinate := trace.missingCoordinate
  reductionCoordinate := trace.reductionCoordinate
  residualF := trace.residualF
  capacityPad := trace.capacityPad
  scalePad := trace.scalePad
  sourceGates := trace.sourceGates
  fineSource := trace.fineSource
  fineFee := trace.fineFee
  fineScalePad := trace.fineScalePad
  fineCapacityPad := trace.fineCapacityPad
  remainingFee := trace.remainingFee
  node_eq := trace.node_eq
  root_scale := trace.root_scale
  root_length := trace.root_length
  root_prefix := trace.root_prefix
  terminal_prefix := trace.terminal_prefix
  relative_scale := trace.relative_scale
  length_step := trace.length_step
  residualF_nonneg := trace.residualF_nonneg
  capacity := trace.capacity
  weight := trace.weight
  coordinates := trace.coordinates
  physical_prefix := trace.physical_prefix
  prefix_preserved := trace.prefix_preserved
  length_model := trace.length_model
  unit_model := trace.unit_model
  junction_model := trace.junction_model
  deletion_model := trace.deletion_model
  missing_model := trace.missing_model
  reduction_model := trace.reduction_model
  amplifierError := trace.amplifierError
  amplifierError_nonneg := trace.amplifierError_nonneg
  fineAmplifierError := trace.fineAmplifierError
  amplifier_model := trace.amplifier_model
  terminal_scale := by
    change trace.scale trace.count=newUnit*(power*(F.part d p).scale)
    rw [←mul_assoc,←hunit]
    exact trace.terminal_scale
  terminal_length := by
    change trace.volumeLength trace.count=newUnit*(power*(F.part d p).length)
    rw [←mul_assoc,←hunit]
    exact trace.terminal_length
  terminal_amp := by
    change trace.amplification trace.count=newUnit*(power*(F.part d p).amp)
    rw [←mul_assoc,←hunit]
    exact trace.terminal_amp
  missing := by
    change newUnit*(power*F.historyMissing d p)=_
    rw [←mul_assoc,←hunit]
    exact trace.missing

/-- The whole dependent payload is transported together. This prevents
an equality of bases from separating a selected part and its provenance. -/
structure TracedSuffixFamily (N : ReachableNode C j) (base unit : ℝ) where
  family : SuffixFamily (hH:=hH) j.val (4-j.val) C.etaSeed base C.Bnorm C.Tz N.presentation.mult
  path : ∀ d p, ActualPathTrace hH N unit family d p

namespace TracedSuffixFamily

def transportBase {base base' unit : ℝ} (he : base=base')
    (F : TracedSuffixFamily (hH:=hH) N base unit) : TracedSuffixFamily (hH:=hH) N base' unit := he ▸ F

theorem transportBase_value {base base' unit : ℝ} (he : base=base')
    (F : TracedSuffixFamily (hH:=hH) N base unit) :
    (transportBase he F).family.value=F.family.value := by
  cases he
  rfl

def rebasePower {Z power oldUnit newUnit : ℝ}
    (hZ : 1 < Z) (hpower : 0 < power) (hpower1 : power ≤ 1)
    (hnewUnit : 0 < newUnit) (hbase : Z=C.globalBase^newUnit)
    (hunit : oldUnit=newUnit*power)
    (F : TracedSuffixFamily (hH:=hH) N (Z^power) oldUnit) :
    TracedSuffixFamily (hH:=hH) N Z newUnit where
  family := rebaseDepthReturnedFamily hZ hpower hpower1 C.normCap_nonneg F.family
  path := fun d p => (F.path d p).rebasePower hZ hpower hpower1 hnewUnit hbase hunit F.family d p

theorem rebasePower_value {Z power oldUnit newUnit : ℝ}
    (hZ : 1 < Z) (hpower : 0 < power) (hpower1 : power ≤ 1)
    (hnewUnit : 0 < newUnit) (hbase : Z=C.globalBase^newUnit)
    (hunit : oldUnit=newUnit*power)
    (F : TracedSuffixFamily (hH:=hH) N (Z^power) oldUnit) :
    (F.rebasePower hZ hpower hpower1 hnewUnit hbase hunit).family.value=F.family.value :=
  rebaseDepthReturnedFamily_value hZ hpower hpower1 C.normCap_nonneg F.family

/-- Re-express the selected child at its actual parent's local base.
The source node N and all of its global physical history are retained. -/
def rebaseToParent {k : Fin 4} (parent : ReachableNode C k)
    (hunit : N.unit ≤ parent.unit)
    (F : TracedSuffixFamily (hH:=hH) N N.localBase N.unit) :
    TracedSuffixFamily (hH:=hH) N parent.localBase parent.unit :=
  rebasePower parent.localBase_gt_one (div_pos N.unit_pos parent.unit_pos)
    ((div_le_one parent.unit_pos).mpr hunit) parent.unit_pos parent.localBase_eq
    (by field_simp [ne_of_gt parent.unit_pos])
    (transportBase (parent.localBase_relative N) F)

theorem rebaseToParent_value {k : Fin 4} (parent : ReachableNode C k)
    (hunit : N.unit ≤ parent.unit)
    (F : TracedSuffixFamily (hH:=hH) N N.localBase N.unit) :
    (F.rebaseToParent parent hunit).family.value=F.family.value := by
  unfold rebaseToParent
  rw [rebasePower_value,transportBase_value]

end TracedSuffixFamily
end
end OAI.SevenEighths.Cycle153Reachable

#print axioms OAI.SevenEighths.Cycle153Reachable.ActualPathTrace.rebasePower
#print axioms OAI.SevenEighths.Cycle153Reachable.TracedSuffixFamily.rebaseToParent_value
