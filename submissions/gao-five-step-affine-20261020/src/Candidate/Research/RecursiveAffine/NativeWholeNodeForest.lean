/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.WholeForestAttainer
import Candidate.Research.RecursiveAffine.NodeOutputCoarseBound
import Candidate.Research.RecursiveAffine.OwnHighForest
import Candidate.Research.RecursiveAffine.NativeOrientedHistory

set_option autoImplicit false
set_option maxHeartbeats 650000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153SourceReturn Cycle153Reachable Cycle153JointCount

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable (hH : RayOrthogonality.globalUnits M ≤ H)
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}(N : ReachableNode C j)

/-- Arithmetic provenance of an actual whole source forest, before the
current node energy is proved. Thus its genuine native counting bound can
be used to choose a source-wide attainer without a circular energy input.
These fields are outputs of physical source attachment and selection. -/
structure NativeNodeForestReceipt (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ)) where
  family : N.Family hH
  chronology : ForestChronology hH N family Bsrc boxes
  path : ∀d p,ActualPathTrace hH N N.unit family d p
  terminalLoss : ∀d p,(family.part d p).loss ≤ terminalLossCap j
  terminalSource : ∀d p,TerminalSourceCaps (family.part d p).scale (family.part d p).length
    (family.part d p).amp (Real.logb N.localBase ((Ideal.span {family.multiplier d p}).absNorm:ℝ))
  classCap : ∀d p b,(Fintype.card ((family.part d p).record b).Class:ℝ) ≤ C.highClassCap

/-- The literal empty physical return carries vacuous provenance. The
operator uses this only when its returned value vanishes; it does not
assume that a nonempty source tree has an empty arithmetic carrier. -/
def native_empty_forest_receipt (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ)) :
    NativeNodeForestReceipt hH N Bsrc boxes := by
  let F : N.Family hH:=emptyReturnedForest
  refine ⟨F,?_,?_,?_,?_,?_⟩
  · exact OrientedFamilyHistory.toNode N F (OrientedFamilyHistory.empty _ Bsrc boxes)
  · intro d p;exact nomatch p
  · intro d p;exact nomatch p
  · intro d p;exact nomatch p
  · intro d p;exact nomatch p

/-- The actual native own-HIGH record supplies the empty-LOW fallback
forest. Its chronology is the true empty history, and its source, loss,
class and rounded-amplifier receipts come from that same record. -/
def native_own_forest_receipt
    (own : ReturnedPartAt M H hH (innerStage j.val).q (prefixDictionary (j.val+1))
      C.etaSeed N.localBase C.Bnorm C.Tz N.presentation.mult)
    (hm : own.scale=N.state.rowWidth)
    (hA : own.length=Real.logb N.localBase (CenteredMomentAmplificationChildInput.volume (N.input hH)))
    (ha : letI : Cycle63.AffineLedger:=N.ledger
      own.amp=Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑i : N.slots,C.originalWeight i/N.unit))))
    (hloss : own.loss ≤ terminalLossCap j)
    (hclass : ∀b,(Fintype.card (own.record b).Class:ℝ) ≤ C.highClassCap)
    (ampError : ℝ)(hampError : 0 ≤ ampError)(hfineAmp : ampError ≤ 1/1000000000000)
    (hamp : N.unit*own.amp ≤
      ![Cycle153Geometry.Coordinates.a1 N.coordinates,Cycle153Geometry.Coordinates.a2 N.coordinates,
        Cycle153Geometry.Coordinates.a3 N.coordinates,Cycle153Geometry.Coordinates.a4 N.coordinates] j+ampError)
    (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ)) : NativeNodeForestReceipt hH N Bsrc boxes := by
  have receipts:=ownHighForest_source_receipts N own hm hA ha hloss hclass
  refine ⟨ownSuffixFamily (4-j.val) (by omega) own, ?_, ?_, ?_, ?_, ?_⟩
  · exact ownHighChronology N own Bsrc boxes
  · exact ownHighForest_paths N own hm hA ampError hampError hfineAmp hamp
  · exact receipts.2.1
  · exact receipts.1
  · exact receipts.2.2

@[simp] theorem native_own_forest_receipt_value
    (own : ReturnedPartAt M H hH (innerStage j.val).q (prefixDictionary (j.val+1))
      C.etaSeed N.localBase C.Bnorm C.Tz N.presentation.mult)
    (hm : own.scale=N.state.rowWidth)
    (hA : own.length=Real.logb N.localBase (CenteredMomentAmplificationChildInput.volume (N.input hH)))
    (ha : letI : Cycle63.AffineLedger:=N.ledger
      own.amp=Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑i : N.slots,C.originalWeight i/N.unit))))
    (hloss : own.loss ≤ terminalLossCap j)
    (hclass : ∀b,(Fintype.card (own.record b).Class:ℝ) ≤ C.highClassCap)
    (ampError : ℝ)(hampError : 0 ≤ ampError)(hfineAmp : ampError ≤ 1/1000000000000)
    (hamp : N.unit*own.amp ≤
      ![Cycle153Geometry.Coordinates.a1 N.coordinates,Cycle153Geometry.Coordinates.a2 N.coordinates,
        Cycle153Geometry.Coordinates.a3 N.coordinates,Cycle153Geometry.Coordinates.a4 N.coordinates] j+ampError)
    (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ)) :
    (native_own_forest_receipt hH N own hm hA ha hloss hclass ampError hampError hfineAmp hamp Bsrc boxes).family.value=
      own.value := ownSuffixFamily_value _ _ own

/-- The actual native history count gives a rough uniform upper bound
on complete produced forests at fixed current source. There is no assumed
prefix cardinality, path weight bound, sharp price, or current node energy
among the hypotheses. Every terminal depth stays in the same forest. -/
theorem actual_source_forests_bddAbove
    {Config : Type*}(Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))
    (hBsrc : 0 ≤ Bsrc)(hbudget : ∀d : SuffixDepth (4-j.val),
      (suffixOffset (4-j.val) d:ℝ)*Bsrc ≤ C.Bnorm)
    (hZ : 2 ≤ N.localBase)(hT : 0 ≤ C.Tz)
    (source : Config→NativeNodeForestReceipt hH N Bsrc boxes) :
    BddAbove (Set.range (fun c=>(source c).family.value)) := by
  let nativeReceipts := fun d : SuffixDepth (4-j.val)=>
    actual_source_family_component_coarse_bound (hH:=hH) C j d Bsrc 1 hBsrc (by norm_num) (hbudget d)
  let J := fun d=>Classical.choose (nativeReceipts d)
  let Cd := fun d=>Classical.choose (Classical.choose_spec (nativeReceipts d))
  let bound := fun d : SuffixDepth (4-j.val)=>
    16*Cd d*(∏k∈Finset.range (suffixOffset (4-j.val) d),(((boxes k).card:ℝ)+1))*
      (1+C.Tz)^(J d)*C.highClassCap*
        N.localBase^(280611+(suffixOffset (4-j.val) d:ℝ)*Bsrc+1)
  have hcomponent (c : Config)(d : SuffixDepth (4-j.val)) :
      (∑p,(source c).family.weight d p*((source c).family.part d p).value) ≤ bound d := by
    have native := (Classical.choose_spec (Classical.choose_spec (nativeReceipts d))).2
    exact native N hZ hT boxes (source c).family (source c).chronology (source c).path
      (source c).terminalSource (source c).terminalLoss (source c).classCap
  refine ⟨∑d,bound d,?_⟩
  rintro _ ⟨c,rfl⟩
  exact Finset.sum_le_sum (fun d _=>hcomponent c d)

/-- Choose one ACTUAL whole source forest using the genuine arithmetic
rough bound above. The chosen source retains its complete native path,
class, loss and source-cap receipts. No independent maximum is taken at a
terminal depth or at a residual allocation. -/
theorem actual_whole_node_forest_attainer
    {Config : Type*}[Nonempty Config](Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))
    (hBsrc : 0 ≤ Bsrc)(hbudget : ∀d : SuffixDepth (4-j.val),
      (suffixOffset (4-j.val) d:ℝ)*Bsrc ≤ C.Bnorm)
    (hZ : 2 ≤ N.localBase)(hT : 0 ≤ C.Tz)
    (source : Config→NativeNodeForestReceipt hH N Bsrc boxes) :
    ∃chosen : Config,∀c : Config,(source c).family.value ≤ 2*(source chosen).family.value := by
  exact whole_source_forest_attainer (fun c=>(source c).family)
    ((by norm_num : (0:ℝ) ≤ 2).trans hZ)
    (actual_source_forests_bddAbove hH N Bsrc boxes hBsrc hbudget hZ hT source)

/-- Adding the genuine own-HIGH fallback makes the configuration space
nonempty, even if no LOW configuration survives. The attainer contains
own HIGH and dominates every whole LOW forest with the same fixed factor
two. It retains one actual candidate receipt, including all terminal
source evidence needed by the subsequent AtState application. -/
theorem actual_whole_forest_with_own_baseline
    {Config : Type*}(Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))
    (hBsrc : 0 ≤ Bsrc)(hbudget : ∀d : SuffixDepth (4-j.val),
      (suffixOffset (4-j.val) d:ℝ)*Bsrc ≤ C.Bnorm)
    (hZ : 2 ≤ N.localBase)(hT : 0 ≤ C.Tz)
    (baseline : NativeNodeForestReceipt hH N Bsrc boxes)
    (source : Config→NativeNodeForestReceipt hH N Bsrc boxes)
    (ownValue : ℝ)(hbaseline : ownValue ≤ baseline.family.value)
    (hsourceOwn : ∀c,ownValue ≤ (source c).family.value) :
    ∃chosen : NativeNodeForestReceipt hH N Bsrc boxes,
      (chosen=baseline ∨ ∃c,chosen=source c) ∧ ownValue ≤ chosen.family.value ∧
      ∀c,(source c).family.value ≤ 2*chosen.family.value := by
  let candidates : Option Config→NativeNodeForestReceipt hH N Bsrc boxes :=
    fun c=>match c with | none=>baseline | some c=>source c
  obtain ⟨chosen,hchosen⟩:=actual_whole_node_forest_attainer hH N Bsrc boxes hBsrc
    hbudget hZ hT candidates
  refine ⟨candidates chosen,?_,?_,fun c=>hchosen (some c)⟩
  · cases chosen with
    | none=>exact Or.inl rfl
    | some c=>exact Or.inr ⟨c,rfl⟩
  · cases chosen with
    | none=>exact hbaseline
    | some c=>exact hsourceOwn c

/-- The own-only fallback and every LOW source are dominated by the same
actual whole attainer. Empty LOW outputs are permitted: the constant two
pays the own baseline too, without inserting an artificial own record or
changing any physical path weight. -/
theorem actual_whole_forest_and_own_attainer
    {Config : Type*}(Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))
    (hBsrc : 0 ≤ Bsrc)(hbudget : ∀d : SuffixDepth (4-j.val),
      (suffixOffset (4-j.val) d:ℝ)*Bsrc ≤ C.Bnorm)
    (hZ : 2 ≤ N.localBase)(hT : 0 ≤ C.Tz)
    (baseline : NativeNodeForestReceipt hH N Bsrc boxes)
    (source : Config→NativeNodeForestReceipt hH N Bsrc boxes)
    (ownValue : ℝ)(hbaseline : ownValue ≤ baseline.family.value) :
    ∃chosen : NativeNodeForestReceipt hH N Bsrc boxes,
      (chosen=baseline ∨ ∃c,chosen=source c) ∧ ownValue ≤ 2*chosen.family.value ∧
      ∀c,(source c).family.value ≤ 2*chosen.family.value := by
  let candidates : Option Config→NativeNodeForestReceipt hH N Bsrc boxes :=
    fun c=>match c with | none=>baseline | some c=>source c
  obtain ⟨chosen,hchosen⟩:=actual_whole_node_forest_attainer hH N Bsrc boxes hBsrc
    hbudget hZ hT candidates
  refine ⟨candidates chosen,?_,hbaseline.trans (hchosen none),fun c=>hchosen (some c)⟩
  cases chosen with
  | none=>exact Or.inl rfl
  | some c=>exact Or.inr ⟨c,rfl⟩

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_source_forests_bddAbove
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_whole_node_forest_attainer
