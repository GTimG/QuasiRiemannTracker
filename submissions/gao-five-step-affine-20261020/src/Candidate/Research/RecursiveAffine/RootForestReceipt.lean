/- Actual root LOW forest source metadata, before root energy. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeOrientedHistory
import Candidate.Research.RecursiveAffine.NativeCommonForest
import Candidate.Research.RecursiveAffine.ActualTraceCoarse
import Candidate.Research.RecursiveAffine.OrientationForest

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153JointCount Cycle153SourceReturn Cycle153RegionalLow

variable {α : Type} [Fintype α] [DecidableEq α]
  {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
  {hH : RayOrthogonality.globalUnits M≤H}
  {C : SourceContext (α:=α) M H}

/-- The unmarked root LOW forest includes its literal first physical
edge. The root's marked HIGH contribution remains a separate source. -/
abbrev RootLowFamily (C : SourceContext (α:=α) M H) :=
  SuffixFamily (hH:=hH) 0 4 C.etaSeed C.globalBase C.Bnorm C.Tz 1

def rootHistoryDepth (d : SuffixDepth 4) : ℕ:=suffixOffset 4 d+1

/-- A source-selected root path retains the same actual child node,
global-rebased child family and terminal record. The root edge is genuine
physical arithmetic. Every binding comes from the literal Σ attachment,
without a weighted-class-payment or root-energy premise. -/
structure RootNativePath (F : RootLowFamily (hH:=hH) C)
    (d : SuffixDepth 4) (p : F.Prefix d) where
  child : ReachableNode C (0:Fin 4)
  childFamily : SuffixFamily (hH:=hH) 0 4 C.etaSeed C.globalBase C.Bnorm C.Tz child.presentation.mult
  childPrefix : childFamily.Prefix d
  trace : ActualPathTrace hH child 1 childFamily d childPrefix
  edge : RootTraceEdge (C:=C) trace.coordinates
    (trace.scale 0) (trace.volumeLength 0) (trace.prefixLog 0)
  multiplier : F.multiplier d p=childFamily.multiplier d childPrefix
  part : HEq (F.part d p) (childFamily.part d childPrefix)
  weight : F.weight d p=C.globalBase^(edge.node.scale+edge.node.shiftedOutside+
    edge.fee.junction*edge.fee.modelDeletion+edge.fee.amount)*childFamily.weight d childPrefix
  missing : F.historyMissing d p=edge.node.coordinate 1+childFamily.historyMissing d childPrefix

/-- This rough cap follows from the retained actual native path, rather
than being assumed separately for every source configuration. -/
theorem RootNativePath.weight_coarse
    {F : RootLowFamily (hH:=hH) C}{d : SuffixDepth 4}{p : F.Prefix d}
    (path : RootNativePath F d p) : F.weight d p≤C.globalBase^(816:ℝ) := by
  rw [path.weight]
  exact root_trace_weight_coarse path.child path.childFamily d path.childPrefix path.trace path.edge

/-- Energy-free provenance of one whole actual root LOW source forest.
It is selected as a whole before the current root source energy is
proved, so the rough counting bound can license a genuine attainer. -/
structure NativeRootForestReceipt (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ)) where
  family : RootLowFamily (hH:=hH) C
  chronology : OrientedFamilyHistory family rootHistoryDepth Bsrc boxes
  path : ∀d p,RootNativePath family d p
  terminalLoss : ∀d p,(family.part d p).loss≤6/1000000000000
  terminalSource : ∀d p,TerminalSourceCaps (family.part d p).scale (family.part d p).length
    (family.part d p).amp (Real.logb C.globalBase ((Ideal.span {family.multiplier d p}).absNorm:ℝ))
  classCap : ∀d p b,(Fintype.card ((family.part d p).record b).Class:ℝ)≤C.highClassCap

/-- The genuine empty LOW return gives a nonempty selection menu when no
LOW source configuration contributes. Its carrier has no invented rows. -/
def native_empty_root_forest_receipt
    (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ)) : NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes :=
  { family:=emptyReturnedForest
    chronology:={
      word:=fun _ p=>nomatch p
      word_padding:=fun _ p=>nomatch p
      units:=fun _ _ _ _=>1
      code:=fun _ p=>nomatch p
      injective:=fun _ p=>nomatch p
      multiplier:=fun _ p=>nomatch p
      missing:=fun _ p=>nomatch p
      facts:=fun _ p=>nomatch p }
    path:=fun _ p=>nomatch p
    terminalLoss:=fun _ p=>nomatch p
    terminalSource:=fun _ p=>nomatch p
    classCap:=fun _ p=>nomatch p }

/-- Partition the already selected actual root family by its literal
reflection word; terminal parts and all original coefficients stay fixed. -/
def rootOrientationFamily (F : RootLowFamily (hH:=hH) C)
    {Bsrc : ℝ}{boxes : ℕ→Finset (Fin 4→ℤ)}
    (hist : OrientedFamilyHistory F rootHistoryDepth Bsrc boxes) (word : OrientationWord) :
    RootLowFamily (hH:=hH) C where
  Prefix:=fun d=>{p : F.Prefix d // hist.word d p=word}
  prefixFintype:=fun _=>inferInstance
  multiplier:=fun d p=>F.multiplier d p.val
  root_divides:=fun d p=>F.root_divides d p.val
  historyMissing:=fun d p=>F.historyMissing d p.val
  historyMissing_nonneg:=fun d p=>F.historyMissing_nonneg d p.val
  part:=fun d p=>F.part d p.val
  weight:=fun d p=>F.weight d p.val
  weight_nonneg:=fun d p=>F.weight_nonneg d p.val

def rootOrientationHistory (F : RootLowFamily (hH:=hH) C)
    {Bsrc : ℝ}{boxes : ℕ→Finset (Fin 4→ℤ)}
    (hist : OrientedFamilyHistory F rootHistoryDepth Bsrc boxes) (word : OrientationWord) :
    LiteralFamilyHistory (rootOrientationFamily F hist word) rootHistoryDepth
      (hist.units word) (wordLeft word) Bsrc boxes where
  code:=fun d p=>hist.code d p.val
  injective:=by
    intro d p q heq
    apply Subtype.ext
    apply hist.injective d
    exact Prod.ext (p.property.trans q.property.symm) heq
  multiplier:=by
    intro d p
    simpa only [p.property,rootOrientationFamily] using hist.multiplier d p.val
  missing:=by
    intro d p
    simpa only [p.property,rootOrientationFamily] using hist.missing d p.val
  facts:=by
    intro d p
    simpa only [p.property] using hist.facts d p.val

private def rootOrientationEquiv (F : RootLowFamily (hH:=hH) C)
    {Bsrc : ℝ}{boxes : ℕ→Finset (Fin 4→ℤ)}
    (hist : OrientedFamilyHistory F rootHistoryDepth Bsrc boxes)(d : SuffixDepth 4) :
    (Σword : OrientationWord,{p : F.Prefix d // hist.word d p=word}) ≃ F.Prefix d where
  toFun:=fun p=>p.2.val
  invFun:=fun p=>⟨hist.word d p,⟨p,rfl⟩⟩
  left_inv:=by rintro ⟨word,p,hp⟩;dsimp only;cases hp;rfl
  right_inv:=fun _=>rfl

theorem rootOrientation_component_sum (F : RootLowFamily (hH:=hH) C)
    {Bsrc : ℝ}{boxes : ℕ→Finset (Fin 4→ℤ)}
    (hist : OrientedFamilyHistory F rootHistoryDepth Bsrc boxes)(d : SuffixDepth 4) :
    (∑word : OrientationWord,∑p,(rootOrientationFamily F hist word).weight d p*
      ((rootOrientationFamily F hist word).part d p).value)=∑p,F.weight d p*(F.part d p).value := by
  have h:=Fintype.sum_equiv (rootOrientationEquiv F hist d)
    (fun p=>F.weight d p.2.val*(F.part d p.2.val).value)
    (fun p=>F.weight d p*(F.part d p).value) (fun _=>rfl)
  rw [Fintype.sum_sigma] at h
  exact h

theorem rootOrientation_component_bound (F : RootLowFamily (hH:=hH) C)
    {Bsrc : ℝ}{boxes : ℕ→Finset (Fin 4→ℤ)}
    (hist : OrientedFamilyHistory F rootHistoryDepth Bsrc boxes)(d : SuffixDepth 4)(bound : ℝ)
    (h : ∀word : OrientationWord,∑p,(rootOrientationFamily F hist word).weight d p*
      ((rootOrientationFamily F hist word).part d p).value≤bound) :
    ∑p,F.weight d p*(F.part d p).value≤16*bound := by
  rw [←rootOrientation_component_sum F hist d]
  calc
    _≤∑_word : OrientationWord,bound:=Finset.sum_le_sum (fun w _=>h w)
    _=16*bound:=by norm_num [OrientationWord,Fintype.card_fun]

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.RootNativePath.weight_coarse
#print axioms OAI.SevenEighths.Cycle153Reachable.rootOrientation_component_bound
