/- Native root count constants before every moving source and base. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.RootForestReturnedBound

set_option autoImplicit false
set_option maxHeartbeats 650000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153JointCount Cycle153SourceReturn

private theorem root_fixed_q_floor (count start : ℕ)(d : SuffixDepth count) :
    (3/5:ℝ) ≤ suffixJunction start count d := by
  induction count generalizing start with
  | zero=>exact nomatch d
  | succ count ih=>
    cases d with
    | none=>
      change (3/5:ℝ) ≤ (innerStage start).q
      unfold innerStage
      split <;> norm_num [Cycle153.FixedStages.stage1,Cycle153.FixedStages.stage2,
        Cycle153.FixedStages.stage3,Cycle153.FixedStages.stage4]
    | some d=>exact ih (start+1) d

/-- Density degrees and constants are chosen from the fixed dictionary,
character, source norm caps and count loss before a moving base Z,
physical profiles, original ray data or source context is selected. -/
theorem root_fixed_component_count_constants
    (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M ≤ H)
    (eta : Character)(Bsrc Bnorm loss : ℝ)(hBsrc : 0 ≤ Bsrc)(hBnorm : 0 ≤ Bnorm)(hloss : 0<loss)
    (d : SuffixDepth 4)(hbudget : (rootHistoryDepth d:ℝ)*Bsrc ≤ Bnorm) :
    ∃J : ℕ,∃Cc : ℝ,0<Cc ∧
    ∀{α : Type}[Fintype α][DecidableEq α](C : SourceContext (α:=α) M H),
    C.etaSeed=eta → C.Bnorm=Bnorm → 2 ≤ C.globalBase → 0 ≤ C.Tz →
    ∀(boxes : ℕ→Finset (Fin 4→ℤ))(F : NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes),
    ∑p,F.family.weight d p*(F.family.part d p).value ≤
      16*Cc*(∏k∈Finset.range (rootHistoryDepth d),(((boxes k).card:ℝ)+1))*
        (1+C.Tz)^J*C.highClassCap*C.globalBase^((1:ℝ)-1/10000000+1/10000000000+loss) := by
  obtain ⟨J,hJ⟩:=literal_family_component_returned_bound (Base:=suffixBase 0 4) M H hH d Bsrc Bnorm
    loss hBsrc hBnorm hloss rootHistoryDepth hbudget
  obtain ⟨Cc,hCc,hbound⟩:=hJ (suffixDictionary 0 4) eta
  refine ⟨J,Cc,hCc,?_⟩
  intro α _ _ C heta hnorm hZ hT boxes F
  cases heta
  cases hnorm
  have hword (word : OrientationWord) :
      ∑p,(rootOrientationFamily F.family F.chronology word).weight d p*
        ((rootOrientationFamily F.family F.chronology word).part d p).value ≤
      Cc*(∏k∈Finset.range (rootHistoryDepth d),(((boxes k).card:ℝ)+1))*
        (1+C.Tz)^J*C.highClassCap*C.globalBase^((1:ℝ)-1/10000000+1/10000000000+loss) := by
    let Fw:=rootOrientationFamily F.family F.chronology word
    let history:=rootOrientationHistory F.family F.chronology word
    exact hbound (suffixJunction 0 4) C.globalBase C.Tz 1 hZ hT Fw boxes
      (F.chronology.units word) (wordLeft word) history C.highClassCap
      ((1:ℝ)-1/10000000+1/10000000000) (root_fixed_q_floor 4 0 d) C.highClassCap_nonneg
      (fun b p=>F.classCap d p.val b)
      (fun b p=>(F.path d p.val).class_payment (F.terminalLoss d p.val) b)
  have h:=rootOrientation_component_bound F.family F.chronology d
    (Cc*(∏k∈Finset.range (rootHistoryDepth d),(((boxes k).card:ℝ)+1))*
      (1+C.Tz)^J*C.highClassCap*C.globalBase^((1:ℝ)-1/10000000+1/10000000000+loss)) hword
  convert h using 1 <;> ring

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.root_fixed_component_count_constants
