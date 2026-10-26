/- Uniform rough bound for the actual produced node forest. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ActualTraceCoarse
import Candidate.Research.RecursiveAffine.OrientationForest

set_option autoImplicit false
set_option maxHeartbeats 650000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153SourceReturn Cycle153JointCount

private theorem innerStage_floor (n : ℕ) : (3/5:ℝ) ≤ (innerStage n).q := by
  unfold innerStage
  split <;> norm_num [Cycle153.FixedStages.stage1,Cycle153.FixedStages.stage2,
    Cycle153.FixedStages.stage3,Cycle153.FixedStages.stage4]

private theorem suffixJunction_floor (start count : ℕ) (d : SuffixDepth count) :
    (3/5:ℝ) ≤ suffixJunction start count d := by
  induction count generalizing start with
  | zero => exact nomatch d
  | succ count ih =>
    cases d with
    | none => exact innerStage_floor start
    | some d => exact ih (start+1) d

variable {α : Type} [Fintype α] [DecidableEq α]
  {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
  {hH : RayOrthogonality.globalUnits M ≤ H}

/-- Bind native literal counting to the actual produced family's full
chronology, retained native path weights and genuine terminal source
caps. The constants precede every moving node and continuous source
configuration. No prefix-cardinality, forest-weight or final source
estimate is assumed. -/
theorem actual_source_family_component_coarse_bound
    (C : SourceContext (α:=α) M H) (j : Fin 4) (d : SuffixDepth (4-j.val))
    (Bsrc loss : ℝ) (hBsrc : 0 ≤ Bsrc) (hloss : 0<loss)
    (hbudget : (suffixOffset (4-j.val) d:ℝ)*Bsrc ≤ C.Bnorm) :
    ∃J : ℕ,∃Cc : ℝ,0<Cc ∧
    ∀N : ReachableNode C j,2 ≤ N.localBase→0 ≤ C.Tz→
    ∀(boxes : ℕ→Finset (Fin 4→ℤ))(F : N.Family hH)
      (chronology : ForestChronology hH N F Bsrc boxes)
      (path : ∀d p,ActualPathTrace hH N N.unit F d p)
      (terminalSource : ∀d p,TerminalSourceCaps (F.part d p).scale (F.part d p).length
        (F.part d p).amp (Real.logb N.localBase ((Ideal.span {F.multiplier d p}).absNorm:ℝ)))
      (terminalLoss : ∀d p,(F.part d p).loss ≤ terminalLossCap j)
      (classCap : ∀d p b,(Fintype.card ((F.part d p).record b).Class:ℝ) ≤ C.highClassCap),
    ∑p,F.weight d p*(F.part d p).value ≤
      16*Cc*(∏k∈Finset.range (suffixOffset (4-j.val) d),(((boxes k).card:ℝ)+1))*
        (1+C.Tz)^J*C.highClassCap*
          N.localBase^(280611+(suffixOffset (4-j.val) d:ℝ)*Bsrc+loss) := by
  obtain ⟨J,hJ⟩:=depth_family_component_coarse_bound
    (Base:=suffixBase j.val (4-j.val)) M H hH d Bsrc C.Bnorm loss
    hBsrc C.normCap_nonneg hloss (suffixOffset (4-j.val) d) hbudget
  obtain ⟨Cc,hCc,hbound⟩:=hJ (suffixDictionary j.val (4-j.val)) C.etaSeed
  refine ⟨J,Cc,hCc,?_⟩
  intro N hZ hT boxes F chronology path terminalSource terminalLoss classCap
  have hword (word : OrientationWord) :
      ∑p,(orientationFamily hH F chronology word).weight d p*
        ((orientationFamily hH F chronology word).part d p).value ≤
      Cc*(∏k∈Finset.range (suffixOffset (4-j.val) d),(((boxes k).card:ℝ)+1))*
        (1+C.Tz)^J*C.highClassCap*
          N.localBase^(280611+(suffixOffset (4-j.val) d:ℝ)*Bsrc+loss) := by
    let Fw:=orientationFamily hH F chronology word
    let history:=orientationLiteralHistory hH F chronology word
    have h:=hbound (suffixJunction j.val (4-j.val)) N.localBase C.Tz N.presentation.mult hZ hT
      Fw boxes (chronology.units word) (wordLeft word) (history.code d)
      (history.injective d) (history.multiplier d)
      C.highClassCap 1 4 1 1 250000 30600 (suffixJunction_floor _ _ d)
      C.highClassCap_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (history.facts d)
      (fun p=>(path d p.val).weight_coarse_local)
      (fun p=>by
        have cap:=terminalSource d p.val
        refine ⟨cap.scale_le,cap.length_le,cap.amp_le,?_,cap.normLog_le⟩
        exact (terminalLoss d p.val).trans (by
          dsimp only [terminalLossCap]
          have hj : 0 ≤ (j.val:ℝ) := Nat.cast_nonneg _
          linarith only [hj]))
      (fun b p=>classCap d p.val b)
    convert h using 1 <;> ring
  have h:=orientation_component_bound hH F chronology d
    (Cc*(∏k∈Finset.range (suffixOffset (4-j.val) d),(((boxes k).card:ℝ)+1))*
      (1+C.Tz)^J*C.highClassCap*
        N.localBase^(280611+(suffixOffset (4-j.val) d:ℝ)*Bsrc+loss)) hword
  convert h using 1 <;> ring

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_source_family_component_coarse_bound
