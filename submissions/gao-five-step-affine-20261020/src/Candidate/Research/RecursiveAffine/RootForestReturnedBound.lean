/- Fine source-count payment for the one actual whole root LOW forest. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.RootForestReceipt
import Candidate.Research.RecursiveAffine.ActualTraceFinePayment

set_option autoImplicit false
set_option maxHeartbeats 900000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153JointCount Cycle153SourceReturn Cycle153Geometry LocalMoment

/-- The robust physical prefix already retained by every produced path
controls all historical negative-coordinate allowances. No exact sign is
inferred from a robust inequality. -/
theorem root_history_robust_of_prefix (j : Fin 4)(x : Fin 14→ℝ)
    (hp : Cycle153ReachableGeometry.PrefixRows (j.val+1) x) :
    -(1/1000000000000:ℝ) ≤ rootHistoricalV j x ∧
    -(1/1000000000000:ℝ) ≤ rootHistoricalRed j x := by
  have hv0:=(hp 35 (Or.inr (by norm_num)))
  have hv1:=(hp 36 (Or.inr (by norm_num)))
  have hv2:=(hp 37 (Or.inr (by norm_num)))
  have hv3:=(hp 38 (Or.inr (by norm_num)))
  have hr0:=(hp 39 (Or.inr (by norm_num)))
  have hr1:=(hp 40 (Or.inr (by norm_num)))
  have hr2:=(hp 41 (Or.inr (by norm_num)))
  have hr3:=(hp 42 (Or.inr (by norm_num)))
  change -(1/1000000000000000:ℝ) ≤ Coordinates.V0 x at hv0
  change -(1/1000000000000000:ℝ) ≤ Coordinates.V1 x at hv1
  change -(1/1000000000000000:ℝ) ≤ Coordinates.V2 x at hv2
  change -(1/1000000000000000:ℝ) ≤ Coordinates.V3 x at hv3
  change -(1/1000000000000000:ℝ) ≤ Coordinates.Red0 x at hr0
  change -(1/1000000000000000:ℝ) ≤ Coordinates.Red1 x at hr1
  change -(1/1000000000000000:ℝ) ≤ Coordinates.Red2 x at hr2
  change -(1/1000000000000000:ℝ) ≤ Coordinates.Red3 x at hr3
  fin_cases j <;>
    norm_num [rootHistoricalV,rootHistoricalRed,Coordinates.historicalMissing1,Coordinates.historicalMissing2,
      Coordinates.historicalMissing3,Coordinates.historicalMissing4,Coordinates.historicalReduction1,
      Coordinates.historicalReduction2,Coordinates.historicalReduction3,Coordinates.historicalReduction4] <;>
    constructor <;> linarith only [hv0,hv1,hv2,hv3,hr0,hr1,hr2,hr3]

section Transfer
variable {BType : Type}{M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
  {hH : RayOrthogonality.globalUnits M ≤ H}
  {q Z Bnorm Tz : ℝ}{dict : Character→BType→Character}{eta : Character}{v v' : O}

private theorem actual_part_payment_transport
    (R : ReturnedPartAt M H hH q dict eta Z Bnorm Tz v)
    (R' : ReturnedPartAt M H hH q dict eta Z Bnorm Tz v')
    (hv : v=v')(hpart : HEq R R') (weight weight' missing missing' E L : ℝ)
    (hweight : weight=weight')(hmissing : missing=missing')
    (hloss : R.loss ≤ L)
    (hpay : R'.loss ≤ L→∀b c,weight'*Z^((R'.record b).exponent c+(R'.record b).missExp c+
      unmarkedDensity (2*(R'.record b).zeroBin c-1)*(R'.record b).rowExp c+missing') ≤ Z^E) :
    ∀b c,weight*Z^((R.record b).exponent c+(R.record b).missExp c+
      unmarkedDensity (2*(R.record b).zeroBin c-1)*(R.record b).rowExp c+missing) ≤ Z^E := by
  cases hv
  have heq:=eq_of_heq hpart
  cases heq
  simpa only [hweight,hmissing] using hpay hloss
end Transfer

variable {α : Type} [Fintype α] [DecidableEq α]
  {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
  {hH : RayOrthogonality.globalUnits M ≤ H}
  {C : SourceContext (α:=α) M H}

/-- Derive the actual root family's weighted class payment from its
retained source path and the checked physical scalar certificates. The
literal coefficient and every historical X1 are preserved, with no
weighted-payment or negative-coordinate-sign premise. -/
theorem RootNativePath.class_payment
    {F : RootLowFamily (hH:=hH) C}{d : SuffixDepth 4}{p : F.Prefix d}
    (path : RootNativePath F d p)(hloss : (F.part d p).loss ≤ 6/1000000000000) :
    ∀b c,F.weight d p*C.globalBase^(((F.part d p).record b).exponent c+
      ((F.part d p).record b).missExp c+
      unmarkedDensity (2*((F.part d p).record b).zeroBin c-1)*((F.part d p).record b).rowExp c+
      F.historyMissing d p) ≤ C.globalBase^((1:ℝ)-1/10000000+1/10000000000) := by
  apply actual_part_payment_transport (F.part d p) (path.childFamily.part d path.childPrefix)
    path.multiplier path.part _ _ _ _ _ (6/1000000000000) path.weight path.missing hloss
  intro hchildLoss b c
  have hn : path.trace.count<4 := by
    rw [path.trace.count_eq]
    exact suffixOffset_lt 4 d
  let k : Fin 4:=⟨path.trace.count,hn⟩
  have hp : Cycle153ReachableGeometry.PrefixRows (k.val+1) path.trace.coordinates := by
    simpa only [k,Fin.val_mk,Fin.val_zero,Nat.zero_add] using path.trace.physical_prefix
  have hr:=root_history_robust_of_prefix k path.trace.coordinates hp
  exact root_trace_class_payment_scheduled path.child path.childFamily d path.childPrefix
    path.trace path.edge b c hr.1 hr.2 hchildLoss


private theorem root_returned_q_floor (count start : ℕ)(d : SuffixDepth count) :
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

/-- Apply one terminal native density estimate to the actually produced
root component. The pointwise class bound is derived from its retained
physical path above; no desired hpay or source-count inequality appears
among the assumptions. All source configurations remain in one forest. -/
theorem actual_root_family_component_returned_bound
    (C : SourceContext (α:=α) M H)(d : SuffixDepth 4)
    (Bsrc loss : ℝ)(hBsrc : 0 ≤ Bsrc)(hloss : 0<loss)
    (hbudget : (rootHistoryDepth d:ℝ)*Bsrc ≤ C.Bnorm) :
    ∃J : ℕ,∃Cc : ℝ,0<Cc ∧
    ∀(_hZ : 2 ≤ C.globalBase)(_hT : 0 ≤ C.Tz)
      (boxes : ℕ→Finset (Fin 4→ℤ))(F : NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes),
    ∑p,F.family.weight d p*(F.family.part d p).value ≤
      16*Cc*(∏k∈Finset.range (rootHistoryDepth d),(((boxes k).card:ℝ)+1))*
        (1+C.Tz)^J*C.highClassCap*C.globalBase^((1:ℝ)-1/10000000+1/10000000000+loss) := by
  obtain ⟨J,hJ⟩:=literal_family_component_returned_bound (Base:=suffixBase 0 4) M H hH d Bsrc C.Bnorm
    loss hBsrc C.normCap_nonneg hloss rootHistoryDepth hbudget
  obtain ⟨Cc,hCc,hbound⟩:=hJ (suffixDictionary 0 4) C.etaSeed
  refine ⟨J,Cc,hCc,?_⟩
  intro hZ hT boxes F
  have hword (word : OrientationWord) :
      ∑p,(rootOrientationFamily F.family F.chronology word).weight d p*
        ((rootOrientationFamily F.family F.chronology word).part d p).value ≤
      Cc*(∏k∈Finset.range (rootHistoryDepth d),(((boxes k).card:ℝ)+1))*
        (1+C.Tz)^J*C.highClassCap*C.globalBase^((1:ℝ)-1/10000000+1/10000000000+loss) := by
    let Fw:=rootOrientationFamily F.family F.chronology word
    let history:=rootOrientationHistory F.family F.chronology word
    exact hbound (suffixJunction 0 4) C.globalBase C.Tz 1 hZ hT Fw boxes
      (F.chronology.units word) (wordLeft word) history C.highClassCap
      ((1:ℝ)-1/10000000+1/10000000000) (root_returned_q_floor 4 0 d) C.highClassCap_nonneg
      (fun b p=>F.classCap d p.val b)
      (fun b p=>(F.path d p.val).class_payment (F.terminalLoss d p.val) b)
  have h:=rootOrientation_component_bound F.family F.chronology d
    (Cc*(∏k∈Finset.range (rootHistoryDepth d),(((boxes k).card:ℝ)+1))*
      (1+C.Tz)^J*C.highClassCap*C.globalBase^((1:ℝ)-1/10000000+1/10000000000+loss)) hword
  convert h using 1 <;> ring

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.RootNativePath.class_payment
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_root_family_component_returned_bound
