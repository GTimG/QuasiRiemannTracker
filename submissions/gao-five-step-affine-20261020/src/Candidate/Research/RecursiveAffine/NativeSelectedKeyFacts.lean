/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeLowHistoryFacts
import Candidate.Research.RecursiveAffine.ReachableNode
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowNormalizedPayment

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentFirstCanonicalFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
open Cycle153Reachable Cycle153JointCount

variable {alpha Current Label : Type} [Fintype alpha] [DecidableEq alpha]
  [Fintype Current] [DecidableEq Current] [Fintype Label]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
  {C : SourceContext (α:=alpha) M H} {j : Fin 4}

/-- Convert the actual native successor multiplier receipt into the local
source norm used by joint history counting. This uses the actual positive
physical unit, rather than resetting an accumulated multiplier to one. -/
theorem actual_successor_norm_local (N : ReachableNode C j) (hj : j.val<3)
    (v : O)(hglobal : ((Ideal.span {v}).absNorm:ℝ) ≤ C.globalBase^(prefixCap (j.val+1))) :
    ((Ideal.span {v}).absNorm:ℝ) ≤ N.localBase^(200000:ℝ) := by
  apply hglobal.trans
  rw [N.localBase_eq,←Real.rpow_mul (zero_lt_one.trans C.globalBase_gt_one).le]
  apply Real.rpow_le_rpow_of_exponent_le C.globalBase_gt_one.le
  have hj' : (j.val:ℝ) ≤ 2 := by exact_mod_cast (show j.val ≤ 2 by omega)
  dsimp only [prefixCap]
  push_cast
  nlinarith only [hj',N.unit_floor]

/-- Bind the real native full row key to its source arithmetic facts.
Support, equal prime supports and old-seed incidence are obtained from
that key's actual source. The multiplier bound is the already produced
native successor receipt; second source caps and dyads are the literal
source-cap/box receipts. No prefix count or energy bound is an input. -/
theorem actual_selected_native_key_facts (N : ReachableNode C j) (hj : j.val<3)
    (reflected : Bool)(s : Input Current)(R seed : Ideal O)
    (Mrow amp xi reserve b firstHeight : ℝ)(budget : ℕ)
    (key : ℤ×(Fin 5→ℤ))(hseed : Squarefree seed)(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (hsource : sourceRadius s ≤ N.localBase^(3:ℝ))
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (N.localBase^Mrow)
      N.localBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key)
    (units : FirstSourceLabel→O)(box : Finset (Fin 4→ℤ)) :
    let Rows:=↥(mainLowSelectedNonzeroRows reflected s R seed N.localBase Mrow amp xi reserve b firstHeight
      budget N.localBase_gt_one key hz1 hz2 firstIndex)
    let code:=nativeLowHistoryCode reflected s R seed N.localBase Mrow amp xi reserve b firstHeight
      budget N.localBase_gt_one key hz1 hz2 firstIndex
    ∀(r : Rows),
    let mult:=Cycle63Moment.childMultiplier (!reflected) N.presentation.mult units (code r).1
    mult≠0 → ((Ideal.span {mult}).absNorm:ℝ) ≤ C.globalBase^(prefixCap (j.val+1)) →
    ((code r).1.2.1.1.absNorm:ℝ) ≤ N.localBase^(130:ℝ) →
    ((code r).1.2.1.2.absNorm:ℝ) ≤ N.localBase^(130:ℝ) →
    (code r).2.2∈box →
    DecoratedFacts (fun _ : Unit=>N.presentation.mult) (!reflected) (fun _=>units)
      N.localBase 250000 box ((),code r) := by
  intro Rows code r mult hmult hmultGlobal hsecondC hsecondD hbox
  have gates:=nativeLowHistoryCode_native_gates reflected s R seed N.localBase Mrow amp xi reserve b firstHeight
    budget N.localBase_gt_one key hz1 hz2 firstIndex r
  have firstCaps:=actual_main_low_first_source_gates reflected s R seed (N.localBase^Mrow) N.localBase xi 3
    (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) hseed hz1 hz2 hsource key firstIndex r.val.1
  rcases firstCaps with ⟨hfirstC,hfirstD,_,_,_,hfirstCcap,hfirstDcap,_⟩
  have hmultLocal:=actual_successor_norm_local N hj mult hmultGlobal
  have hmissing : ((firstSourceMissing (!reflected) (code r).1.1).absNorm:ℝ) ≤ N.localBase^(3:ℝ) := by
    exact (Nat.cast_le.mpr (first_missing_norm_le (!reflected) (code r).1.1 hfirstC hfirstD).2.1).trans hfirstCcap
  have hrow : ((Ideal.span {mult}*firstSourceMissing (!reflected) (code r).1.1).absNorm:ℝ) ≤
      N.localBase^(250000:ℝ) := by
    rw [map_mul,Nat.cast_mul]
    calc
      _ ≤ N.localBase^(200000:ℝ)*N.localBase^(3:ℝ) :=
        mul_le_mul hmultLocal hmissing (Nat.cast_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans N.localBase_gt_one).le _)
      _ = N.localBase^(200003:ℝ) := by rw [←Real.rpow_add (zero_lt_one.trans N.localBase_gt_one)];norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le N.localBase_gt_one.le (by norm_num)
  have cap3 : N.localBase^(3:ℝ) ≤ N.localBase^(250000:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le N.localBase_gt_one.le (by norm_num)
  have cap130 : N.localBase^(130:ℝ) ≤ N.localBase^(250000:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le N.localBase_gt_one.le (by norm_num)
  have hmult250000 : ((Ideal.span {mult}).absNorm:ℝ) ≤ N.localBase^(250000:ℝ) :=
    hmultLocal.trans (Real.rpow_le_rpow_of_exponent_le N.localBase_gt_one.le (by norm_num))
  refine ⟨?_,gates.2.2.1,gates.2.2.2,hbox⟩
  change StepFacts (fun _ : Unit=>N.presentation.mult) (!reflected) (fun _=>units)
    N.localBase 250000 ((),(code r).1)
  have hmultEq : appendMultiplier (fun _ : Unit=>N.presentation.mult) (!reflected) (fun _=>units)
      ((),(code r).1)=mult := rfl
  refine ⟨?_,?_,gates.1,gates.2.1,?_,?_,?_,?_,?_⟩
  · rwa [hmultEq]
  · rwa [hmultEq]
  · rwa [hmultEq]
  · exact hfirstCcap.trans cap3
  · exact hfirstDcap.trans cap3
  · exact hsecondC.trans cap130
  · exact hsecondD.trans cap130

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_selected_native_key_facts
