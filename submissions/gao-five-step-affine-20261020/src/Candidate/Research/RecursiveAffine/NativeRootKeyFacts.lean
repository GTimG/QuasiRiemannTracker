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

/-- Literal root key source facts use the actual root prefix norm1000,
not a fictitious inner node or a reset ancestor in a later source. -/
theorem actual_root_selected_native_key_facts (Z : ℝ)(hZ : 1<Z)
    (reflected : Bool)(s : Input Current)(R seed : Ideal O)
    (Mrow amp xi reserve b firstHeight : ℝ)(budget : ℕ)
    (key : ℤ×(Fin 5→ℤ))(hseed : Squarefree seed)(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (hsource : sourceRadius s ≤ Z^(3:ℝ))
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow)
      Z xi (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (units : FirstSourceLabel→O)(box : Finset (Fin 4→ℤ)) :
    let Rows:=↥(mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp xi reserve b firstHeight
      budget hZ key hz1 hz2 firstIndex)
    let code:=nativeLowHistoryCode reflected s R seed Z Mrow amp xi reserve b firstHeight
      budget hZ key hz1 hz2 firstIndex
    ∀(r : Rows),
    let mult:=Cycle63Moment.childMultiplier (!reflected) (1:O) units (code r).1
    mult≠0 → ((Ideal.span {mult}).absNorm:ℝ) ≤ Z^(1000:ℝ) →
    ((code r).1.2.1.1.absNorm:ℝ) ≤ Z^(130:ℝ) →
    ((code r).1.2.1.2.absNorm:ℝ) ≤ Z^(130:ℝ) →
    (code r).2.2∈box →
    DecoratedFacts (fun _ : Unit=>(1:O)) (!reflected) (fun _=>units)
      Z 250000 box ((),code r) := by
  intro Rows code r mult hmult hmultGlobal hsecondC hsecondD hbox
  have gates:=nativeLowHistoryCode_native_gates reflected s R seed Z Mrow amp xi reserve b firstHeight
    budget hZ key hz1 hz2 firstIndex r
  have firstCaps:=actual_main_low_first_source_gates reflected s R seed (Z^Mrow) Z xi 3
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hseed hz1 hz2 hsource key firstIndex r.val.1
  rcases firstCaps with ⟨hfirstC,hfirstD,_,_,_,hfirstCcap,hfirstDcap,_⟩
  have hmultLocal:=hmultGlobal
  have hmissing : ((firstSourceMissing (!reflected) (code r).1.1).absNorm:ℝ) ≤ Z^(3:ℝ) := by
    exact (Nat.cast_le.mpr (first_missing_norm_le (!reflected) (code r).1.1 hfirstC hfirstD).2.1).trans hfirstCcap
  have hrow : ((Ideal.span {mult}*firstSourceMissing (!reflected) (code r).1.1).absNorm:ℝ) ≤
      Z^(250000:ℝ) := by
    rw [map_mul,Nat.cast_mul]
    calc
      _ ≤ Z^(1000:ℝ)*Z^(3:ℝ) :=
        mul_le_mul hmultLocal hmissing (Nat.cast_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      _ = Z^(1003:ℝ) := by rw [←Real.rpow_add (zero_lt_one.trans hZ)];norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)
  have cap3 : Z^(3:ℝ) ≤ Z^(250000:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)
  have cap130 : Z^(130:ℝ) ≤ Z^(250000:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)
  have hmult250000 : ((Ideal.span {mult}).absNorm:ℝ) ≤ Z^(250000:ℝ) :=
    hmultLocal.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))
  refine ⟨?_,gates.2.2.1,gates.2.2.2,hbox⟩
  change StepFacts (fun _ : Unit=>(1:O)) (!reflected) (fun _=>units)
    Z 250000 ((),(code r).1)
  have hmultEq : appendMultiplier (fun _ : Unit=>(1:O)) (!reflected) (fun _=>units)
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
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_root_selected_native_key_facts
