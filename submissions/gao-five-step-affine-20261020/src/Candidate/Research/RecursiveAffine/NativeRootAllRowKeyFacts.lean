/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootKeyFacts
import Candidate.Research.RecursiveAffine.NativeAllRowPrefixCap

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

/-- The native key facts are produced for EVERY actual row, including
zero, Direct and OLD branches. Supported-label norm factorization pays
its multiplier before a continued child, residual live row or recursive
output is selected. Actual second source caps and the actual dyad box are
kept; no multiplier/count/energy bound is a premise. -/
theorem actual_root_selected_all_row_key_facts (Z : ℝ)(hZ : 1<Z)
    (reflected : Bool)(s : Input Current)(R seed : Ideal O)
    (Mrow amp xi reserve b firstHeight : ℝ)(budget : ℕ)
    (key : ℤ×(Fin 5→ℤ))(hseed : Squarefree seed)(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (hsource : sourceRadius s ≤ Z^(3:ℝ))
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow)
      Z xi (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (units : FirstSourceLabel→O)(hunits : ∀l,IsUnit (units l))(box : Finset (Fin 4→ℤ)) :
    let Rows:=↥(mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp xi reserve b firstHeight
      budget hZ key hz1 hz2 firstIndex)
    let code:=nativeLowHistoryCode reflected s R seed Z Mrow amp xi reserve b firstHeight
      budget hZ key hz1 hz2 firstIndex
    ∀(r : Rows),
    ((code r).1.2.1.1.absNorm:ℝ) ≤ Z^(130:ℝ) →
    ((code r).1.2.1.2.absNorm:ℝ) ≤ Z^(130:ℝ) →
    (code r).2.2∈box →
    DecoratedFacts (fun _ : Unit=>(1:O)) (!reflected) (fun _=>units)
      Z 250000 box ((),code r) :=by
  intro Rows code r hsecondC hsecondD hbox
  have firstCaps:=actual_main_low_first_source_gates reflected s R seed (Z^Mrow) Z xi 3
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hseed hz1 hz2 hsource key firstIndex r.val.1
  rcases firstCaps with ⟨hfirstC,hfirstD,_,_,_,hfirstCcap,hfirstDcap,_⟩
  let datum:=geometryLowSecondDatum reflected s R seed Z Mrow amp xi reserve b firstHeight
    budget hZ key (firstIndex r.val.1) hz1 hz2 r.val.2
  have hC2 : Supported (code r).1.2.1.1:=datum.hC
  have hD2 : Supported (code r).1.2.1.2:=datum.hD
  have hCD2 : CompletedGauss.primeSupport (code r).1.2.1.1=
      CompletedGauss.primeSupport (code r).1.2.1.2:=datum.sameSupport
  have hcap:=actual_root_all_row_prefix_cap Z hZ (!reflected) units hunits (code r).1
    hfirstC hfirstD hC2 hD2 hCD2 hfirstCcap hsecondC
  exact actual_root_selected_native_key_facts Z hZ reflected s R seed Mrow amp xi reserve b firstHeight budget
    key hseed hz1 hz2 hsource firstIndex units box r hcap.1 (by simpa only [normValue,prefixCap,Nat.cast_zero,zero_add,Nat.cast_one,mul_one] using hcap.2) hsecondC hsecondD hbox

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_root_selected_all_row_key_facts
