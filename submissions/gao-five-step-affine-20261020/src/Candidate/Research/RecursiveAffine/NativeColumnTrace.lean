/- The actual source attainer's child/output is retained independently of energy.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ReachableNode
import Candidate.Research.RecursiveAffine.NativeCommonForest

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153Reachable Cycle153SourceReturn Cycle153RegionalLow
variable {alpha Current Daughter : Type}[Fintype alpha][DecidableEq alpha][Fintype Current]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M≤H}
variable {C : SourceContext (α:=alpha) M H}{stage : Fin 4}

/-- The exact real child chosen by the source detector. The `child`
function is instantiated by literal nodeOfNativeContinuation in the
source theorem, not by a separately selected IH output. -/
def NativeColumnOutputTrace
    (admitted : Daughter→Prop)(sourceRow : Daughter→O→ℂ)
    (J : Daughter→Finset Current)(w : Current→ℝ)(del mesh : ℝ)
    (continues : Daughter→Finset Current→Prop)
    (child : ∀(d : Daughter),admitted d→∀(z : O),sourceRow d z≠0→
      ∀(R : Finset Current),R⊆J d→(∑i∈R,w i)≤del+mesh→
      (R=J d ∨ del≤∑i∈R,w i)→continues d R→ReachableNode C stage)
    (constant epsilon Bsrc : ℝ)(control : Finset (ℕ×ℕ))(degree : ℕ)
    (boxes : ℕ→Finset (Fin 4→ℤ))
    {Z Bnorm T : ℝ}{root : O}(d : Daughter)(R : Finset Current)
    (F : SuffixFamily (hH:=hH) stage.val (4-stage.val) C.etaSeed Z Bnorm T root) : Prop :=
  (F=emptyReturnedForest ∧ ∀z,sourceRow d z=0) ∨
  ∃(hn : admitted d)(z : O)(hne : sourceRow d z≠0)(hR : R⊆J d)
    (hsum : (∑i∈R,w i)≤del+mesh)(hcover : R=J d ∨ del≤∑i∈R,w i),
    (F=emptyReturnedForest ∧ ¬continues d R) ∨
    ∃hcontinue : continues d R,
    ∃out : NodeOutput hH (child d hn z hne R hR hsum hcover hcontinue)
      constant epsilon Bsrc control degree boxes,
      F.value=out.family.value

/-- Nonempty source metadata can be eliminated without unfolding any
analytic operator, profile envelope, reciprocal or source energy. -/
theorem NativeColumnOutputTrace.live
    {admitted : Daughter→Prop}{sourceRow : Daughter→O→ℂ}
    {J : Daughter→Finset Current}{w : Current→ℝ}{del mesh : ℝ}
    {continues : Daughter→Finset Current→Prop}
    {child : ∀(d : Daughter),admitted d→∀(z : O),sourceRow d z≠0→
      ∀(R : Finset Current),R⊆J d→(∑i∈R,w i)≤del+mesh→
      (R=J d ∨ del≤∑i∈R,w i)→continues d R→ReachableNode C stage}
    {constant epsilon Bsrc : ℝ}{control : Finset (ℕ×ℕ)}{degree : ℕ}
    {boxes : ℕ→Finset (Fin 4→ℤ)}{Z Bnorm T : ℝ}{root : O}
    {d : Daughter}{R : Finset Current}
    {F : SuffixFamily (hH:=hH) stage.val (4-stage.val) C.etaSeed Z Bnorm T root}
    (h : NativeColumnOutputTrace admitted sourceRow J w del mesh continues child
      constant epsilon Bsrc control degree boxes d R F)(hne : F≠emptyReturnedForest) :
    ∃(hn : admitted d)(z : O)(hz : sourceRow d z≠0)(hR : R⊆J d)
      (hsum : (∑i∈R,w i)≤del+mesh)(hcover : R=J d ∨ del≤∑i∈R,w i)
      (hc : continues d R),
      ∃out : NodeOutput hH (child d hn z hz R hR hsum hcover hc)
        constant epsilon Bsrc control degree boxes,
        F.value=out.family.value := by
  rcases h with hz | ⟨hn,z,hz,hR,hsum,hcover,hbranch⟩
  · exact False.elim (hne hz.1)
  · rcases hbranch with hz | ⟨hc,out,hvalue⟩
    · exact False.elim (hne hz.1)
    · exact ⟨hn,z,hz,hR,hsum,hcover,hc,out,hvalue⟩

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.NativeColumnOutputTrace.live
