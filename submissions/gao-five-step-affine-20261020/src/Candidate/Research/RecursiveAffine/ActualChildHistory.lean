/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ActualRootChildPath
import Candidate.Research.RecursiveAffine.NativeOrientedHistory

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153RegionalLow Cycle153SourceReturn Cycle153JointCount
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=alpha) M H}{j k : Fin 4}

/-- Equal actual prefix multipliers change only the root presentation;
the physical word, full source code and all original dyads stay fixed. -/
def rootedFamilyHistory
    {start count : ℕ}{eta : Character}{Z B T Bsrc : ℝ}{v v' : O}
    {F : SuffixFamily (hH:=hH) start count eta Z B T v}
    {n : SuffixDepth count→ℕ}{boxes : ℕ→Finset (Fin 4→ℤ)}
    (hv : v=v')(history : OrientedFamilyHistory F n Bsrc boxes) :
    OrientedFamilyHistory (suffixFamilyRootEq hv F) n Bsrc boxes := by
  cases hv
  exact history

private def traced_history_transport {N : ReachableNode C k}
    {base base' unit Bsrc : ℝ}{n : SuffixDepth (4-k.val)→ℕ}
    {boxes : ℕ→Finset (Fin 4→ℤ)}(he : base=base')
    (F : TracedSuffixFamily (hH:=hH) N base unit)
    (history : OrientedFamilyHistory F.family n Bsrc boxes) :
    OrientedFamilyHistory (TracedSuffixFamily.transportBase he F).family n Bsrc boxes := by
  cases he
  exact history

namespace NodeOutput

/-- Rebase the SAME actual child chronology to the real parent base.
Physical norm bounds are enlarged only by the proved relative unit≤1;
missing-radical logs acquire exactly that relative unit. -/
def parentHistory {child : ReachableNode C k}
    {constant eps Bsrc : ℝ}{control : Finset (ℕ×ℕ)}{degree : ℕ}{boxes : ℕ→Finset (Fin 4→ℤ)}
    (out : NodeOutput hH child constant eps Bsrc control degree boxes)(hBsrc : 0 ≤ Bsrc)
    (parent : ReachableNode C j)(hunit : child.unit ≤ parent.unit)
    (v : O)(hv : child.presentation.mult=v) :
    OrientedFamilyHistory (out.parentFamilyAtRoot parent hunit v hv)
      (suffixOffset (4-k.val)) Bsrc boxes := by
  have ht:=traced_history_transport (parent.localBase_relative child)
    (⟨out.family,out.path⟩ : TracedSuffixFamily (hH:=hH) child child.localBase child.unit)
    (OrientedFamilyHistory.ofNode child out.family out.chronology)
  have hr:=OrientedFamilyHistory.rebase parent.localBase_gt_one
    (div_pos child.unit_pos parent.unit_pos) ((div_le_one parent.unit_pos).mpr hunit)
    C.normCap_nonneg _ hBsrc ht
  exact rootedFamilyHistory hv hr

/-- The first actual inner forest is represented at the original base,
with the same literal history code and no artificial parent node. -/
def globalHistory {child : ReachableNode C (0:Fin 4)}
    {constant eps Bsrc : ℝ}{control : Finset (ℕ×ℕ)}{degree : ℕ}{boxes : ℕ→Finset (Fin 4→ℤ)}
    (out : NodeOutput hH child constant eps Bsrc control degree boxes)(hBsrc : 0 ≤ Bsrc)
    (v : O)(hv : child.presentation.mult=v) :
    OrientedFamilyHistory (out.globalFamilyAtRoot v hv) (suffixOffset 4) Bsrc boxes := by
  have ht:=traced_history_transport child.localBase_eq
    (⟨out.family,out.path⟩ : TracedSuffixFamily (hH:=hH) child child.localBase child.unit)
    (OrientedFamilyHistory.ofNode child out.family out.chronology)
  have hr:=OrientedFamilyHistory.rebase C.globalBase_gt_one child.unit_pos child.unit_le_one
    C.normCap_nonneg _ hBsrc ht
  exact rootedFamilyHistory hv hr

end NodeOutput
end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.NodeOutput.parentHistory
#print axioms OAI.SevenEighths.Cycle153Reachable.NodeOutput.globalHistory
