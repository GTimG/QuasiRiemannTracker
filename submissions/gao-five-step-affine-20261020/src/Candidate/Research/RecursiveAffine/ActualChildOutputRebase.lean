/- Retain an actual child NodeOutput through the native parent-base rebase.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ActualTraceRebase

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153RegionalLow
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M≤H}
variable {C : SourceContext (α:=alpha) M H} {j k : Fin 4}

/-- Only the actual equal root-divisibility proof changes. Every carrier,
terminal record, source weight and missing-radical value stays literal. -/
def suffixFamilyRootEq {start count : ℕ} {eta : Character} {Z B T : ℝ} {v v' : O}
    (hv : v=v') (F : SuffixFamily (hH:=hH) start count eta Z B T v) :
    SuffixFamily (hH:=hH) start count eta Z B T v' where
  Prefix:=F.Prefix
  prefixFintype:=F.prefixFintype
  multiplier:=F.multiplier
  root_divides:=by intro d p;rw [←hv];exact F.root_divides d p
  historyMissing:=F.historyMissing
  historyMissing_nonneg:=F.historyMissing_nonneg
  part:=F.part
  weight:=F.weight
  weight_nonneg:=F.weight_nonneg

theorem suffixFamilyRootEq_value {start count : ℕ} {eta : Character} {Z B T : ℝ} {v v' : O}
    (hv : v=v') (F : SuffixFamily (hH:=hH) start count eta Z B T v) :
    (suffixFamilyRootEq hv F).value=F.value := rfl

namespace NodeOutput

/-- The SAME strict-IH output becomes a traced child family at its real
parent base. No current-node energy or returned-count assumption occurs. -/
def parentTraced {child : ReachableNode C k}
    {constant eps Bsrc : ℝ} {control : Finset (ℕ×ℕ)} {degree : ℕ} {boxes : ℕ→Finset (Fin 4→ℤ)}
    (out : NodeOutput hH child constant eps Bsrc control degree boxes)
    (parent : ReachableNode C j) (hunit : child.unit≤parent.unit) :
    TracedSuffixFamily (hH:=hH) child parent.localBase parent.unit :=
  TracedSuffixFamily.rebaseToParent parent hunit ⟨out.family,out.path⟩

theorem parentTraced_value {child : ReachableNode C k}
    {constant eps Bsrc : ℝ} {control : Finset (ℕ×ℕ)} {degree : ℕ} {boxes : ℕ→Finset (Fin 4→ℤ)}
    (out : NodeOutput hH child constant eps Bsrc control degree boxes)
    (parent : ReachableNode C j) (hunit : child.unit≤parent.unit) :
    (out.parentTraced parent hunit).family.value=out.family.value :=
  TracedSuffixFamily.rebaseToParent_value parent hunit ⟨out.family,out.path⟩

/-- Bind the actual continuation multiplier to the literal native row
multiplier while keeping the same terminal payload and chronology. -/
def parentFamilyAtRoot {child : ReachableNode C k}
    {constant eps Bsrc : ℝ} {control : Finset (ℕ×ℕ)} {degree : ℕ} {boxes : ℕ→Finset (Fin 4→ℤ)}
    (out : NodeOutput hH child constant eps Bsrc control degree boxes)
    (parent : ReachableNode C j) (hunit : child.unit≤parent.unit)
    (v : O) (hv : child.presentation.mult=v) :
    SuffixFamily (hH:=hH) k.val (4-k.val) C.etaSeed parent.localBase C.Bnorm C.Tz v :=
  suffixFamilyRootEq hv (out.parentTraced parent hunit).family

theorem parentFamilyAtRoot_value {child : ReachableNode C k}
    {constant eps Bsrc : ℝ} {control : Finset (ℕ×ℕ)} {degree : ℕ} {boxes : ℕ→Finset (Fin 4→ℤ)}
    (out : NodeOutput hH child constant eps Bsrc control degree boxes)
    (parent : ReachableNode C j) (hunit : child.unit≤parent.unit)
    (v : O) (hv : child.presentation.mult=v) :
    (out.parentFamilyAtRoot parent hunit v hv).value=out.family.value := out.parentTraced_value parent hunit

end NodeOutput
end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.NodeOutput.parentFamilyAtRoot_value
