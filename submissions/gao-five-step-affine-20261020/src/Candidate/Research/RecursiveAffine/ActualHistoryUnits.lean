/- Literal chronological units for attached actual source families. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.HistoryPrepend

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open scoped Classical
open HeckeFamily Cycle63Moment

/-- Extend the actual daughter units to one global function on full physical
histories. Off the image of the actual source tree the choice is immaterial.
No source configuration, residual attainer or deleted subset is counted. -/
def graftHistoryUnits {I : Type} (key : I→DecoratedPrefix)
    (ownUnit : FirstSourceLabel→O)
    (childUnits : I→(∀k,History k→FirstSourceLabel→O)) :
    ∀k,History k→FirstSourceLabel→O
  | 0, _ => ownUnit
  | k+1, p =>
    if h : ∃ t : I×History k,prependHistory k (key t.1) t.2=p then
      childUnits (Classical.choose h).1 k (Classical.choose h).2
    else fun _=>1

theorem graftHistoryUnits_zero {I : Type} (key : I→DecoratedPrefix)
    (ownUnit : FirstSourceLabel→O) (childUnits : I→(∀k,History k→FirstSourceLabel→O))
    (p : History 0) : graftHistoryUnits key ownUnit childUnits 0 p=ownUnit := rfl

/-- Injection of the physical key makes the unit at an actual daughter
prefix precisely that daughter's unit; no independent global-unit premise. -/
theorem graftHistoryUnits_child {I : Type} (key : I→DecoratedPrefix)
    (hkey : Function.Injective key) (ownUnit : FirstSourceLabel→O)
    (childUnits : I→(∀k,History k→FirstSourceLabel→O))
    (r : I) (k : ℕ) (p : History k) :
    graftHistoryUnits key ownUnit childUnits (k+1) (prependHistory k (key r) p)=
      childUnits r k p := by
  let h : ∃t : I×History k,prependHistory k (key t.1) t.2=prependHistory k (key r) p :=
    ⟨(r,p),rfl⟩
  have hc := Classical.choose_spec h
  have he := @prependHistory_pair_injective k
    (key (Classical.choose h).1,(Classical.choose h).2) (key r,p) hc
  have ht : Classical.choose h=(r,p) :=
    Prod.ext (hkey (congrArg Prod.fst he)) (congrArg (fun t : DecoratedPrefix×History k=>t.2) he)
  simp only [graftHistoryUnits,dite_eq_left h]
  rw [ht]

/-- The attached chronological global multiplier is exactly the daughter
multiplier at the literal native child root. -/
theorem historyMultiplier_graft {I : Type} (key : I→DecoratedPrefix)
    (hkey : Function.Injective key) (ownUnit : FirstSourceLabel→O)
    (childUnits : I→(∀k,History k→FirstSourceLabel→O))
    (lefts : ℕ→Bool) (root : O) (r : I) (n : ℕ) (p : History n) :
    historyMultiplier (graftHistoryUnits key ownUnit childUnits) lefts root (n+1)
      (prependHistory n (key r) p)=
    historyMultiplier (childUnits r) (fun k=>lefts (k+1))
      (childMultiplier (lefts 0) root ownUnit (key r).1) n p := by
  have h:=historyMultiplier_prepend (graftHistoryUnits key ownUnit childUnits) lefts root (key r) n p
  have hu : (fun k p=>graftHistoryUnits key ownUnit childUnits (k+1)
      (prependHistory k (key r) p))=childUnits r := by
    funext k p
    exact graftHistoryUnits_child key hkey ownUnit childUnits r k p
  rw [hu] at h
  exact h

/-- Native support, norm, missing-radical and dyad facts of an actual
parent and its actual child history give the facts for the attached full
history. The unit function is constructed from that tree, not assumed. -/
theorem historyFacts_graft {I : Type} (key : I→DecoratedPrefix)
    (hkey : Function.Injective key) (ownUnit : FirstSourceLabel→O)
    (childUnits : I→(∀k,History k→FirstSourceLabel→O))
    (lefts : ℕ→Bool) (root : O) (Z B : ℝ) (boxes : ℕ→Finset (Fin 4→ℤ))
    (r : I)
    (hown : DecoratedFacts (fun _ : Unit=>root) (lefts 0) (fun _=>ownUnit)
      Z B (boxes 0) ((),key r)) :
    ∀n (p : History n),
      HistoryFacts (childUnits r) (fun k=>lefts (k+1))
        (childMultiplier (lefts 0) root ownUnit (key r).1) Z B (fun k=>boxes (k+1)) n p →
      HistoryFacts (graftHistoryUnits key ownUnit childUnits) lefts root Z B boxes (n+1)
        (prependHistory n (key r) p) := by
  intro n
  induction n with
  | zero =>
    intro p _
    refine ⟨trivial,?_⟩
    have hu : graftHistoryUnits key ownUnit childUnits 0=(fun _ : Unit=>ownUnit) := by
      funext p
      rfl
    change DecoratedFacts (fun _ : Unit=>root) (lefts 0)
      (graftHistoryUnits key ownUnit childUnits 0) Z B (boxes 0) ((),key r)
    rw [hu]
    exact hown
  | succ n ih =>
    intro p hp
    refine ⟨ih p.1 hp.1,?_⟩
    have old:=hp.2
    refine ⟨?_,old.seed_squarefree,old.seed_divides,old.dyad_mem⟩
    refine ⟨?_,?_,old.source.supported,old.source.same_support,?_,old.source.ideal_cap⟩
    · simpa only [appendMultiplier,forgetDecoration,prependHistory,historyMultiplier_graft key hkey,
        graftHistoryUnits_child key hkey] using old.source.nonzero
    · simpa only [appendMultiplier,forgetDecoration,prependHistory,historyMultiplier_graft key hkey,
        graftHistoryUnits_child key hkey] using old.source.multiplier_cap
    · simpa only [appendMultiplier,forgetDecoration,prependHistory,historyMultiplier_graft key hkey,
        graftHistoryUnits_child key hkey] using old.source.row_cap

end
end OAI.SevenEighths.Cycle153JointCount
#print axioms OAI.SevenEighths.Cycle153JointCount.historyFacts_graft
