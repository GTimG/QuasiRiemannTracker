/- Literal histories of the actual attached returned family. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ActualHistoryUnits
import Candidate.Research.RecursiveAffine.DepthReturnedFamily

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63Moment Cycle153SourceReturn

/-- This is provenance of an already constructed source family. The code,
multiplier and missing radical are identities; `facts` are native support,
source norm and dyad facts. There is no cardinality or energy assumption. -/
structure LiteralFamilyHistory {Depth : Type} [Fintype Depth]
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M≤H}
    {junction : Depth→ℝ} {Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}
    {eta : Character} {Z Bnorm T : ℝ} {root : O}
    (F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root)
    (n : Depth→ℕ) (units : ∀k,History k→FirstSourceLabel→O)
    (lefts : ℕ→Bool) (Bsrc : ℝ) (boxes : ℕ→Finset (Fin 4→ℤ)) where
  code : (d : Depth)→F.Prefix d→History (n d)
  injective : ∀d,Function.Injective (code d)
  multiplier : ∀d p,F.multiplier d p=historyMultiplier units lefts root (n d) (code d p)
  missing : ∀d p,F.historyMissing d p=historyMissing lefts Z (n d) (code d p)
  facts : ∀d p,HistoryFacts units lefts root Z Bsrc boxes (n d) (code d p)

/-- Construct the literal chronology on the actual dependent-sum carrier
of `DepthReturnedFamily.attach`. The units of the children are glued by
the injective physical key. Every multiplier and historical missing
radical is proved equal to the one retained by that actual family. -/
def attachLiteralFamilyHistory
    {Depth I : Type} [Fintype Depth] [Fintype I]
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M≤H}
    {junction : Depth→ℝ} {Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}
    {eta : Character} {Z Bnorm T : ℝ} {root : O}
    {qOwn : ℝ} {OwnBase : Type} {ownBase : Character→OwnBase→Character}
    (own : ReturnedPartAt M H hH qOwn ownBase eta Z Bnorm T root)
    (ownWeight : ℝ) (hOwnWeight : 0≤ownWeight)
    (key : I→DecoratedPrefix) (hkey : Function.Injective key)
    (ownUnit : FirstSourceLabel→O) (childUnits : I→(∀k,History k→FirstSourceLabel→O))
    (lefts : ℕ→Bool) (Bsrc : ℝ) (boxes : ℕ→Finset (Fin 4→ℤ))
    (hown : ∀r,DecoratedFacts (fun _ : Unit=>root) (lefts 0) (fun _=>ownUnit)
      Z Bsrc (boxes 0) ((),key r))
    (childRoot : I→O) (hChildRoot : ∀r,root∣childRoot r)
    (hChildMultiplier : ∀r,childRoot r=childMultiplier (lefts 0) root ownUnit (key r).1)
    (children : (r : I)→DepthReturnedFamily M H hH junction Base base eta Z Bnorm T (childRoot r))
    (edge : I→ℝ) (hEdge : ∀r,0≤edge r)
    (hMissing : ∀r,0 ≤ stepMissing (lefts 0) Z (key r).1)
    (n : Depth→ℕ)
    (histories : ∀r,LiteralFamilyHistory (children r) n (childUnits r)
      (fun k=>lefts (k+1)) Bsrc (fun k=>boxes (k+1))) :
    LiteralFamilyHistory
      (DepthReturnedFamily.attach own ownWeight hOwnWeight childRoot hChildRoot children
        edge (fun r=>stepMissing (lefts 0) Z (key r).1) hEdge hMissing)
      (fun d : Option Depth=>match d with | none=>0 | some j=>n j+1)
      (graftHistoryUnits key ownUnit childUnits) lefts Bsrc boxes where
  code := fun d=>Option.rec (fun p : Unit=>p)
    (fun j p=>prependHistory (n j) (key p.1) ((histories p.1).code j p.2)) d
  injective := by
    intro d
    cases d with
    | none => exact Function.injective_id
    | some j =>
      rintro ⟨r,p⟩ ⟨r',p'⟩ h
      have he:=@prependHistory_pair_injective (n j)
        (key r,(histories r).code j p) (key r',(histories r').code j p') h
      have hr:r=r':=hkey (congrArg Prod.fst he)
      cases hr
      have hp:p=p':=(histories r).injective j
        (congrArg (fun t : DecoratedPrefix×History (n j)=>t.2) he)
      exact Sigma.ext rfl (heq_of_eq hp)
  multiplier := by
    intro d
    cases d with
    | none => intro p;rfl
    | some j =>
      intro p
      have hm:=(histories p.1).multiplier j p.2
      have ht:=congrArg (fun v : O=>historyMultiplier (childUnits p.1)
        (fun k=>lefts (k+1)) v (n j) ((histories p.1).code j p.2)) (hChildMultiplier p.1)
      exact (hm.trans ht).trans (historyMultiplier_graft key hkey ownUnit childUnits lefts root p.1 (n j)
        ((histories p.1).code j p.2)).symm
  missing := by
    intro d
    cases d with
    | none => intro p;rfl
    | some j =>
      intro p
      change stepMissing (lefts 0) Z (key p.1).1+(children p.1).historyMissing j p.2=_
      rw [(histories p.1).missing j p.2,historyMissing_prepend]
  facts := by
    intro d
    cases d with
    | none => intro p;trivial
    | some j =>
      intro p
      apply historyFacts_graft key hkey ownUnit childUnits lefts root Z Bsrc boxes p.1 (hown p.1)
      have h:=(histories p.1).facts j p.2
      exact Eq.mp (congrArg (fun v : O=>HistoryFacts (childUnits p.1)
        (fun k=>lefts (k+1)) v Z Bsrc (fun k=>boxes (k+1)) (n j)
        ((histories p.1).code j p.2)) (hChildMultiplier p.1)) h

end
end OAI.SevenEighths.Cycle153JointCount
#print axioms OAI.SevenEighths.Cycle153JointCount.attachLiteralFamilyHistory
