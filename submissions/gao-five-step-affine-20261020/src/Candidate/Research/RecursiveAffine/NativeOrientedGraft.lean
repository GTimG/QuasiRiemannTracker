/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0.
The carrier is the literal native own-plus-LOW dependent sum. -/
import Candidate.Research.RecursiveAffine.NativeOrientedHistory
import Candidate.Research.RecursiveAffine.OrientationPrepend

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63Moment Cycle153SourceReturn Cycle153Reachable Cycle153JointCount

variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}

/-- Graft the actual varying daughter orientations and units into the
literal native dependent-sum carrier. The complete physical row key is
injective, so the unit on every actual descendant is recovered from that
same row. No global common child orientation is assumed, and no metadata
coordinate is appended to the arithmetic history. -/
def OrientedFamilyHistory.attach
    {Depth I : Type} [Fintype Depth] [Fintype I]
    {junction : Depth→ℝ}{Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}{eta : Character}
    {Z Bnorm T : ℝ}{root : O}{qOwn : ℝ}
    {OwnBase : Type}{ownBase : Character→OwnBase→Character}
    (own : ReturnedPartAt M H hH qOwn ownBase eta Z Bnorm T root)
    (ownWeight : ℝ)(hOwnWeight : 0 ≤ ownWeight)
    (key : I→DecoratedPrefix)(hkey : Function.Injective key)
    (left : Bool)(ownUnit : FirstSourceLabel→O)
    (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))
    (hown : ∀r,DecoratedFacts (fun _ : Unit=>root) left (fun _=>ownUnit)
      Z Bsrc (boxes 0) ((),key r))
    (childRoot : I→O)(hChildRoot : ∀r,root∣childRoot r)
    (hChildMultiplier : ∀r,childRoot r=Cycle153JointCount.childMultiplier left root ownUnit (key r).1)
    (children : (r : I)→DepthReturnedFamily M H hH junction Base base eta Z Bnorm T (childRoot r))
    (edge : I→ℝ)(hEdge : ∀r,0 ≤ edge r)
    (hMissing : ∀r,0 ≤ stepMissing left Z (key r).1)
    (n : Depth→ℕ)(hn : ∀d,n d ≤ 3)
    (histories : ∀r,OrientedFamilyHistory (children r) n Bsrc (fun k=>boxes (k+1))) :
    OrientedFamilyHistory
      (DepthReturnedFamily.attach own ownWeight hOwnWeight childRoot hChildRoot children edge
        (fun r=>stepMissing left Z (key r).1) hEdge hMissing)
      (fun d : Option Depth=>match d with | none=>0 | some d=>n d+1) Bsrc boxes where
  word:=fun d=>Option.rec (fun _ : Unit=>(fun _=>false))
    (fun d p=>prependOrientation left ((histories p.1).word d p.2)) d
  word_padding:=by
    intro d
    cases d with
    | none=>intro p k hk;rfl
    | some d=>
      intro p k hk
      exact prepend_orientation_padding left ((histories p.1).word d p.2) (n d)
        ((histories p.1).word_padding d p.2) k hk
  units:=fun word=>graftHistoryUnits key ownUnit (fun r=>(histories r).units (tailOrientation word))
  code:=fun d=>Option.rec (fun p : Unit=>p)
    (fun d p=>prependHistory (n d) (key p.1) ((histories p.1).code d p.2)) d
  injective:=by
    intro d
    cases d with
    | none=>
      intro p p' h
      change @Eq Unit p p'
      exact Subsingleton.elim _ _
    | some d=>
      rintro ⟨r,p⟩ ⟨r',p'⟩ h
      have hpre:=@prependHistory_pair_injective (n d)
        (key r,(histories r).code d p) (key r',(histories r').code d p') (congrArg Prod.snd h)
      have hr : r=r' := hkey (congrArg Prod.fst hpre)
      cases hr
      have hword : (histories r).word d p=(histories r).word d p' :=
        prepend_orientation_injective left _ _
          ((histories r).word_padding d p 3 (by have:=hn d;omega))
          ((histories r).word_padding d p' 3 (by have:=hn d;omega))
          (congrArg Prod.fst h)
      have hcode : (histories r).code d p=(histories r).code d p' :=
        congrArg (fun x : DecoratedPrefix×History (n d)=>x.2) hpre
      have hp : p=p' := (histories r).injective d (Prod.ext hword hcode)
      exact Sigma.ext rfl (heq_of_eq hp)
  multiplier:=by
    intro d
    cases d with
    | none=>intro p;rfl
    | some d=>
      intro p
      let W:=prependOrientation left ((histories p.1).word d p.2)
      have htail : tailOrientation W=(histories p.1).word d p.2 :=
        tail_prepend_orientation left _ ((histories p.1).word_padding d p.2 3 (by have:=hn d;omega))
      have hm : (children p.1).multiplier d p.2=
          historyMultiplier ((histories p.1).units (tailOrientation W))
            (wordLeft (tailOrientation W)) (childRoot p.1) (n d) ((histories p.1).code d p.2) := by
        rw [htail]
        exact (histories p.1).multiplier d p.2
      change (children p.1).multiplier d p.2=
        historyMultiplier (graftHistoryUnits key ownUnit
          (fun r=>(histories r).units (tailOrientation W))) (wordLeft W) root (n d+1)
            (prependHistory (n d) (key p.1) ((histories p.1).code d p.2))
      rw [historyMultiplier_graft key hkey]
      apply hm.trans
      rw [historyMultiplier_tail_orientation _ W _ (n d) (hn d)]
      exact congrArg (fun v : O=>historyMultiplier ((histories p.1).units (tailOrientation W))
        (fun k=>wordLeft W (k+1)) v (n d) ((histories p.1).code d p.2))
        (by simpa only [show wordLeft W 0=left by rfl] using hChildMultiplier p.1)
  missing:=by
    intro d
    cases d with
    | none=>intro p;rfl
    | some d=>
      intro p
      let W:=prependOrientation left ((histories p.1).word d p.2)
      have htail : tailOrientation W=(histories p.1).word d p.2 :=
        tail_prepend_orientation left _ ((histories p.1).word_padding d p.2 3 (by have:=hn d;omega))
      change stepMissing left Z (key p.1).1+(children p.1).historyMissing d p.2=
        historyMissing (wordLeft W) Z (n d+1)
          (prependHistory (n d) (key p.1) ((histories p.1).code d p.2))
      rw [(histories p.1).missing d p.2,←htail,
        historyMissing_tail_orientation W Z (n d) (hn d),historyMissing_prepend]
      rfl
  facts:=by
    intro d
    cases d with
    | none=>intro p;trivial
    | some d=>
      intro p
      let W:=prependOrientation left ((histories p.1).word d p.2)
      have htail : tailOrientation W=(histories p.1).word d p.2 :=
        tail_prepend_orientation left _ ((histories p.1).word_padding d p.2 3 (by have:=hn d;omega))
      change HistoryFacts (graftHistoryUnits key ownUnit
        (fun r=>(histories r).units (tailOrientation W))) (wordLeft W) root Z Bsrc boxes (n d+1)
          (prependHistory (n d) (key p.1) ((histories p.1).code d p.2))
      apply historyFacts_graft key hkey ownUnit _ (wordLeft W) root Z Bsrc boxes p.1
        (by simpa only [show wordLeft W 0=left by rfl] using hown p.1)
      have hchild : HistoryFacts ((histories p.1).units (tailOrientation W))
          (wordLeft (tailOrientation W)) (childRoot p.1) Z Bsrc (fun k=>boxes (k+1))
          (n d) ((histories p.1).code d p.2) := by
        rw [htail]
        exact (histories p.1).facts d p.2
      have hshift:=(historyFacts_tail_orientation _ W (childRoot p.1) Z Bsrc
        (fun k=>boxes (k+1)) (n d) (hn d) ((histories p.1).code d p.2)).mp hchild
      simpa only [hChildMultiplier,show wordLeft W 0=left by rfl] using hshift

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.OrientedFamilyHistory.attach
