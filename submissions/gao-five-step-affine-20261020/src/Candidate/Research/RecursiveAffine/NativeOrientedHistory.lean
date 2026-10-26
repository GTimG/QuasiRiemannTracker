/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ReachableNode
import Candidate.Research.RecursiveAffine.ActualFamilyRebase
import Candidate.Research.RecursiveAffine.AttachedFamilyHistory
import Candidate.Research.RecursiveAffine.ActualReturnShift
import Candidate.Research.RecursiveAffine.NativeCommonForest

set_option autoImplicit false
set_option maxHeartbeats 650000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63Moment Cycle153SourceReturn Cycle153Reachable Cycle153JointCount

variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}

/-- Literal orientation-sensitive chronology of an actual finite family.
Unlike the node form, this representation also applies after a genuine
base rebase. It contains no estimate of cardinality, weight or energy. -/
structure OrientedFamilyHistory
    {Depth : Type} [Fintype Depth] {junction : Depth→ℝ} {Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character} {eta : Character}
    {Z Bnorm T : ℝ} {root : O}
    (F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root)
    (n : Depth→ℕ)(Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ)) where
  word : (d : Depth)→F.Prefix d→OrientationWord
  word_padding : ∀d p k,n d ≤ k.val→word d p k=false
  units : OrientationWord→∀k,History k→FirstSourceLabel→O
  code : (d : Depth)→F.Prefix d→History (n d)
  injective : ∀d,Function.Injective (fun p=>(word d p,code d p))
  multiplier : ∀d p,F.multiplier d p=
    historyMultiplier (units (word d p)) (wordLeft (word d p)) root (n d) (code d p)
  missing : ∀d p,F.historyMissing d p=historyMissing (wordLeft (word d p)) Z (n d) (code d p)
  facts : ∀d p,HistoryFacts (units (word d p)) (wordLeft (word d p)) root Z Bsrc boxes (n d) (code d p)

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
  {C : SourceContext (α:=alpha) M H} {j : Fin 4}

def OrientedFamilyHistory.ofNode (N : ReachableNode C j) (F : N.Family hH)
    {Bsrc : ℝ}{boxes : ℕ→Finset (Fin 4→ℤ)}
    (history : ForestChronology hH N F Bsrc boxes) :
    OrientedFamilyHistory F (suffixOffset (4-j.val)) Bsrc boxes :=
  ⟨history.word,history.word_padding,history.units,history.code,history.injective,
    history.multiplier,history.missing,history.facts⟩

def OrientedFamilyHistory.toNode (N : ReachableNode C j) (F : N.Family hH)
    {Bsrc : ℝ}{boxes : ℕ→Finset (Fin 4→ℤ)}
    (history : OrientedFamilyHistory F (suffixOffset (4-j.val)) Bsrc boxes) :
    ForestChronology hH N F Bsrc boxes :=
  ⟨history.word,history.word_padding,history.units,history.code,history.injective,
    history.multiplier,history.missing,history.facts⟩

/-- Enlarging the representation base enlarges only the actual source
norm cap. All arithmetic identities, support conditions and dyads remain
literal. -/
theorem historyFacts_enlarge_base
    (units : ∀k,History k→FirstSourceLabel→O)(lefts : ℕ→Bool)(root : O)
    (Zsmall Zlarge B : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))
    (hcap : Zsmall^B ≤ Zlarge^B) :
    ∀n p,HistoryFacts units lefts root Zsmall B boxes n p→
      HistoryFacts units lefts root Zlarge B boxes n p := by
  intro n
  induction n with
  | zero=>intro p hp;trivial
  | succ n ih=>
    intro p hp
    refine ⟨ih p.1 hp.1,?_⟩
    let old:=hp.2
    exact ⟨⟨old.source.nonzero,old.source.multiplier_cap.trans hcap,
      old.source.supported,old.source.same_support,old.source.row_cap.trans hcap,
      old.source.ideal_cap.1.trans hcap,old.source.ideal_cap.2.1.trans hcap,
      old.source.ideal_cap.2.2.1.trans hcap,old.source.ideal_cap.2.2.2.trans hcap⟩,
      old.seed_squarefree,old.seed_divides,old.dyad_mem⟩

/-- Missing radical logarithms acquire the actual physical rebase unit.
The multiplier itself and its accumulated radical factors do not change. -/
theorem historyMissing_rebase
    (lefts : ℕ→Bool)(Z power : ℝ)(hZ : 0<Z)(hp : 0<power) :
    ∀n p,power*historyMissing lefts (Z^power) n p=historyMissing lefts Z n p := by
  intro n
  induction n with
  | zero=>intro p;simp only [historyMissing,mul_zero]
  | succ n ih=>
    intro p
    simp only [historyMissing,mul_add,ih]
    congr 1
    unfold stepMissing Real.logb
    rw [Real.log_rpow hZ]
    rw [mul_div_assoc',mul_div_mul_left _ _ hp.ne']

/-- Preserve the SAME actual forest chronology under native widening and
base rebase. Source norm caps are enlarged by `power ≤ 1`; historical
missing logs are multiplied by `power`, exactly as in the native family. -/
def OrientedFamilyHistory.rebase
    {Depth : Type} [Fintype Depth] {junction : Depth→ℝ} {Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}{eta : Character}
    {Z Bnorm T power : ℝ}{root : O}
    (hZ : 1<Z)(hp : 0<power)(hp1 : power ≤ 1)(hBnorm : 0 ≤ Bnorm)
    (F : DepthReturnedFamily M H hH junction Base base eta (Z^power) Bnorm T root)
    {n : Depth→ℕ}{Bsrc : ℝ}{boxes : ℕ→Finset (Fin 4→ℤ)}
    (hBsrc : 0 ≤ Bsrc)(history : OrientedFamilyHistory F n Bsrc boxes) :
    OrientedFamilyHistory (rebaseDepthReturnedFamily hZ hp hp1 hBnorm F) n Bsrc boxes where
  word:=history.word
  word_padding:=history.word_padding
  units:=history.units
  code:=history.code
  injective:=history.injective
  multiplier:=history.multiplier
  missing:=by
    intro d p
    change power*F.historyMissing d p=_
    rw [history.missing d p]
    exact historyMissing_rebase _ _ _ (zero_lt_one.trans hZ) hp _ _
  facts:=by
    intro d p
    apply historyFacts_enlarge_base _ _ _ (Z^power) Z Bsrc boxes _ _ _ (history.facts d p)
    rw [←Real.rpow_mul (zero_lt_one.trans hZ).le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp1 hBsrc

/-- A literal empty returned family has vacuous actual history. This is
used only when the physical operator has no returned contribution. -/
def OrientedFamilyHistory.empty
    {Depth : Type} [Fintype Depth] {junction : Depth→ℝ} {Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}{eta : Character}
    {Z Bnorm T : ℝ}{root : O}(n : Depth→ℕ)(Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ)) :
    OrientedFamilyHistory
      (emptyReturnedForest (M:=M) (H:=H) (hH:=hH) (junction:=junction) (Base:=Base)
        (base:=base) (eta:=eta) (Z:=Z) (Bnorm:=Bnorm) (Tz:=T) (root:=root)) n Bsrc boxes where
  word:=fun _ p=>nomatch p
  word_padding:=fun _ p=>nomatch p
  units:=fun _ _ _ _=>1
  code:=fun _ p=>nomatch p
  injective:=fun _ p=>nomatch p
  multiplier:=fun _ p=>nomatch p
  missing:=fun _ p=>nomatch p
  facts:=fun _ p=>nomatch p

/-- A genuine operator shell loss changes terminal record exponent/loss,
while every physical chronology field remains the same actual source. -/
def OrientedFamilyHistory.shift
    {Depth : Type} [Fintype Depth] {junction : Depth→ℝ} {Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}{eta : Character}
    {Z Bnorm T : ℝ}{root : O}
    (F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root)(shift : ℝ)
    {n : Depth→ℕ}{Bsrc : ℝ}{boxes : ℕ→Finset (Fin 4→ℤ)}
    (history : OrientedFamilyHistory F n Bsrc boxes) :
    OrientedFamilyHistory (shiftedReturnedForest F shift) n Bsrc boxes :=
  ⟨history.word,history.word_padding,history.units,history.code,history.injective,
    history.multiplier,history.missing,history.facts⟩

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.OrientedFamilyHistory.rebase
