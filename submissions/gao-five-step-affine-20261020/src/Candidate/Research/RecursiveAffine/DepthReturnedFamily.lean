/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.RegionalReturned

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153SourceReturn
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63Moment

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Terminal depths have their own fixed finite dictionaries. A future
source constructor supplies literal physical prefixes and original edge
weights; this type does not assert that it has supplied them. -/
structure DepthReturnedFamily {Depth : Type} [Fintype Depth]
    (junction : Depth→ℝ) (Base : Depth→Type)
    (base : (d : Depth)→Character→Base d→Character)
    (eta : Character) (Z Bnorm T : ℝ) (root : O) where
  Prefix : Depth→Type
  [prefixFintype : ∀d,Fintype (Prefix d)]
  multiplier : (d : Depth)→Prefix d→O
  root_divides : ∀d p,root∣multiplier d p
  historyMissing : (d : Depth)→Prefix d→ℝ
  historyMissing_nonneg : ∀d p,0≤historyMissing d p
  part : (d : Depth)→(p : Prefix d)→
    ReturnedPartAt M H hH (junction d) (base d) eta Z Bnorm T (multiplier d p)
  weight : (d : Depth)→Prefix d→ℝ
  weight_nonneg : ∀d p,0≤weight d p

attribute [instance] DepthReturnedFamily.prefixFintype
variable {M H hH}

def DepthReturnedFamily.value {Depth : Type} [Fintype Depth]
    {junction : Depth→ℝ} {Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}
    {eta : Character} {Z Bnorm T : ℝ} {root : O}
    (F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root) : ℝ :=
  ∑d,∑p,F.weight d p*(F.part d p).value

theorem DepthReturnedFamily.value_nonneg {Depth : Type} [Fintype Depth]
    {junction : Depth→ℝ} {Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}
    {eta : Character} {Z Bnorm T : ℝ} {root : O}
    (F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root) (hZ : 0≤Z) :
    0≤F.value :=
  Finset.sum_nonneg (fun d _=>Finset.sum_nonneg (fun p _=>
    mul_nonneg (F.weight_nonneg d p) ((F.part d p).value_nonneg hZ)))

/-- Attach the actual own-HIGH part and the finitely many deeper physical
source families. The depth dictionary extends, every child prefix remains
literal, and the new missing radical and edge coefficient are retained. -/
def DepthReturnedFamily.attach {Depth I : Type} [Fintype Depth] [Fintype I]
    {junction : Depth→ℝ} {Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}
    {eta : Character} {Z Bnorm T : ℝ} {root : O}
    {qOwn : ℝ} {OwnBase : Type} {ownBase : Character→OwnBase→Character}
    (own : ReturnedPartAt M H hH qOwn ownBase eta Z Bnorm T root)
    (ownWeight : ℝ) (hOwnWeight : 0≤ownWeight)
    (childRoot : I→O) (hChildRoot : ∀r,root∣childRoot r)
    (children : (r : I)→DepthReturnedFamily M H hH junction Base base eta Z Bnorm T (childRoot r))
    (edge missing : I→ℝ) (hEdge : ∀r,0≤edge r) (hMissing : ∀r,0 ≤ missing r) :
    DepthReturnedFamily M H hH (fun d : Option Depth=>match d with | none=>qOwn | some j=>junction j)
      (fun d : Option Depth=>match d with | none=>OwnBase | some j=>Base j)
      (fun d=>match d with | none=>ownBase | some j=>base j) eta Z Bnorm T root where
  Prefix := fun d=>match d with | none=>Unit | some j=>Σr : I,(children r).Prefix j
  prefixFintype := fun d=>by cases d <;> infer_instance
  multiplier := fun d=>Option.rec (fun _ : Unit=>root)
    (fun j p=>(children p.1).multiplier j p.2) d
  root_divides := fun d=>by
    cases d with
    | none => intro p;exact dvd_refl root
    | some j => intro p;exact (hChildRoot p.1).trans ((children p.1).root_divides j p.2)
  historyMissing := fun d=>Option.rec (fun _ : Unit=>(0:ℝ))
    (fun j p=>missing p.1+(children p.1).historyMissing j p.2) d
  historyMissing_nonneg := fun d=>by
    cases d with
    | none => intro p;exact le_rfl
    | some j => intro p;exact add_nonneg (hMissing p.1) ((children p.1).historyMissing_nonneg j p.2)
  part := fun d=>Option.rec (fun _ : Unit=>own)
    (fun j p=>(children p.1).part j p.2) d
  weight := fun d=>Option.rec (fun _ : Unit=>ownWeight)
    (fun j p=>edge p.1*(children p.1).weight j p.2) d
  weight_nonneg := fun d=>by
    cases d with
    | none => intro p;exact hOwnWeight
    | some j => intro p;exact mul_nonneg (hEdge p.1) ((children p.1).weight_nonneg j p.2)

theorem DepthReturnedFamily.value_attach {Depth I : Type} [Fintype Depth] [Fintype I]
    {junction : Depth→ℝ} {Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}
    {eta : Character} {Z Bnorm T : ℝ} {root : O}
    {qOwn : ℝ} {OwnBase : Type} {ownBase : Character→OwnBase→Character}
    (own : ReturnedPartAt M H hH qOwn ownBase eta Z Bnorm T root)
    (ownWeight : ℝ) (hOwnWeight : 0≤ownWeight)
    (childRoot : I→O) (hChildRoot : ∀r,root∣childRoot r)
    (children : (r : I)→DepthReturnedFamily M H hH junction Base base eta Z Bnorm T (childRoot r))
    (edge missing : I→ℝ) (hEdge : ∀r,0≤edge r) (hMissing : ∀r,0 ≤ missing r) :
    (DepthReturnedFamily.attach own ownWeight hOwnWeight childRoot hChildRoot children edge missing hEdge hMissing).value=
      ownWeight*own.value+∑r,edge r*(children r).value := by
  unfold DepthReturnedFamily.value
  rw [Fintype.sum_option]
  change (∑ _ : Unit, ownWeight*own.value) +
    (∑ j,∑ p : Σr : I,(children r).Prefix j,
      (edge p.1*(children p.1).weight j p.2)*((children p.1).part j p.2).value) = _
  simp only [Fintype.sum_unique, Fintype.sum_sigma]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Finset.mul_sum,mul_assoc]

end
end OAI.SevenEighths.Cycle153SourceReturn

#print axioms OAI.SevenEighths.Cycle153SourceReturn.DepthReturnedFamily.value_attach
