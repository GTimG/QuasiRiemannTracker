/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.NaturalSharedTables

/-! Exact rank-one removal of the original diagonal at a fixed shared table.
The two exceptional unit masks belong to their own residual row vectors.
This does not license an arbitrary bounded pair mask in the Mellin estimate.
-/
namespace Qrh.JointDetector.NaturalDiagonalMask
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve
open NaturalSelectedNorm NaturalSharedTables

def unitTuple : ColourTuple := fun _ => 1

theorem leftResidual_self (c : ColourTuple) (hc : ∀ j, Admissible (c j))
    (hp : Pairwise (fun j k => IsCoprime (c j) (c k))) : leftResidual c c=unitTuple := by
  funext j
  exact isUnit_iff_eq_one.mp ((leftResidual_coprime_right hc hp j j).isUnit_of_dvd
    (leftResidual_dvd hp j))

theorem rightResidual_self (c : ColourTuple) (hc : ∀ j, Admissible (c j))
    (hp : Pairwise (fun j k => IsCoprime (c j) (c k))) : rightResidual c c=unitTuple := by
  funext j
  exact isUnit_iff_eq_one.mp ((rightResidual_coprime_left hc hp j j).isUnit_of_dvd
    (rightResidual_dvd hp j))

/-- On the actual residual fibre the original diagonal consists of at most
the single unit/unit point. Its remaining guard is frozen with the table. -/
theorem diagonal_iff_units (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (hpF : ∀ c ∈ F, Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable) (a b : ColourTuple) (hr : (a,b) ∈ residualFibre F g) :
    recoverLeft g a=recoverRight g b ↔ a=unitTuple ∧ b=unitTuple ∧
      recoverLeft g unitTuple=recoverRight g unitTuple := by
  obtain ⟨⟨c,d⟩,hp,he⟩ := Finset.mem_image.mp hr
  have ha : leftResidual c d=a := congrArg Prod.fst he
  have hb : rightResidual c d=b := congrArg Prod.snd he
  subst a
  subst b
  obtain ⟨hp,ht⟩ := Finset.mem_filter.mp hp
  obtain ⟨hc,hd⟩ := Finset.mem_product.mp hp
  have hleft : recoverLeft g (leftResidual c d)=c := by rw [← ht,recover_left (hpF d hd)]
  have hright : recoverRight g (rightResidual c d)=d := by rw [← ht,recover_right (hpF c hc)]
  change recoverLeft g (leftResidual c d)=recoverRight g (rightResidual c d) ↔ _
  constructor
  · intro he
    have hcd : c=d := hleft.symm.trans (he.trans hright)
    subst d
    have ha := leftResidual_self c (hF c hc) (hpF c hc)
    have hb := rightResidual_self c (hF c hc) (hpF c hc)
    refine ⟨ha,hb,?_⟩
    calc
      recoverLeft g unitTuple=recoverLeft g (leftResidual c c) := congrArg (recoverLeft g) ha.symm
      _ = recoverRight g (rightResidual c c) := he
      _ = recoverRight g unitTuple := congrArg (recoverRight g) hb
  · rintro ⟨ha,hb,he⟩
    simpa only [ha,hb] using he

def unitMask (a : ColourTuple) : ℂ := if a=unitTuple then 1 else 0
def tableDiagonal (g : SharedTable) : ℂ :=
  if recoverLeft g unitTuple=recoverRight g unitTuple then 1 else 0

theorem unitMask_norm_le (a : ColourTuple) : ‖unitMask a‖ ≤ 1 := by
  unfold unitMask
  split_ifs <;> norm_num

theorem tableDiagonal_norm_le (g : SharedTable) : ‖tableDiagonal g‖ ≤ 1 := by
  unfold tableDiagonal
  split_ifs <;> norm_num

theorem diagonal_indicator_factor (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (hpF : ∀ c ∈ F, Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable) (a b : ColourTuple) (hr : (a,b) ∈ residualFibre F g) :
    (if recoverLeft g a=recoverRight g b then (1:ℂ) else 0)=
      tableDiagonal g*unitMask a*unitMask b := by
  simp only [diagonal_iff_units F hF hpF g a b hr]
  unfold tableDiagonal unitMask
  split_ifs <;> simp_all

theorem offdiagonal_selector_factor (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (hpF : ∀ c ∈ F, Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable) (a b : ColourTuple) (hr : (a,b) ∈ residualFibre F g) :
    (if recoverLeft g a=recoverRight g b then (0:ℂ) else 1)=
      1-tableDiagonal g*unitMask a*unitMask b := by
  rw [← diagonal_indicator_factor F hF hpF g a b hr]
  split_ifs <;> norm_num

/-- An equality of signed finite sums, before any norm estimate. The second
form is obtained solely by multiplying each own vector by its unit mask. -/
theorem sum_offdiagonal_split (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (hpF : ∀ c ∈ F, Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable) (S : Finset (ColourTuple × ColourTuple))
    (hS : S ⊆ residualFibre F g) (f : ColourTuple × ColourTuple → ℂ) :
    (∑ p ∈ S, if recoverLeft g p.1=recoverRight g p.2 then 0 else f p)=
      (∑ p ∈ S, f p)-tableDiagonal g*(∑ p ∈ S, unitMask p.1*unitMask p.2*f p) := by
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have he := offdiagonal_selector_factor F hF hpF g p.1 p.2 (hS hp)
  have hpoint : (if recoverLeft g p.1=recoverRight g p.2 then (0:ℂ) else 1)*f p=
      f p-tableDiagonal g*(unitMask p.1*unitMask p.2*f p) := by rw [he]; ring
  simpa only [ite_mul,zero_mul,one_mul] using hpoint

/-- Two legitimate vector estimates suffice; no norm monotonicity for a
general entrywise pair selector is asserted. -/
theorem sum_offdiagonal_norm_le (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (hpF : ∀ c ∈ F, Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable) (S : Finset (ColourTuple × ColourTuple))
    (hS : S ⊆ residualFibre F g) (f : ColourTuple × ColourTuple → ℂ) (B : ℝ)
    (hfull : ‖∑ p ∈ S, f p‖ ≤ B)
    (hunit : ‖∑ p ∈ S, unitMask p.1*unitMask p.2*f p‖ ≤ B) :
    ‖∑ p ∈ S, if recoverLeft g p.1=recoverRight g p.2 then 0 else f p‖ ≤ 2*B := by
  rw [sum_offdiagonal_split F hF hpF g S hS f]
  calc
    _ ≤ ‖∑ p ∈ S, f p‖+‖tableDiagonal g*(∑ p ∈ S, unitMask p.1*unitMask p.2*f p)‖ :=
      norm_sub_le _ _
    _ ≤ B+‖∑ p ∈ S, unitMask p.1*unitMask p.2*f p‖ := by
      apply add_le_add hfull
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (tableDiagonal_norm_le g)
    _ ≤ B+B := add_le_add le_rfl hunit
    _ = 2*B := by ring

end
end Qrh.JointDetector.NaturalDiagonalMask

#print axioms Qrh.JointDetector.NaturalDiagonalMask.sum_offdiagonal_split
