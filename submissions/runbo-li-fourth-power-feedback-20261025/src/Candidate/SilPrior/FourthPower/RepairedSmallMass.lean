/- Copyright (c) 2026 Sil. Apache-2.0.
Empty-selection scalar and the EXACT shared supplier Cauchy mass. This is
finite assembly: it introduces no branchwise Cauchy and no source estimate.

-/
import Candidate.SilPrior.FourthPower.RepairedSmallSupplier
import Candidate.SilPrior.FourthPower.RepairedSupplierSplit

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.RepairedSmallMass
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open MixedPrincipalPair MixedSupplierFourthRow MixedSupplierPositive MixedSupplierSource
open OuterFreshSource OuterFreshSelected OuterFreshCutoffAllowance
open RepairedRawSupplier RepairedSupplierSplit RepairedSmallEmptyGauss
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

theorem empty_active_card_eq (q : Data ι) (hJ : q.J=∅) : (activeSelected q).card=1 := by
  let y : Selected q := fun j => False.elim (by simpa only [hJ,Finset.notMem_empty] using j.property)
  have hy : y∈activeSelected q := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_⟩
    · intro i j he
      exact False.elim (by simpa only [hJ,Finset.notMem_empty] using i.property)
    · rw [empty_selected_weight q hJ y]
      exact one_ne_zero
  have hp := Finset.card_pos.mpr ⟨y,hy⟩
  exact le_antisymm (empty_active_card q hJ) (by omega)

theorem empty_selected_volume (q : Data ι) (hJ : q.J=∅) : selectedVolume q=1 := by
  unfold selectedVolume
  apply Finset.prod_eq_one
  intro j hj
  exact False.elim (by simpa only [hJ,Finset.notMem_empty] using j.property)

theorem empty_selected_scale (q : Data ι) (hJ : q.J=∅) : MixedSelectedVolume.scale q=1 := by
  have hn : Fintype.card q.J=0 := by simp only [Fintype.card_coe,hJ,Finset.card_empty]
  have hv : MixedSelectedVolume.volume q=1 := empty_selected_volume q hJ
  simp only [MixedSelectedVolume.scale,MixedSelectedVolume.padding,hn,pow_zero,hv,one_mul]

theorem empty_raw_cost (q : Data ι) (hJ : q.J=∅) (x : Frozen q) (seed : Id) :
    rawSupplierCost q x seed=
      (‖MixedSupplierFourthRow.frozenWeight q x‖^2*256)/(frozenVolume q*(seed.absNorm:ℝ)) := by
  rw [rawSupplierCost,empty_active_card_eq q hJ,empty_selected_scale q hJ,
    empty_selected_volume q hJ]
  simp only [Nat.cast_one,mul_one,one_pow]

/-- The full supplier cardinality is already in supplierBranch and in
the proved mass supplier. No second Cauchy is performed on this subfamily. -/
theorem uniform_branch_of_raw_cost (N : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type u} [Fintype ι],Fintype.card ι≤N →
      ∀a b : ℝ,∀s : Source ι a b,∀ha : 0<a,∀u : Id,Squarefree u →
      ∀J : (L : Finset ι) → Finset {i // i∉Lᶜ},∀Kslot : ℝ,1≤Kslot → (∀i,s.M i≤Kslot) →
      ∀branch : Finset ι → Prop,∀(τ : Character)(v K : ℝ)(rows : Finset O)(A : ℝ),0≤A →
      (∀p : SupplierIndex s ha u J,branch p.1 →
        finiteSupplierEnergy s ha u J p τ v K rows≤
          A*rawSupplierCost (supplierData s ha u p.1 (J p.1)) p.2.val
            (residualSeed (supplierData s ha u p.1 (J p.1)) p.2)) →
      supplierBranch s ha u J branch τ v K rows≤
        A*(C*Kslot^(2*N)*(u.absNorm:ℝ)^δ/(u.absNorm:ℝ)) := by
  obtain ⟨C,hC,hmass⟩ := uniform_raw_supplier_cauchy_mass N δ hδ
  refine ⟨C,hC,?_⟩
  intro ι instι hcard a b s ha u hu J Kslot hKslot hM branch τ v K rows A hA hterm
  have hpoint (p : SupplierIndex s ha u J) :
      (if branch p.1 then finiteSupplierEnergy s ha u J p τ v K rows else 0)≤
      A*rawSupplierCost (supplierData s ha u p.1 (J p.1)) p.2.val
        (residualSeed (supplierData s ha u p.1 (J p.1)) p.2) := by
    split_ifs with hp
    · exact hterm p hp
    · exact mul_nonneg hA (rawSupplierCost_nonneg _
        (fun i=>zero_lt_one.trans_le (s.hP i)) _ _)
  have hsum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=Finset.univ) (fun p _ => hpoint p))
    (Nat.cast_nonneg (Fintype.card (SupplierIndex s ha u J)))
  apply hsum.trans
  have hm := mul_le_mul_of_nonneg_left (hmass hcard a b s ha u hu J Kslot hKslot hM) hA
  convert hm using 1
  · rw [Fintype.sum_sigma]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro L hL
    apply Finset.sum_congr rfl
    intro x hx
    ring

end
end Candidate.SilPrior.FourthPower.RepairedSmallMass
