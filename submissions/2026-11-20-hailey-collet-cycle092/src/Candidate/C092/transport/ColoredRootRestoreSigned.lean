/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The two actual signed scale arms in one common native divisor expansion.
Adapted from Sil's cube-free restoration; both arms remain inside each norm. -/
import Candidate.C092.transport.ColoredRootRestoreFamily
import Submissions.sil_density_split_20261026.CubeFree.FP.RestorationInverseEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredRootRestore
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open Candidate.FourthPower QRH.SilDensitySplit.CubeFree.FP
open KernelRowExpansion KernelRowProfiles KernelMarkedRows KernelPhysicalScalars
open KernelAssignmentReindex KernelRowPools KernelLabelledSlots RestorationFamily
open RestorationInverseEnergy QRH.Cycle092.RegularColoredForward
local notation "Id" => Ideal HeckeFamily.O
variable {α : Type*} [Fintype α]

/-- The actual signed difference, with the same natural marks and common
finite ordinary domain. Ordinary characters have separate coordinates. -/
def signedRow (inv : Bool) (S : Finset PrimeIdeal) (χ : Character)
    (ω₁ ω₂ : Id →*₀ ℂ) (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (D : Finset IdealPair) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (cX cY : ℂ) : ℂ :=
  cX*weightedSum (naturalCoefficients χ S pool β P) (fun slot =>
    row χ ω₁ ω₂ D (sourceValue inv S slot) W₁ W₂ X₁ X₂) -
  cY*weightedSum (naturalCoefficients χ S pool β P) (fun slot =>
    row χ ω₁ ω₂ D (sourceValue inv S slot) W₁ W₂ Y₁ Y₂)

/-- Literal colored inverse restoration, including the original normalization
of both arms. The live signed difference is never split by a triangle bound. -/
theorem signed_inverse_expansion (S : Finset PrimeIdeal) (χ : Character)
    (ω₁ ω₂ : Id →*₀ ℂ) (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (D : Finset IdealPair) (hnz : ∀ n∈D,n.1≠0 ∧ n.2≠0)
    (hs : ∀ n∈D,pairSupport n.1 n.2 ⊆ primeValues S)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (cX cY : ℂ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) :
    signedRow true S χ ω₁ ω₂ pool β P D W₁ W₂ X₁ X₂ Y₁ Y₂ cX cY =
    ∑ T : Finset α, ∑ t ∈ frozenChoices T S, ∑ d ∈ divisorPool D,
      scalar χ S (ordinarySeriesFor true) (markedSeriesFor true)
        (fun i:T=>pool i.val) (fun i:T=>β i.val) (fun i:T=>P i.val) t d *
      color ω₁ ω₂ d *
      signedRow false S χ ω₁ ω₂ (fun i:{i // i∉T}=>pool i.val)
        (crossBeta T S t β) (fun i=>P i.val) (residualPool D d) W₁ W₂
        (X₁/d.1.absNorm) (X₂/d.2.absNorm) (Y₁/d.1.absNorm) (Y₂/d.2.absNorm) cX cY := by
  unfold signedRow
  rw [natural_inverse_family_expansion S χ ω₁ ω₂ pool β P D hnz hs W₁ W₂ X₁ X₂ hX₁ hX₂,
    natural_inverse_family_expansion S χ ω₁ ω₂ pool β P D hnz hs W₁ W₂ Y₁ Y₂ hY₁ hY₂,
    Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib,frozenChoices,Finset.sum_filter]
  apply Finset.sum_congr (by ext;simp)
  intro t ht
  by_cases hi : Function.Injective t
  · simp only [hi,ite_true]
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [remaining_mask,remaining_mask]
    simp only [childValue,sourceValue,Bool.false_eq_true,ite_true,ite_false]
    ring
  · simp only [hi,ite_false,mul_zero,sub_self]

#print axioms signed_inverse_expansion
end
end QRH.Cycle092.ColoredRootRestore
