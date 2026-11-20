/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussRectangle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.Cycle092.SignedCenter
open QRH.SilDensitySplit.CubeFree.FP MixedCommonRestriction
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

/-- Exact H8 source after every remaining actual mark is frozen. The full
puncture, supplier labels, two original profiles, and all four shortened
scales are explicit. No absolute values have yet been taken. -/
theorem canonicalSource_eq_fixedCubePhysical (D : FixedCubeDatum) (P₁ P₂ : OrdinaryProfile)
    (S H : Finset QRH.Record1252270103KernelMass.PrimeIdeal) (R : Id) (hR : R≠0)
    (pool : ι→Finset Id) (hp : ∀i,∀I∈pool i,I≠0)
    (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (b X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0)
    (hb₁ : P₁.b≤b) (hb₂ : P₂.b≤b)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) :
    MixedCanonicalSource.source D.row.χ S H R pool ν Wslot P P₁.normalized P₂.normalized
      b X₁ X₂ Y₁ Y₂ d=
    ∑p : (i:ι)→pool i,canonicalFrozenScalar D.row.χ R pool ν Wslot P p*
      (let M : Id:=∏i,(p i).val
       let K : Id:=(punctureProduct S H*M)*R
       let bad:=fixedCubeBad D D (residualSuppliers M∪residualHoles K)
       let allowed:=supplyingResidualPairs D.row D.row (residualSuppliers M) (residualHoles K) (residualHoles K)
       fixedCubePhysicalSource D D P₁ P₂ bad allowed
         (X₁/(Ideal.absNorm d.1 : ℝ)) (X₂/(Ideal.absNorm d.2 : ℝ))-
       fixedCubePhysicalSource D D P₁ P₂ bad allowed
         (Y₁/(Ideal.absNorm d.1 : ℝ)) (Y₂/(Ideal.absNorm d.2 : ℝ))) := by
  rw [canonicalSource_frozen_marks]
  apply Finset.sum_congr rfl
  intro p _
  apply congrArg (fun z : ℂ=>canonicalFrozenScalar D.row.χ R pool ν Wslot P p*z)
  have hM : (∏i,(p i).val)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>hp i _ (p i).property)
  have hpuncture : punctureProduct S H≠0 := by
    unfold punctureProduct
    exact Finset.prod_ne_zero_iff.mpr (fun Q _=>Q.property.ne_zero)
  exact canonicalPair_rectangle_eq_physical D P₁ P₂ _ _ hM
    (mul_ne_zero (mul_ne_zero hpuncture hM) hR)
    ⟨punctureProduct S H*R,by ring⟩ b X₁ X₂ Y₁ Y₂ d hd hb₁ hb₂ hX₁ hX₂ hY₁ hY₂

#print axioms canonicalSource_eq_fixedCubePhysical
end
end QRH.Cycle092.FixedCubeGauss
