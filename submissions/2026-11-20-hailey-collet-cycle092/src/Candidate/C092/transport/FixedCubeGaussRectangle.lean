/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussPhysical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.Cycle092.SignedCenter
open CenteredMomentTwist EisensteinSchwartzPoisson CenteredMomentLattice CenteredMomentSourceRectangle CenteredMomentRectangle
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

lemma prefixed_norm_scale (d I : Id) (x : ℝ) :
    (Ideal.absNorm (d*I) : ℝ)/x=(Ideal.absNorm I : ℝ)/(x/(Ideal.absNorm d : ℝ)) := by
  simp only [map_mul,Nat.cast_mul,div_div_eq_mul_div]
  ring

lemma ordinaryProfile_upper_support (P : OrdinaryProfile) (b : ℝ) (hb : P.b≤b) :
    Function.support P.normalized ⊆ Set.Iic b :=
  (normPowerProfile_support P.W P.a P.b P.ha P.hs P.hW P.t).trans
    (fun _ hx=>(P.hs hx).2.trans hb)

lemma ordinaryProfile_zero (P : OrdinaryProfile) : P.normalized 0=0 := by
  by_contra h
  have hh := (normPowerProfile_support P.W P.a P.b P.ha P.hs P.hW P.t) h
  exact (not_le_of_gt P.ha) (P.hs hh).1

/-- Exact signed physical rectangle, shortened by the actual ordinary
prefixes. It keeps each original profile height and both separate scale arms. -/
theorem canonicalPair_rectangle_eq_physical (D : FixedCubeDatum) (P₁ P₂ : OrdinaryProfile)
    (M K : Id) (hM : M≠0) (hK : K≠0) (hMK : M∣K)
    (b X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0)
    (hb₁ : P₁.b≤b) (hb₂ : P₂.b≤b)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) :
    (∑I : plainSupportPool b (X₁/(Ideal.absNorm d.1 : ℝ)) (Y₁/(Ideal.absNorm d.1 : ℝ)),
      ∑J : plainSupportPool b (X₂/(Ideal.absNorm d.2 : ℝ)) (Y₂/(Ideal.absNorm d.2 : ℝ)),
        canonicalPairCoefficient D.row.χ K I J*
        idealRectangle P₁.normalized P₂.normalized X₁ X₂ Y₁ Y₂ (d.1*I) (d.2*J))=
      fixedCubePhysicalSource D D P₁ P₂
        (fixedCubeBad D D (residualSuppliers M∪residualHoles K))
        (supplyingResidualPairs D.row D.row (residualSuppliers M) (residualHoles K) (residualHoles K))
        (X₁/(Ideal.absNorm d.1 : ℝ)) (X₂/(Ideal.absNorm d.2 : ℝ))-
      fixedCubePhysicalSource D D P₁ P₂
        (fixedCubeBad D D (residualSuppliers M∪residualHoles K))
        (supplyingResidualPairs D.row D.row (residualSuppliers M) (residualHoles K) (residualHoles K))
        (Y₁/(Ideal.absNorm d.1 : ℝ)) (Y₂/(Ideal.absNorm d.2 : ℝ)) := by
  have hn₁ : 0<(Ideal.absNorm d.1 : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hd.1)
  have hn₂ : 0<(Ideal.absNorm d.2 : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hd.2)
  have hc₁ := plainSupportPool_coverage P₁.normalized b
    (X₁/(Ideal.absNorm d.1 : ℝ)) (Y₁/(Ideal.absNorm d.1 : ℝ))
    (ordinaryProfile_zero P₁) (ordinaryProfile_upper_support P₁ b hb₁)
    (div_pos hX₁ hn₁) (div_pos hY₁ hn₁)
  have hc₂ := plainSupportPool_coverage P₂.normalized b
    (X₂/(Ideal.absNorm d.2 : ℝ)) (Y₂/(Ideal.absNorm d.2 : ℝ))
    (ordinaryProfile_zero P₂) (ordinaryProfile_upper_support P₂ b hb₂)
    (div_pos hX₂ hn₂) (div_pos hY₂ hn₂)
  let f : Id→Id→ℂ := fun I J=>canonicalPairCoefficient D.row.χ K I J
  have hx₁ : ∀I,P₁.normalized ((Ideal.absNorm I : ℝ)/(X₁/(Ideal.absNorm d.1 : ℝ)))≠0→
      I∈plainSupportPool b (X₁/(Ideal.absNorm d.1 : ℝ)) (Y₁/(Ideal.absNorm d.1 : ℝ)) := by
    intro I hi
    exact hc₁ I (Or.inl (by simpa only [one_mul] using hi))
  have hy₁ : ∀I,P₁.normalized ((Ideal.absNorm I : ℝ)/(Y₁/(Ideal.absNorm d.1 : ℝ)))≠0→
      I∈plainSupportPool b (X₁/(Ideal.absNorm d.1 : ℝ)) (Y₁/(Ideal.absNorm d.1 : ℝ)) := by
    intro I hi
    exact hc₁ I (Or.inr (by simpa only [one_mul] using hi))
  have hx₂ : ∀J,P₂.normalized ((Ideal.absNorm J : ℝ)/(X₂/(Ideal.absNorm d.2 : ℝ)))≠0→
      J∈plainSupportPool b (X₂/(Ideal.absNorm d.2 : ℝ)) (Y₂/(Ideal.absNorm d.2 : ℝ)) := by
    intro J hj
    exact hc₂ J (Or.inl (by simpa only [one_mul] using hj))
  have hy₂ : ∀J,P₂.normalized ((Ideal.absNorm J : ℝ)/(Y₂/(Ideal.absNorm d.2 : ℝ)))≠0→
      J∈plainSupportPool b (X₂/(Ideal.absNorm d.2 : ℝ)) (Y₂/(Ideal.absNorm d.2 : ℝ)) := by
    intro J hj
    exact hc₂ J (Or.inr (by simpa only [one_mul] using hj))
  simp only [idealRectangle,prefixed_norm_scale,mul_sub,←mul_assoc,
    Finset.sum_sub_distrib]
  rw [finite_physical_arm _ _ f _ _ _ _ hx₁ hx₂,
      finite_physical_arm _ _ f _ _ _ _ hy₁ hy₂]
  congr 1 <;> apply tsum_congr <;> intro p <;>
    simp only [physicalPairTerm,f,canonicalPairCoefficient_eq_physical D M K hM hK hMK]

#print axioms canonicalPair_rectangle_eq_physical
end
end QRH.Cycle092.FixedCubeGauss
