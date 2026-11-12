/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.RayQuotient
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.IdealBridge
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Inverse.Restore.Twist — the common child twist `θ' = conj θ · δ · η'`

The restored child slot coefficient carries, on every slot prime `P = (g)`, the character
`conj(χ_θ(P)) · δ(P) · η'(P)` (parent relative ray character conjugated, the deleted base `δ`, the
child row character `η'`). It is ONE ray-class character modulo
`childRay rayM δ η' = rayM · mod δ · mod η'`, trivial on the global units (one common
twist for all slots):

* `pullChar h χ`: a residue character mod `N` pulled back to `O/M'` (`M' ≤ N`), `pullChar_mk`;
* `childTwist rayM H hH θ δ η' ∈ Characters (childRay …) (globalUnits _)`;
* **`childTwist_span`**: for `g` a unit mod `childRay`,
  `idealCoeff (character childRay (globalUnits) le_rfl θ') (g) =
    star (idealCoeff (character rayM H hH θ) (g)) · idealCoeff δ (g) · idealCoeff η' (g)`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical
open OAI OAI.SevenEighths HeckeFamily

local notation "O" => HeckeFamily.O
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-- Pull a residue character modulo `N` back to `O ⧸ M'` (`M' ≤ N`). -/
def pullChar {M' N : Ideal O} (h : M' ≤ N) (χ : MulChar (O ⧸ N) ℂ) : MulChar (O ⧸ M') ℂ :=
  MulChar.ofUnitHom (χ.toUnitHom.comp (Units.map (Ideal.Quotient.factor h).toMonoidHom))

theorem pullChar_mk {M' N : Ideal O} (h : M' ≤ N) (χ : MulChar (O ⧸ N) ℂ) (z : O)
    (hz : IsUnit (Ideal.Quotient.mk M' z)) :
    pullChar h χ (Ideal.Quotient.mk M' z) = χ (Ideal.Quotient.mk N z) := by
  obtain ⟨u, hu⟩ := hz
  rw [← hu, pullChar, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom,
    Units.coe_map]
  change χ (Ideal.Quotient.factor h (u : O ⧸ M')) = _
  rw [hu, Ideal.Quotient.factor_mk]

/-- The child ray modulus `rayM · mod δ · mod η'`. -/
def childRay (rayM : Ideal O) (δ η' : Character) : Ideal O := rayM * δ.modulus * η'.modulus

theorem childRay_ne_zero (rayM : Ideal O) [hr : NeZero rayM] (δ η' : Character) :
    childRay rayM δ η' ≠ 0 := by
  unfold childRay
  rw [Ne, Ideal.zero_eq_bot, Ideal.mul_eq_bot, Ideal.mul_eq_bot, not_or, not_or]
  exact ⟨⟨fun h => hr.out (h.trans Ideal.zero_eq_bot.symm), δ.modulus_ne_bot⟩,
    η'.modulus_ne_bot⟩

instance childRay_neZero (rayM : Ideal O) [NeZero rayM] (δ η' : Character) :
    NeZero (childRay rayM δ η') := ⟨childRay_ne_zero rayM δ η'⟩

theorem childRay_le_ray (rayM : Ideal O) (δ η' : Character) : childRay rayM δ η' ≤ rayM :=
  Ideal.mul_le_left.trans Ideal.mul_le_left

theorem childRay_le_delta (rayM : Ideal O) (δ η' : Character) :
    childRay rayM δ η' ≤ δ.modulus :=
  Ideal.mul_le_left.trans Ideal.mul_le_right

theorem childRay_le_eta (rayM : Ideal O) (δ η' : Character) :
    childRay rayM δ η' ≤ η'.modulus := Ideal.mul_le_right

section
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
local instance (δ η' : Character) : Finite (O ⧸ childRay rayM δ η') :=
  Ring.HasFiniteQuotients.finiteQuotient (childRay_ne_zero rayM δ η')

/-- The common child twist as a residue character modulo `childRay`. -/
def childTwistChar (H : Subgroup (O ⧸ rayM)ˣ) (θ : RayQuotient.Characters rayM H)
    (δ η' : Character) : MulChar (O ⧸ childRay rayM δ η') ℂ :=
  pullChar (childRay_le_ray rayM δ η') (star (θ : MulChar (O ⧸ rayM) ℂ)) *
    pullChar (childRay_le_delta rayM δ η') δ.residue *
    pullChar (childRay_le_eta rayM δ η') η'.residue

theorem childTwistChar_mk (H : Subgroup (O ⧸ rayM)ˣ) (θ : RayQuotient.Characters rayM H)
    (δ η' : Character) (z : O) (hz : IsUnit (Ideal.Quotient.mk (childRay rayM δ η') z)) :
    childTwistChar rayM H θ δ η' (Ideal.Quotient.mk _ z) =
      star ((θ : MulChar (O ⧸ rayM) ℂ) (Ideal.Quotient.mk rayM z)) *
        δ.residue (Ideal.Quotient.mk δ.modulus z) * η'.residue (Ideal.Quotient.mk η'.modulus z) := by
  unfold childTwistChar
  rw [MulChar.mul_apply, MulChar.mul_apply, pullChar_mk _ _ _ hz, pullChar_mk _ _ _ hz,
    pullChar_mk _ _ _ hz, MulChar.star_apply]

theorem childTwistChar_mem (H : Subgroup (O ⧸ rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (θ : RayQuotient.Characters rayM H)
    (δ η' : Character) :
    childTwistChar rayM H θ δ η' ∈
      RayOrthogonality.characters (RayOrthogonality.globalUnits (childRay rayM δ η')) := by
  rw [RayOrthogonality.mem_characters_iff]
  rintro u ⟨ε, rfl⟩
  have hunit : IsUnit (Ideal.Quotient.mk (childRay rayM δ η') (ε : O)) :=
    (Units.map (Ideal.Quotient.mk (childRay rayM δ η')).toMonoidHom ε).isUnit
  change childTwistChar rayM H θ δ η' (Ideal.Quotient.mk _ (ε : O)) = 1
  rw [childTwistChar_mk rayM H θ δ η' _ hunit, δ.unit_trivial ε, η'.unit_trivial ε]
  have hθ : (θ : MulChar (O ⧸ rayM) ℂ) (Ideal.Quotient.mk rayM (ε : O)) = 1 :=
    (RayOrthogonality.mem_characters_iff H _).mp θ.property _ (hH ⟨ε, rfl⟩)
  rw [hθ]
  simp

/-- The common child twist `θ'`. -/
def childTwist (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (θ : RayQuotient.Characters rayM H) (δ η' : Character) :
    RayQuotient.Characters (childRay rayM δ η') (RayOrthogonality.globalUnits (childRay rayM δ η')) :=
  ⟨childTwistChar rayM H θ δ η', childTwistChar_mem rayM H hH θ δ η'⟩

/-- **The Hecke character of the child twist on a principal ideal prime to `childRay`.** -/
theorem childTwist_span (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (θ : RayQuotient.Characters rayM H) (δ η' : Character) (g : O) (hg : g ≠ 0)
    (hunit : IsUnit (Ideal.Quotient.mk (childRay rayM δ η') g)) :
    idealCoeff (HeckeRayQuotient.character (childRay rayM δ η')
        (RayOrthogonality.globalUnits (childRay rayM δ η')) le_rfl
        (childTwist rayM H hH θ δ η')) (Ideal.span {g}) =
      star (idealCoeff (HeckeRayQuotient.character rayM H hH θ) (Ideal.span {g})) *
        idealCoeff δ (Ideal.span {g}) * idealCoeff η' (Ideal.span {g}) := by
  rw [HeckeRayQuotient.idealCoeff_character, HeckeRayQuotient.idealCoeff_character,
    idealCoeff_span δ hg, idealCoeff_span η' hg]
  unfold RayQuotient.idealCharacter
  rw [IdealCharacter.ofResidue_span _ _ _ hg, IdealCharacter.ofResidue_span _ _ _ hg]
  exact childTwistChar_mk rayM H θ δ η' g hunit

end

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.childTwist_span
