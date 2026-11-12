/- Copyright (c) 2026 Sil. Apache-2.0.
The pool/coefficient dictionary follows `Interface.Bridge.physical_eq_conj_directSlot`; it uses
Hailey Collet's `naturalSlot_eq_direct`, `naturalSlot_annular_filter` (Apache-2.0). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Marked.Contract
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Interface.Bridge
import Submissions.hailey_collet_1252270103.Record12518109Gain.ActualSourceFields

/-!
# High.Marked.Twist

The core slots of the HIGH detector are canonical whole slots with a ray twist
(`Interface.Contract.SlotTwist`).

A core slot (at a fixed common height `τ`) is the natural slot of the row character
`excluded η mask` on the pool `primePool rayM H 2 D` with coefficient `relChar(η₀, θ)·annular`.
On the identity-class primes of norm `≥ D` (large) its coefficient is
`η(P) η₀(P)⁻¹ · annular`, the value of the ray character
`ξ = 1_{rayM} · η η₀⁻¹` (`twistChar`), modulus `rayM' = rayM ⊓ mod(η η₀⁻¹)`.
With the slot twist `G = ⟨comap H, globalUnits rayM'⟩` (`twistSlot`) and `θ' = ξ`
(`twistTheta`), this is the coefficient `relChar(data.η, θ')·data.η·annular` of
`Contract.canonicalSlots` for any row data whose base does not vanish at `P`.

* `twist_coeff`: `ξ(P) = η(P) η₀⁻¹(P)` on `identityClass rayM H`.
* `pool_eq`: `annularPool (primePool rayM H 2 D) D = canonicalPool rayM' (comap H) D` once
  `N(rayM') < D`.
* `node_slot_eq`: the core slot at a fixed height with profile `c·W'` equals
  `c · directSlot u (canonicalPool rayM' pool' D) β D`, `β` the canonical coefficient of `W'`.
* `canon_beta_norm_le`: `‖β‖ ≤ 1` when `‖W'‖ ≤ 1`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High.Marked
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDyadic
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open Qrh.MarkedAnchor.Interface
local notation "O" => HeckeFamily.O
local instance markedTwistQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
local instance markedTwistPID : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

section Twist
variable (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
  (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- The ray twist of the slots: `ξ = 1_{rayM} · η · η₀⁻¹`. -/
def twistChar (η η₀ : Character) : Character :=
  (HeckeRayFamily.character rayM 1).product (η.product η₀.inverse)

/-- Its modulus `rayM ⊓ mod(η η₀⁻¹)`. -/
def twistMod (η η₀ : Character) : Ideal O := (twistChar rayM η η₀).modulus

instance twistMod_neZero (η η₀ : Character) : NeZero (twistMod rayM η η₀) :=
  ⟨(twistChar rayM η η₀).modulus_ne_bot⟩

theorem twistMod_le (η η₀ : Character) : twistMod rayM η η₀ ≤ rayM := inf_le_left

/-- The map of unit groups `(O/rayM')ˣ → (O/rayM)ˣ`. -/
def twistMap (η η₀ : Character) : (O ⧸ twistMod rayM η η₀)ˣ →* (O ⧸ rayM)ˣ :=
  Units.map (Ideal.Quotient.factor (twistMod_le rayM η η₀)).toMonoidHom

/-- The slot pool subgroup: preimage of `H`. -/
def twistPool (η η₀ : Character) : Subgroup (O ⧸ twistMod rayM η η₀)ˣ :=
  Subgroup.comap (twistMap rayM η η₀) H

theorem twistMap_mk (η η₀ : Character) (u : Oˣ) :
    twistMap rayM η η₀ (Units.map (Ideal.Quotient.mk (twistMod rayM η η₀)).toMonoidHom u) =
      Units.map (Ideal.Quotient.mk rayM).toMonoidHom u := by
  ext
  simp [twistMap, Ideal.Quotient.factor_mk]

include hH in
theorem globalUnits_le_twistPool (η η₀ : Character) :
    RayOrthogonality.globalUnits (twistMod rayM η η₀) ≤ twistPool rayM H η η₀ := by
  rintro _ ⟨u, rfl⟩
  show twistMap rayM η η₀ _ ∈ H
  rw [twistMap_mk]
  exact hH ⟨u, rfl⟩

/-- The slot twist: pool `comap H`, twist subgroup `globalUnits rayM'`. -/
def twistSlot (η η₀ : Character) : Contract.SlotTwist (twistMod rayM η η₀) :=
  ⟨twistPool rayM H η η₀, RayOrthogonality.globalUnits (twistMod rayM η η₀),
    globalUnits_le_twistPool rayM H hH η η₀⟩

/-- The twist character as a ray character of `rayM'`. -/
def twistTheta (η η₀ : Character) :
    RayQuotient.Characters (twistMod rayM η η₀) (RayOrthogonality.globalUnits (twistMod rayM η η₀)) :=
  ⟨(twistChar rayM η η₀).residue,
    (RayOrthogonality.mem_rayCharacters_iff (twistMod rayM η η₀) _).mpr
      (twistChar rayM η η₀).unit_trivial⟩

theorem twistTheta_coeff (η η₀ : Character) (I : Ideal O) :
    idealCoeff (HeckeRayQuotient.character (twistMod rayM η η₀)
      (RayOrthogonality.globalUnits (twistMod rayM η η₀)) le_rfl (twistTheta rayM η η₀)) I =
      idealCoeff (twistChar rayM η η₀) I := rfl

include hH in
/-- `ξ = η η₀⁻¹` on the identity class of `H`. -/
theorem twist_coeff (η η₀ : Character) (P : Ideal O)
    (hcl : P ∈ RayQuotient.identityClass rayM H) :
    idealCoeff (twistChar rayM η η₀) P = idealCoeff η P * idealCoeff η₀.inverse P := by
  rw [twistChar, idealCoeff_product, idealCoeff_product,
    HeckePrimeRow.identityClass_principal_coeff rayM H hH hcl, one_mul]

/-- A residue class coprime to the modulus is a unit. -/
theorem isUnit_mk_of_coprime {M : Ideal O} {g : O} (h : IsCoprime (Ideal.span {g}) M) :
    IsUnit (Ideal.Quotient.mk M g) := by
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp h
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hi
  refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk M c) ?_
  rw [← map_mul, mul_comm, ← sub_eq_iff_eq_add.mpr hij.symm, map_sub, map_one,
    Ideal.Quotient.eq_zero_iff_mem.mpr hj, sub_zero]

include hH in
/-- The identity classes agree on primes coprime to `rayM'`. -/
theorem identityClass_twist_iff (η η₀ : Character) {P : Ideal O} (hP0 : P ≠ ⊥)
    (hcop : IsCoprime P (twistMod rayM η η₀)) :
    P ∈ RayQuotient.identityClass rayM H ↔
      P ∈ RayQuotient.identityClass (twistMod rayM η η₀) (twistPool rayM H η η₀) := by
  rw [RayQuotient.identityClass_iff_generator rayM H hH hP0,
    RayQuotient.identityClass_iff_generator (twistMod rayM η η₀) (twistPool rayM H η η₀)
      (globalUnits_le_twistPool rayM H hH η η₀) hP0]
  set g := Submodule.IsPrincipal.generator P
  have hspan : Ideal.span {g} = P := Ideal.span_singleton_generator P
  have hu : IsUnit (Ideal.Quotient.mk (twistMod rayM η η₀) g) :=
    isUnit_mk_of_coprime (hspan ▸ hcop)
  constructor
  · rintro ⟨w, hw, hwH⟩
    refine ⟨hu.unit, rfl, ?_⟩
    show twistMap rayM η η₀ hu.unit ∈ H
    have : twistMap rayM η η₀ hu.unit = w := by
      ext
      simp [twistMap, Ideal.Quotient.factor_mk, hw]
    rw [this]; exact hwH
  · rintro ⟨w, hw, hwH⟩
    refine ⟨twistMap rayM η η₀ w, ?_, hwH⟩
    simp [twistMap, hw, Ideal.Quotient.factor_mk]

include hH in
/-- Pools: the annular part of the core pool is the canonical pool of the twist. -/
theorem pool_eq (η η₀ : Character) {D : ℝ} (hD : 0 < D)
    (hN : ((twistMod rayM η η₀).absNorm : ℝ) < D) :
    Cycle61MarkedPlain.annularPool (primePool rayM H 2 D) D =
      Contract.canonicalPool (twistMod rayM η η₀) (twistPool rayM H η η₀) D := by
  ext P
  simp only [Cycle61MarkedPlain.annularPool, Contract.canonicalPool, primePool,
    Finset.mem_filter]
  constructor
  · rintro ⟨⟨hA, hpr, hcl⟩, hr⟩
    have hND : D ≤ (P.absNorm : ℝ) := by
      have := (le_div_iff₀ hD).mp hr.1; linarith
    have hcop := InverseInitialExcludedGeometry.prime_coprime_of_norm_gt hpr
      (twistChar rayM η η₀).modulus_ne_bot (lt_of_lt_of_le hN hND)
    exact ⟨⟨hA, hpr, (identityClass_twist_iff rayM H hH η η₀ hpr.ne_zero hcop).mp hcl⟩, hr⟩
  · rintro ⟨⟨hA, hpr, hcl⟩, hr⟩
    have hND : D ≤ (P.absNorm : ℝ) := by
      have := (le_div_iff₀ hD).mp hr.1; linarith
    have hcop := InverseInitialExcludedGeometry.prime_coprime_of_norm_gt hpr
      (twistChar rayM η η₀).modulus_ne_bot (lt_of_lt_of_le hN hND)
    exact ⟨⟨hA, hpr, (identityClass_twist_iff rayM H hH η η₀ hpr.ne_zero hcop).mpr hcl⟩, hr⟩

end Twist

end
end Qrh.MarkedAnchor.High.Marked
