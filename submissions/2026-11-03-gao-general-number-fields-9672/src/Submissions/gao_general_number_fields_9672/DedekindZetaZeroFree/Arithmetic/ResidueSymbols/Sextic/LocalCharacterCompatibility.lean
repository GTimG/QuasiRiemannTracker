/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/ResidueSymbols/Sextic/LocalCharacterCompatibility.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.LocalFields.Residues.ArtinModelEquivalence

@[expose] public section

open scoped NumberField Classical ValuativeRel
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.LocalFiniteSumCompatibility
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
local instance (p : ExteriorPrime A) : ValuativeRel (LocalField p) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F p.val

theorem exterior_tame (p : ExteriorPrime A) :
    ValuativeRel.valuation (LocalField p) (6 : LocalField p) = 1 := by
  exact (KPHilbert.tame_place_iff F p.val).mpr
    (fun h => exterior_notMem p (A.above_six p.val h))

theorem chi_exact_order (p : ExteriorPrime A) : orderOf (chi (σ := σ) p) = 6 :=
  intrinsic_chi_order p

local instance (p : ExteriorPrime A) : IsNonarchimedeanLocalField (LocalField p) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F p.val

theorem sexticPower_eq_chi_pow (p : ExteriorPrime A) (a : ℤ) :
    A.sexticResiduePowerChar σ (primeIdeal p) a =
      chi (σ := σ) p ^ SArithmeticData.sexticExponent a := by
  simp [chi, SArithmeticData.sexticResiduePowerChar, SArithmeticData.sexticExponent]

theorem maskedPower_eq_reduction (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hn : n ≠ 0) (a : ℤ) (x : Residue C p n) :
    maskedPower C p n a x =
      (chi (σ := σ) p ^ SArithmeticData.sexticExponent a) (reduction C p n hn x) := by
  unfold maskedPower
  rw [dif_neg hn, ← sexticPower_eq_chi_pow]
  by_cases hx : IsUnit x
  · exact if_pos hx
  · rw [if_neg hx]
    exact (A.sexticResiduePowerChar_nonunit σ (primeIdeal p) a _
      (fun h => hx ((reduction_isUnit C p n hn x).mp h))).symm

theorem maskedPower_nonunit (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hn : n ≠ 0) (a : ℤ) (x : Residue C p n)
    (hx : ¬ IsUnit x) : maskedPower C p n a x = 0 := by
  simp [maskedPower, hn, hx]

theorem maskedPower_zero_depth (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (a : ℤ) (x : Residue C p 0) :
    maskedPower C p 0 a x = 1 := by
  simp [maskedPower]

end DedekindZetaZeroFree.LocalFiniteSumCompatibility

end
