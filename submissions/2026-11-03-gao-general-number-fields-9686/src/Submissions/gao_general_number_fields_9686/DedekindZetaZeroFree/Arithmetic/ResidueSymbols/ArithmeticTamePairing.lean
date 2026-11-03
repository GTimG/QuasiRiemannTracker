/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/ResidueSymbols/ArithmeticTamePairing.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.All

@[expose] public section

open scoped Classical ValuativeRel

namespace DedekindZetaZeroFree.RepresentationTheory.KPHilbertNormalization.TamePairing
noncomputable section
set_option autoImplicit false

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem arithmetic_tame_pairing (n : ℕ+)
    (hgood : ValuativeRel.valuation K ((n : ℕ) : K) = 1)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (x : Kˣ) (u u' : (ValuativeRel.valuation K).integerˣ) :
    ClassFieldTheory.localHilbertPairing K n
        (LocalClassFieldTheory.Kummer.natCast_ne_zero_of_valuation_eq_one K n hgood)
        hmu
        (ClassFieldTheory.powerClass K n
          (LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits K u))
        (ClassFieldTheory.powerClass K n x) =
      KummerTheory.nthRootsSubgroupEquivRootsOfUnity K (n : ℕ)
        (LocalClassFieldTheory.Kummer.localTamePowerResidueSymbol K n hgood hmu u ^
          (-LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
            (Additive.ofMul x))) ∧
    ClassFieldTheory.localHilbertPairing K n
        (LocalClassFieldTheory.Kummer.natCast_ne_zero_of_valuation_eq_one K n hgood)
        hmu
        (ClassFieldTheory.powerClass K n
          (LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits K u'))
        (ClassFieldTheory.powerClass K n
          (LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits K u)) = 1 := by
  constructor
  · calc
      _ = ClassFieldTheory.localHilbertSymbol K n
          (LocalClassFieldTheory.Kummer.natCast_ne_zero_of_valuation_eq_one K n hgood)
          hmu (LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits K u)
          x := ClassFieldTheory.localHilbertPairing_powerClass K n _ hmu _ _
      _ = _ := congrArg (KummerTheory.nthRootsSubgroupEquivRootsOfUnity K (n : ℕ))
        (LocalClassFieldTheory.Kummer.localHilbertSymbol_tame_formula K n hgood hmu u x)
  · calc
      _ = ClassFieldTheory.localHilbertSymbol K n
          (LocalClassFieldTheory.Kummer.natCast_ne_zero_of_valuation_eq_one K n hgood)
          hmu (LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits K u')
          (LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits K u) :=
        ClassFieldTheory.localHilbertPairing_powerClass K n _ hmu _ _
      _ = 1 := by
        unfold ClassFieldTheory.localHilbertSymbol
        rw [LocalClassFieldTheory.Kummer.localHilbertSymbol_integerUnit_integerUnit_eq_one
          K n hgood hmu u' u, map_one]

end
end DedekindZetaZeroFree.RepresentationTheory.KPHilbertNormalization.TamePairing
