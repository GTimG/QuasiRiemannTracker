/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/Units/TorsionPowerCoordinates.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.All

@[expose] public section

namespace DedekindZetaZeroFree.SArithmeticData

theorem primitive_roots_of_dvd_twelve {F : Type} [Field F] [NumberField F]
    (A : DedekindZetaZeroFree.SArithmeticData F) (n : ℕ+) (hn : (n : ℕ) ∣ 12) :
    (primitiveRoots (n : ℕ) F).Nonempty := by
  exact ⟨A.zeta12 ^ (12 / (n : ℕ)), (mem_primitiveRoots n.pos).2
    (A.primitive_zeta12.pow (by decide) (Nat.div_mul_cancel hn).symm)⟩

noncomputable def torsionPowerQuotientEquiv {F : Type} [Field F] [NumberField F]
    (A : DedekindZetaZeroFree.SArithmeticData F) (n : ℕ+) (hn : (n : ℕ) ∣ 12) :
    (NumberField.Units.torsion F ⧸
      (powMonoidHom (n : ℕ) :
        NumberField.Units.torsion F →* NumberField.Units.torsion F).range) ≃*
      Multiplicative (ZMod (n : ℕ)) := by
  exact KummerTheory.numberFieldTorsionNthPowerQuotientEquivZMod (K := F) n
    (A.primitive_roots_of_dvd_twelve n hn)

end DedekindZetaZeroFree.SArithmeticData
