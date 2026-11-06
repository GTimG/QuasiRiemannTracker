/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/LocalFields/PowerDefectProduct.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.All

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree
namespace SArithmeticData

noncomputable section
variable {F : Type} [Field F] [NumberField F]

theorem prod_finitePlaceNthPowerDefect (A : SArithmeticData F)
    (n : ℕ) (hn : n = 2 ∨ n = 3) :
    (∏ v : ↥A.Sf,
      GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceNthPowerDefect
        (K := F) ⟨n, by omega⟩ v.val) = n ^ Module.finrank ℚ F := by
  apply GlobalClassFieldTheory.ClassFieldAxiom.prod_finitePlaceNthPowerDefect
  intro v hv
  apply A.above_six v
  have hmem : (n : 𝓞 F) ∈ v.asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).mp (Ideal.dvd_iff_le.mp hv)
  rcases hn with rfl | rfl
  · convert v.asIdeal.mul_mem_left (3 : 𝓞 F) hmem using 1 <;> norm_num
  · convert v.asIdeal.mul_mem_left (2 : 𝓞 F) hmem using 1 <;> norm_num

end
end SArithmeticData
end DedekindZetaZeroFree
