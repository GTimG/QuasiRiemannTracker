/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/SelectedJacquet/CompactWeyl.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Profiles.LocalTensorActions

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SheetRescaling
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPGlobalResidualConstruction

def compactWeyl : ComplexSU2 :=
  ⟨!![0, Complex.I; Complex.I, 0], by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.star_apply]
    · simp [Matrix.det_fin_two]⟩

end DedekindZetaZeroFree.SheetRescaling

end
