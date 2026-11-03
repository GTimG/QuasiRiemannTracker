/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/Smooth/MatrixFlowDerivativeIdentification.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.Smooth.RightInvariantDifferentialWords

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField

namespace DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeWordBridge

variable (F : Type) [Field F] [NumberField F]

def basisEquiv : KPContActualSphericalRightFieldIdentification.LieIndex F ≃
    KPSmoothActualFlowData.B F :=
  Equiv.prodCongr (Equiv.refl _) finProdFinEquiv

def wordIndexEquiv : Fin (KPContActualSphericalRightFieldIdentification.groupDimension F) ≃
    KPSmoothActualFlowData.B F :=
  (KPContActualSphericalRightFieldIdentification.lieEnumeration F).trans (basisEquiv F)

omit [NumberField F] in
private theorem matrix_basis (b : KPContActualSphericalRightFieldIdentification.LieIndex F)
    (t : ℝ) (v : NumberField.InfinitePlace F) :
    KPSmoothLocalQuotientCharts.lieMatrix F (t • Pi.single b 1) v =
      KPSmoothActualFlowData.sl2Matrix (fun j => if (v,j) = basisEquiv F b then t else 0) := by
  rcases b with ⟨w, i, j⟩
  by_cases hv : v = w
  · subst v
    fin_cases i <;> fin_cases j <;>
      ext r c <;> fin_cases r <;> fin_cases c <;>
      simp [KPSmoothLocalQuotientCharts.lieMatrix, KPSmoothActualFlowData.sl2Matrix,
        basisEquiv, finProdFinEquiv, Complex.mk_eq_add_mul_I, mul_comm]
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [KPSmoothLocalQuotientCharts.lieMatrix, KPSmoothActualFlowData.sl2Matrix,
        basisEquiv, finProdFinEquiv, hv, Complex.mk_eq_add_mul_I]

omit [NumberField F] in

theorem matrixExp_eq_flow
    (b : KPContActualSphericalRightFieldIdentification.LieIndex F) (t : ℝ) :
    KPSmoothLocalQuotientCharts.matrixExp F (t • Pi.single b 1) =
      KPSmoothActualFlowData.flow F (basisEquiv F b) t := by
  funext v
  simp only [KPSmoothLocalQuotientCharts.matrixExp, KPSmoothActualFlowData.flow,
    KPSmoothActualFlowData.exponential, KPSmoothActualFlowData.matrixExponential,
    matrix_basis]

variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem actualRightWord_eq_wordDerivative
    (w : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F)))
    (f : KPSmoothActualFlowData.X F ζ hζ → ℂ) (g : KPSmoothActualFlowData.G F ζ hζ) :
    KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ w
      (fun g => f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) g =
    KPSmoothActualFlowData.wordDerivative F ζ hζ (w.map (wordIndexEquiv F)) f
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
    change deriv _ 0 = deriv _ 0
    apply congrArg (fun q : ℝ → ℂ => deriv q 0)
    funext t
    rw [matrixExp_eq_flow]
    exact ih _

end DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeWordBridge

end
