/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact original three-height cube factorization. The physical denominator,
marked correction and compensated local factors are unchanged. -/
import Candidate.C092.transport.SelectedActualIntegral

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter MeasureTheory
open OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open ProbeMellinBoundary
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.ProbeAssembly
namespace QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters]

def sLine (D : BaselineData) (a : ℝ) (t : HeightSpace) : ℂ := (a+16*D.e:ℝ)+t.1.1*Complex.I
def wLine (D : BaselineData) (a : ℝ) (t : HeightSpace) : ℂ := (1-a-6*D.e:ℝ)+t.2*Complex.I
def zLine (t : HeightSpace) : ℂ := (17/50:ℂ)+t.1.2*Complex.I

def cubeWindow (H : ℝ) : Set HeightSpace := {t | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}

def factoredRow (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (u : FreeRow) (Z a H : ℝ) (P : ∀ j, SelectedActualIntegral.primePool D F Z j) : HeightSpace → ℂ :=
  (cubeWindow H).indicator (fun t =>
    sourceMellinWeight F.W F.W (Z^Geometry.x) (Z^Geometry.y) Z (sLine D a t) (wLine D a t) (zLine t) *
    frequencyWeight (zLine t) ⟨u.val,u.property.1⟩ *
    SelectedActualIntegral.rawFactor D F η u Z P (sLine D a t) (wLine D a t) (zLine t))

/-- All three contour heights are independent; the reciprocal stays evaluated
at the retained s coordinate, with the separate original s+w guard. -/
theorem cube_row_factor (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (u : FreeRow) (Z a H : ℝ) (P : ∀ j, SelectedActualIntegral.primePool D F Z j)
    (hP : Function.Injective (fun j => (P j).val)) :
    cubeWeightedRow F.S F.exclusions F.maximal (fun j => (P j).val)
      (fun j => SelectedActualIntegral.pool_outside D F Z j _ (P j).property) η u
      (fun (_ : Fin D.N) y => (F.w y:ℂ)) (fun j => Z^(D.length j)) F.W F.W
      (Z^Geometry.x) (Z^Geometry.y) Z a D.e H = factoredRow D F η u Z a H P := by
  funext t
  by_cases ht : t ∈ cubeWindow H
  · dsimp only [cubeWindow] at ht
    simp only [cubeWeightedRow, factoredRow, cubeWindow, Set.indicator_of_mem ht,
      weightedRowOnLines, sLine, wLine, zLine]
    rw [SelectedActualIntegral.calibrated_row_factor D F η u Z P hP]
    norm_num
  · dsimp only [cubeWindow] at ht
    simp only [cubeWeightedRow, factoredRow, cubeWindow, Set.indicator_of_notMem ht]

def fullEnvelope (D : BaselineData) (F : BaselineSourceData D)
    (padding tau : ℝ) (η : Character) (Z : ℝ) (idx grid : FreeRow → ℕ) (t : HeightSpace) : ℝ :=
  ∑ u ∈ SelectedActualIntegral.selectedRows D F padding Z grid,
    ∑ P : (∀ j, SelectedActualIntegral.primePool D F Z j),
      ‖factoredRow D F η u Z (51/100+D.e*grid u) ((3*idx u+1:ℕ)*Z^tau) P t‖

/-- Exact selected integrand with full prime assignments and rowwise buffers.
No particular source energy, count estimate or moment is assumed. -/
theorem selected_integrand_factor (D : BaselineData) (F : BaselineSourceData D) :
    ∀ᶠ Z : ℝ in atTop, ∀ padding tau : ℝ, ∀ η : Character,
      ∀ idx grid : FreeRow → ℕ, ∀ t : HeightSpace,
      SelectedActualIntegral.selectedIntegrand D F padding tau η Z idx grid t =
        ∑ u ∈ SelectedActualIntegral.selectedRows D F padding Z grid,
          ∑ P : (∀ j, SelectedActualIntegral.primePool D F Z j),
            factoredRow D F η u Z (51/100+D.e*grid u) ((3*idx u+1:ℕ)*Z^tau) P t := by
  filter_upwards [SelectedActualIntegral.tuples_injective D F] with Z hP
  intro padding tau η idx grid t
  unfold SelectedActualIntegral.selectedIntegrand
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro P hP'
  exact congrFun (cube_row_factor D F η u Z _ _ P (hP P)) t

theorem selected_integrand_norm_le (D : BaselineData) (F : BaselineSourceData D) :
    ∀ᶠ Z : ℝ in atTop, ∀ padding tau : ℝ, ∀ η : Character,
      ∀ idx grid : FreeRow → ℕ, ∀ t : HeightSpace,
      ‖SelectedActualIntegral.selectedIntegrand D F padding tau η Z idx grid t‖ ≤
        fullEnvelope D F padding tau η Z idx grid t := by
  filter_upwards [selected_integrand_factor D F] with Z hZ
  intro padding tau η idx grid t
  rw [hZ padding tau η idx grid t]
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum (fun u hu => norm_sum_le _ _)

end QRH.Cycle092.SelectedNonfloor
#print axioms QRH.Cycle092.SelectedNonfloor.cube_row_factor
#print axioms QRH.Cycle092.SelectedNonfloor.selected_integrand_factor
