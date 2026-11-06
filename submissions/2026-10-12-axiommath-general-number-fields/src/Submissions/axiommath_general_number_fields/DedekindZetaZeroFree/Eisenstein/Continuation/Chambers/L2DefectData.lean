/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Continuation/Chambers/L2DefectData.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.Continuation.Cusps.CutoffSourceData
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.Induction.ConvergenceChamberAndConstantTerms

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPChamberL2Defect

open MeasureTheory
open scoped ENNReal

abbrev chamber : Set ℂ := KPEisensteinChamber.chamber

theorem chamber_isOpen : IsOpen chamber := by
  exact isOpen_lt continuous_const Complex.continuous_re

section ScalarFormula
variable {G Q X H A : Type*} [Group G] [Fintype A]
  [AddCommGroup H] [Module ℂ H]

def series (lift : Q → G) (representative : X → G)
    (realize : ℂ → H →ₗ[ℂ] (G → ℂ)) (f : ℂ → H) (s : ℂ) (x : X) : ℂ :=
  ∑' q, realize s (f s) (lift q * representative x)

def quotientRealization (representative : X → G)
    (realize : ℂ → H →ₗ[ℂ] (G → ℂ)) (s : ℂ) : H →ₗ[ℂ] (X → ℂ) where
  toFun v x := realize s v (representative x)
  map_add' := by intro v w; ext x; simp
  map_smul' := by intro c v; ext x; simp

end ScalarFormula

def scalarJet {X : Type*} (g : ℂ → X → ℂ) (k : ℕ) (s : ℂ) : X → ℂ :=
  fun x => iteratedDerivWithin k (fun z => g z x) chamber s

def spectralCorrection {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (d : ℕ) (u : ℕ → ℂ → H) (k : ℕ) (s : ℂ) : H :=
  ∑ j ∈ Finset.Icc 1 (min k 2),
    ((Nat.choose k j : ℂ) *
      iteratedDerivWithin j (KPContinuation.spectralCoordinate (d : ℤ)) chamber s) •
        u (k - j) s

def graphNorm {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (Δ : H →ₗ.[ℂ] H) (u : Δ.domain) : ℝ := ‖(u : H)‖ + ‖Δ u‖

section CuspOutput
variable {Y A W : Type*} [MeasurableSpace Y] [Fintype A]
  [NormedAddCommGroup W]

end CuspOutput

section GraphEstimates
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

end GraphEstimates
end DedekindZetaZeroFree.KPChamberL2Defect

end
