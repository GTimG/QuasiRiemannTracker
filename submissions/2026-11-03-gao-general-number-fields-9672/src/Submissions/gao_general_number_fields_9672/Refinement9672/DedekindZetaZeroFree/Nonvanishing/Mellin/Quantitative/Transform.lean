/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9672;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Successor namespace extension, 2026-11-03, Zhongpai Gao with AI assistance.
Original source: AxiomMath/DedekindZetaZeroFree at09afbb4ce6570c1615d58509dc197fc9f0956b7d;
starting refinement: Gaozhongpai/DedekindZetaZeroFree at829193272c1eaf223bb7228fbfb9003f414808e9.
Original path: DedekindZetaZeroFree/Nonvanishing/Mellin/Quantitative/Transform.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9672.Refinement9672.DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.SpectralFunction

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.MellinTransform

noncomputable section

open _root_.DedekindZetaZeroFree
open DedekindZetaZeroFree NumberField MeasureTheory
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def g (Z : ℝ) : ℂ :=
  if 0 < Z then (Z : ℂ) ^ (61 / 100 : ℂ) * Spectral.f D Z else 0

def T (s : ℂ) : ℂ := mellin (g D) (-s)

theorem T_eq (s : ℂ) :
    T D s = ∫ Z : ℝ in Set.Ioi 0,
      Spectral.f D Z * (Z : ℂ) ^ (-s + 61 / 100) / (Z : ℂ) := by
  unfold T mellin
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
  intro Z hZ
  have hZ' : (0 : ℝ) < Z := hZ
  have hne : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ'.ne'
  have h1 : (Z : ℂ) ^ (-s - 1) = (Z : ℂ) ^ (-s) / (Z : ℂ) := by
    rw [Complex.cpow_sub _ _ hne, Complex.cpow_one]
  have h2 : (Z : ℂ) ^ (-s + 61 / 100) = (Z : ℂ) ^ (-s) * (Z : ℂ) ^ (61 / 100 : ℂ) :=
    Complex.cpow_add _ _ hne
  simp only [g, if_pos hZ', smul_eq_mul]
  rw [h1, h2]
  ring

theorem g_of_nonpos (Z : ℝ) (hZ : Z ≤ 0) : g D Z = 0 := by
  simp [g, not_lt.mpr hZ]

end

end DedekindZetaZeroFree.Quantitative.MellinTransform

end Refinement9672
