/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9686;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Successor namespace extension, 2026-11-03, Zhongpai Gao with AI assistance.
Original source: AxiomMath/DedekindZetaZeroFree at09afbb4ce6570c1615d58509dc197fc9f0956b7d;
starting refinement: Gaozhongpai/DedekindZetaZeroFree at829193272c1eaf223bb7228fbfb9003f414808e9.
Original path: DedekindZetaZeroFree/Nonvanishing/Mellin/Quantitative/Growth.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Moments.Comparison.QuantitativePoissonComparison
public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Moments.Reflected.FixedProbeBound

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.Spectral

open _root_.DedekindZetaZeroFree
open DedekindZetaZeroFree NumberField

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem f_growth (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 < Cε ∧ ∀ Z : ℝ, 2 ≤ Z → ‖f D Z‖ ≤ Cε * Z ^ ((893 / 2500 : ℝ) + ε) := by
  obtain ⟨C1, hC1, h1⟩ := DedekindZetaZeroFree.Quantitative.Compare.Iscale_sub_main_le D
  obtain ⟨C2, hC2, h2⟩ := DedekindZetaZeroFree.Quantitative.FixedData.Iscale_bound D ε hε
  have hc : 0 < ‖c₀ D‖ := norm_pos_iff.mpr (DedekindZetaZeroFree.Quantitative.Compare.c₀_ne_zero D)
  refine ⟨(C1 + C2) / ‖c₀ D‖, div_pos (by linarith) hc, ?_⟩
  intro Z hZ
  have hZ0 : 0 < Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hexp : (35719 / 100000 : ℝ) ≤ 893 / 2500 + ε := by linarith
  have hpow : Z ^ (35719 / 100000 : ℝ) ≤ Z ^ ((893 / 2500 : ℝ) + ε) :=
    Real.rpow_le_rpow_of_exponent_le hZ1 hexp
  have hnonneg : 0 ≤ Z ^ ((893 / 2500 : ℝ) + ε) := Real.rpow_nonneg hZ0.le _
  have hI : ‖D.Iscale Z‖ ≤ C2 * Z ^ ((893 / 2500 : ℝ) + ε) := h2 Z hZ
  have hM := h1 Z hZ
  have key := norm_sub_le (D.Iscale Z) (D.Iscale Z - c₀ D * f D Z)
  have e : D.Iscale Z - (D.Iscale Z - c₀ D * f D Z) = c₀ D * f D Z := by ring
  rw [e] at key
  rw [norm_mul] at key
  have hC1' : C1 * Z ^ (35719 / 100000 : ℝ) ≤ C1 * Z ^ ((893 / 2500 : ℝ) + ε) :=
    mul_le_mul_of_nonneg_left hpow hC1.le
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  nlinarith

theorem g_growth (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 < Cε ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖((Z : ℂ) ^ (((61 / 100 : ℝ)) : ℂ)) * f D Z‖ ≤ Cε * Z ^ (1209 / 1250 + ε) := by
  obtain ⟨C, hC, h⟩ := f_growth D ε hε
  refine ⟨C, hC, fun Z hZ => ?_⟩
  have hZ0 : 0 < Z := by linarith
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hZ0]
  simp only [Complex.ofReal_re]
  have hfz := h Z hZ
  have e : Z ^ (1209 / 1250 + ε) = Z ^ (61 / 100 : ℝ) * Z ^ ((893 / 2500 : ℝ) + ε) := by
    rw [← Real.rpow_add hZ0]
    congr 1
    ring
  have hw : 0 ≤ Z ^ (61 / 100 : ℝ) := Real.rpow_nonneg hZ0.le _
  calc Z ^ (61 / 100 : ℝ) * ‖f D Z‖ ≤ Z ^ (61 / 100 : ℝ) * (C * Z ^ ((893 / 2500 : ℝ) + ε)) :=
        mul_le_mul_of_nonneg_left hfz hw
    _ = C * Z ^ (1209 / 1250 + ε) := by rw [e]; ring

end DedekindZetaZeroFree.Quantitative.Spectral

end Refinement9672
