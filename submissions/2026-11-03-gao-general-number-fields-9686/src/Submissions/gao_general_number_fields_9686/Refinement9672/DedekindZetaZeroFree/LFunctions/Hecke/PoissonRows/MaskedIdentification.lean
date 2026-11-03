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
Original path: DedekindZetaZeroFree/LFunctions/Hecke/PoissonRows/MaskedIdentification.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencyData
public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.FrequencyIdentification

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.RawHeckeIdentification31

noncomputable section

open _root_.DedekindZetaZeroFree
open DedekindZetaZeroFree NumberField
open _root_.DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.PrincipalMellinComparison
open _root_.DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
open _root_.DedekindZetaZeroFree.Quantitative.RawFixed
open DedekindZetaZeroFree.Quantitative.RawFixed
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

theorem pkg_bridge :
    RawFrequencyPublicBridge.Bridge D (FixedData.pkg D).U (FixedData.pkg D).P
      (FixedData.pkg D).M (FixedData.pkg D).plus (FixedData.pkg D).minus where
  raw_u := (FixedData.pkg D).U_u
  finite := (FixedData.pkg D).deletion_finite
  plus_coeff := (FixedData.pkg D).plus_mask
  minus_coeff := (FixedData.pkg D).minus_mask
  plus_nonprincipal := fun u hu => ((FixedData.pkg D).nonprincipal u hu).1
  minus_nonprincipal := fun u hu => ((FixedData.pkg D).nonprincipal u hu).2
  plus_diff := fun u hu => (FixedData.pkg D).plus_diff u (((FixedData.pkg D).nonprincipal u hu).1)
  minus_diff := fun u hu => (FixedData.pkg D).minus_diff u (((FixedData.pkg D).nonprincipal u hu).2)
  plus_series := (FixedData.pkg D).plus_eq
  minus_series := (FixedData.pkg D).minus_eq

theorem plus_eq_hecke_mul_mask (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (w : ℂ) (hw : 0 < w.re) :
    (FixedData.pkg D).plus u w =
      (RowHeckeBridge.hecke D.recipe.A (FixedData.primPlus D u)
          ((FixedData.pkg D).nonprincipal u hu).1).L w *
        Detector.finiteEulerDeletionMask F
          (RawHeckeRows.rawDeletionSet (FixedData.rawFrequency D u))
          (fun v => (FixedData.primPlus D u).character v.asIdeal) w :=
  (pkg_bridge D).plus_eq_hecke_mul_mask u hu w hw

theorem minus_eq_hecke_mul_mask (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (w : ℂ) (hw : 0 < w.re) :
    (FixedData.pkg D).minus u w =
      (RowHeckeBridge.hecke D.recipe.A (FixedData.primMinus D u)
          ((FixedData.pkg D).nonprincipal u hu).2).L w *
        Detector.finiteEulerDeletionMask F
          (RawHeckeRows.rawDeletionSet (FixedData.rawFrequency D u))
          (fun v => (FixedData.primMinus D u).character v.asIdeal) w :=
  (pkg_bridge D).minus_eq_hecke_mul_mask u hu w hw

theorem plus_conductor_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Frequency D.recipe,
      1 + (Ideal.absNorm (FixedData.primPlus D u).conductor : ℝ) ≤
        C * frequencyNorm D.recipe u :=
  (pkg_bridge D).plus_conductor_bound

theorem minus_conductor_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ u : Frequency D.recipe,
      (Ideal.absNorm (FixedData.primMinus D u).conductor : ℝ) ≤ c * frequencyNorm D.recipe u := by
  obtain ⟨c, hc, h⟩ := DetectorDyads.actual_raw_minus_inducer_conductor_bound D.recipe
  exact ⟨c, hc, fun u => h u (FixedData.rawFrequency D u) (FixedData.rawFrequency_u D u)
    (FixedData.primMinus D u)
    ((FixedData.pkg D).minus_mask u)⟩

end

end DedekindZetaZeroFree.Quantitative.RawHeckeIdentification31

end Refinement9672
