/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Moments/Principal/TripleMellin/HeightPermutationFubini.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Moments.Principal.TripleMellin.KernelDefinitions

@[expose] public section

namespace DedekindZetaZeroFree.NormalizedProbe.TripleMellin
open TripleMellinRaw
noncomputable section
open MeasureTheory

def heightEquiv : (Fin 3 → ℝ) ≃ᵐ ℝ × ℝ × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.piFinTwo (fun _ => ℝ)))

theorem heightEquiv_apply (t : Fin 3 → ℝ) : heightEquiv t = (t 0, t 1, t 2) := by
  rfl

theorem heightEquiv_symm_apply (t : ℝ × ℝ × ℝ) :
    heightEquiv.symm t = ![t.1, t.2.1, t.2.2] := by
  ext i
  fin_cases i <;> rfl

theorem heightEquiv_preserving : MeasurePreserving heightEquiv volume volume := by
  exact ((MeasurePreserving.id volume).prod
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)

theorem integral_eq_initial_order (f : (Fin 3 → ℝ) → ℂ) (hf : Integrable f) :
    (∫ t, f t) = ∫ t0 : ℝ, ∫ t1 : ℝ, ∫ t2 : ℝ, f ![t0, t1, t2] := by
  have hp : Integrable (fun t : ℝ × ℝ × ℝ => f (heightEquiv.symm t)) :=
    (heightEquiv_preserving.symm heightEquiv).integrable_comp_emb
      heightEquiv.symm.measurableEmbedding |>.mpr hf
  rw [← (heightEquiv_preserving.symm heightEquiv).integral_comp' f]
  simp only [Measure.volume_eq_prod] at hp ⊢
  rw [integral_prod _ hp]
  apply integral_congr_ae
  filter_upwards [hp.prod_right_ae] with t0 ht0
  rw [integral_prod _ ht0]
  simp only [heightEquiv_symm_apply]

theorem integral_eq_order (f : (Fin 3 → ℝ) → ℂ) (hf : Integrable f)
    (order : Equiv.Perm (Fin 3)) :
    (∫ t, f t) = ∫ t0 : ℝ, ∫ t1 : ℝ, ∫ t2 : ℝ,
      f (fun i => (![t0, t1, t2] : Fin 3 → ℝ) (order.symm i)) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) order
  have he : MeasurePreserving e volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin 3 => ℝ) order
  have hg : Integrable (fun t => f (e t)) :=
    he.integrable_comp_emb e.measurableEmbedding |>.mpr hf
  rw [← he.integral_comp' f]
  convert integral_eq_initial_order (fun t => f (e t)) hg using 1
  congr 1
  ext t0
  congr 1
  ext t1
  congr 1
  ext t2
  congr 1
  ext i
  simp [e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

end
end DedekindZetaZeroFree.NormalizedProbe.TripleMellin
