/-
The radial energy of one root class.

If every kept row in the support of the radial weight is `u·g⁶` for a core `u` of a finite set, and the row
function at `u·g⁶` is the value at `u` of a fixed ordinary polynomial, then the radial energy is at most the
diagonal control of the weight times the core energy, and hence (PR 93's selected norm) at most
`diag Φ · Kn (X + Y^{1-δ} X^δ) · mass`.
-/
import Submissions.arvi_selected_leaf.R1.Height
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OriginalRadialComparison
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FixedRadialSource

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf.R1
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths CanonicalRowCompletion HeckeFamily ConcreteTraceCRT
open CenteredMomentOriginalRadialComparison
open Qrh.JointDetector Qrh.JointDetector.FineDetectorWords
local notation "O" => ActualEisensteinCubic.O

/-- **Radial energy of a root class** by its core energy. -/
theorem root_radial_energy (F : O → ℂ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hΦ : ∀ z : O, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) (g : O) (cores : Finset O)
    (hcover : ∀ z, keep z → Φ (‖eisEmbedding z‖^2/K) ≠ 0 → ∃ u ∈ cores, z = u * g^6) :
    radialEnergy F keep Φ K ≤
      QuadraticInitialBound.diagonalControl Φ * ∑ u ∈ cores, ‖F (u * g^6)‖^2 := by
  classical
  set f : O → ℝ := fun z => if keep z then ‖F z‖^2 * (Φ (‖eisEmbedding z‖^2/K)).re else 0 with hf
  have hf0 : ∀ z, 0 ≤ f z := by
    intro z; simp only [hf]; split_ifs
    · exact mul_nonneg (sq_nonneg _) (hΦ _)
    · exact le_rfl
  have hsupp : ∀ z ∉ cores.image (fun u => u * g^6), f z = 0 := by
    intro z hz
    simp only [hf]
    split_ifs with hk
    · by_cases hΦz : Φ (‖eisEmbedding z‖^2/K) = 0
      · rw [hΦz]; simp
      · obtain ⟨u, hu, rfl⟩ := hcover z hk hΦz
        exact absurd (Finset.mem_image_of_mem _ hu) hz
    · rfl
  have htsum : radialEnergy F keep Φ K = ∑ z ∈ cores.image (fun u => u * g^6), f z := by
    unfold radialEnergy
    exact tsum_eq_sum hsupp
  rw [htsum]
  have himage : ∑ z ∈ cores.image (fun u => u * g^6), f z ≤ ∑ u ∈ cores, f (u * g^6) :=
    Finset.sum_image_le_of_nonneg (fun z _ => hf0 z)
  refine himage.trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  simp only [hf]
  split_ifs
  · have hw : (Φ (‖eisEmbedding (u * g^6)‖^2/K)).re ≤ QuadraticInitialBound.diagonalControl Φ :=
      (Complex.re_le_norm _).trans
        (CenteredMomentEnergyFixedRadialSource.norm_le_diagonalControl Φ _)
    calc ‖F (u * g^6)‖^2 * (Φ (‖eisEmbedding (u * g^6)‖^2/K)).re
        ≤ ‖F (u * g^6)‖^2 * QuadraticInitialBound.diagonalControl Φ :=
          mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ = _ := by ring
  · exact mul_nonneg (QuadraticInitialBound.diagonalControl_nonneg Φ) (sq_nonneg _)

/-- **The root-class energy of an ordinary polynomial under a selected norm bound.** -/
theorem root_radial_energy_norm (F : O → ℂ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hΦ : ∀ z : O, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) (g : O) (cores : Finset O)
    (hcover : ∀ z, keep z → Φ (‖eisEmbedding z‖^2/K) ≠ 0 → ∃ u ∈ cores, z = u * g^6)
    (q : OrdPoly) (hF : ∀ u ∈ cores, F (u * g^6) = q.eval u)
    (Y δ Kn Xmax X : ℝ) (hnorm : SelectedAllSourceNormBound cores Y δ Kn Xmax) (hX1 : 1 ≤ X)
    (hXmax : X ≤ Xmax) (hq : q.NormLe X) :
    radialEnergy F keep Φ K ≤
      QuadraticInitialBound.diagonalControl Φ * (Kn*(X + Y^(1-δ)*X^δ) * q.mass) := by
  refine (root_radial_energy F keep Φ K hΦ g cores hcover).trans ?_
  apply mul_le_mul_of_nonneg_left _ (QuadraticInitialBound.diagonalControl_nonneg Φ)
  have heq : ∑ u ∈ cores, ‖F (u * g^6)‖^2 = ∑ u ∈ cores, ‖q.eval u‖^2 :=
    Finset.sum_congr rfl (fun u hu => by rw [hF u hu])
  rw [heq]
  exact selected_energy_le cores Y δ Kn Xmax X hnorm q hX1 hXmax hq

end
end QRH.ArviSelectedLeaf.R1
