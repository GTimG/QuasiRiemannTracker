/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.Price
import Submissions.sil_density_split_20261026.Density.Price

/-!
# The joint-detector price in Sil's actual scalar interface

The imported upstream modules are pinned byte-for-byte in the provenance record
`Submissions/sil_density_split_20261026/SOURCE.md`.
This constructs the actual `QRH.SilDensitySplit.CubeFree.Price` structure.
It does not assert an analytic `PricedPackedSource` theorem.
-/

namespace Qrh.JointDetector

noncomputable section

open QRH.SilDensitySplit.CubeFree

/-- The actual upstream price, with an arbitrary uniformly clipped density cut. -/
def jointPrice (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (q : ℝ → ℝ) (hq : ∀ w, q w ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    QRH.SilDensitySplit.CubeFree.Price where
  f w P s M := max
    (QRH.SilDensitySplit.Density.lowPart B₀ L₀ c₀ (q w) P s M)
    (highSup (q w) P s M)
  nonneg w P s M := by
    have hq0 : 0 ≤ q w := by linarith [(hq w).1]
    exact le_max_of_le_left (mul_nonneg hq0 (deletionNeed_nonneg B₀ L₀ c₀ P s M))
  mono w P P' s s' M hP hs := by
    have hq0 : 0 ≤ q w := by linarith [(hq w).1]
    exact max_le_max
      (mul_le_mul_of_nonneg_left (deletionNeed_mono hL hP hs) hq0)
      (highSup_mono (hq w) hP hs)
  lip := needLip B₀ L₀ c₀
  lip_nonneg := zero_le_one.trans (one_le_needLip B₀ L₀ c₀)
  lipP w P s M δ hδ := by
    have hq0 : 0 ≤ q w := by linarith [(hq w).1]
    have hq1 : q w ≤ 1 := by linarith [(hq w).2]
    have hK := one_le_needLip B₀ L₀ c₀
    apply QRH.SilDensitySplit.Density.max_le_max_add
    · exact QRH.SilDensitySplit.Density.lowPart_lip hq0 hq1
        (mul_nonneg (by linarith : 0 ≤ needLip B₀ L₀ c₀) hδ)
        (deletionNeed_lipP hL hδ)
    · have hhigh := highSup_lipP (hq w) P s M δ hδ
      have hscale : (3/4 : ℝ) * δ ≤ needLip B₀ L₀ c₀ * δ :=
        mul_le_mul_of_nonneg_right (by linarith) hδ
      exact hhigh.trans (add_le_add le_rfl hscale)
  lipS w P s M δ hδ := by
    have hq0 : 0 ≤ q w := by linarith [(hq w).1]
    have hq1 : q w ≤ 1 := by linarith [(hq w).2]
    have hK := one_le_needLip B₀ L₀ c₀
    apply QRH.SilDensitySplit.Density.max_le_max_add
    · exact QRH.SilDensitySplit.Density.lowPart_lip hq0 hq1
        (mul_nonneg (by linarith : 0 ≤ needLip B₀ L₀ c₀) hδ)
        (deletionNeed_lipS hL hδ)
    · have hhigh := highSup_lipS (hq w) P s M δ hδ
      have hscale : (3/4 : ℝ) * δ ≤ needLip B₀ L₀ c₀ * δ :=
        mul_le_mul_of_nonneg_right (by linarith) hδ
      exact hhigh.trans (add_le_add le_rfl hscale)
  lipM w P s M δ := by
    have hq0 : 0 ≤ q w := by linarith [(hq w).1]
    have hq1 : q w ≤ 1 := by linarith [(hq w).2]
    have hK := one_le_needLip B₀ L₀ c₀
    apply QRH.SilDensitySplit.Density.max_le_max_add
    · exact QRH.SilDensitySplit.Density.lowPart_lip hq0 hq1
        (mul_nonneg (by linarith : 0 ≤ needLip B₀ L₀ c₀) (abs_nonneg δ))
        (deletionNeed_lipM hL)
    · have hhigh := highSup_lipM (hq w) P s M δ
      have hscale : (61/84 : ℝ) * |δ| ≤ needLip B₀ L₀ c₀ * |δ| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg δ)
      exact hhigh.trans (add_le_add le_rfl hscale)

theorem jointPrice_f (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (q : ℝ → ℝ) (hq : ∀ w, q w ∈ Set.Icc (13/20 : ℝ) (3/4))
    (w P s M : ℝ) :
    (jointPrice B₀ L₀ c₀ hL q hq).f w P s M =
      max (q w * deletionNeed B₀ L₀ c₀ P s M) (highSup (q w) P s M) := rfl

theorem jointPrice_lip (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (q : ℝ → ℝ) (hq : ∀ w, q w ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    (jointPrice B₀ L₀ c₀ hL q hq).lip = needLip B₀ L₀ c₀ := rfl

/-- Specialization to the literal accepted density cut, rather than a substitute. -/
def jointDensityPrice (B₀ L₀ c₀ L A D s₀ : ℝ) (hL : 0 < L₀) :
    QRH.SilDensitySplit.CubeFree.Price :=
  jointPrice B₀ L₀ c₀ hL
    (QRH.SilDensitySplit.Density.densQ B₀ L₀ L A D s₀)
    (fun w => ⟨QRH.SilDensitySplit.Density.densQ_ge B₀ L₀ L A D s₀ w,
      QRH.SilDensitySplit.Density.densQ_le B₀ L₀ L A D s₀ w⟩)

theorem jointDensityPrice_f (B₀ L₀ c₀ L A D s₀ : ℝ) (hL : 0 < L₀)
    (w P s M : ℝ) :
    (jointDensityPrice B₀ L₀ c₀ L A D s₀ hL).f w P s M =
      max
        (QRH.SilDensitySplit.Density.densQ B₀ L₀ L A D s₀ w *
          deletionNeed B₀ L₀ c₀ P s M)
        (highSup (QRH.SilDensitySplit.Density.densQ B₀ L₀ L A D s₀ w) P s M) := rfl

theorem jointDensityPrice_lip (B₀ L₀ c₀ L A D s₀ : ℝ) (hL : 0 < L₀) :
    (jointDensityPrice B₀ L₀ c₀ L A D s₀ hL).lip = needLip B₀ L₀ c₀ := rfl

theorem highSup_le_jointPrice (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (q : ℝ → ℝ) (hq : ∀ w, q w ∈ Set.Icc (13/20 : ℝ) (3/4))
    (w P s M : ℝ) :
    highSup (q w) P s M ≤ (jointPrice B₀ L₀ c₀ hL q hq).f w P s M :=
  le_max_right _ _

theorem g_le_jointPrice (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (q : ℝ → ℝ) (hq : ∀ w, q w ∈ Set.Icc (13/20 : ℝ) (3/4))
    {w ν P s M : ℝ} (hν : ν ∈ Set.Icc (q w) (3/4)) :
    g ν P s M ≤ (jointPrice B₀ L₀ c₀ hL q hq).f w P s M :=
  (le_highSup (hq w).1 hν.1 hν.2 P s M).trans
    (highSup_le_jointPrice B₀ L₀ c₀ hL q hq w P s M)

end

end Qrh.JointDetector
