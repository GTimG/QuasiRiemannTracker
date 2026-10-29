/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.FinePointwisePrice

/-! A full amplitude supremum. The index contains both the density and
amplitude labels; no endpoint-maximization shortcut is part of this Price. -/
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open Set
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.Density

private theorem linear_increment_le {a L : ℝ} (ha : |a| ≤ L) (d : ℝ) :
    a*d ≤ L*|d| := by
  calc a*d ≤ |a * d| := le_abs_self _
       _ = |a| * |d| := abs_mul _ _
       _ ≤ L*|d| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)

structure WeightedFamily where
  Index : Type
  nonempty : Nonempty Index
  density : Index → ℝ
  amplitude : Index → ℝ
  rate : Index → ℝ
  density_mem : ∀ i, density i ∈ Icc (0:ℝ) (3/4)
  amplitude_mem : ∀ i, amplitude i ∈ Icc (0:ℝ) (3/4)
  rate_mem : ∀ i, rate i ∈ Icc (0:ℝ) 1

namespace WeightedFamily
variable (F : WeightedFamily)

def term (i : F.Index) (P s M : ℝ) : ℝ :=
  F.density i*P+(F.rate i-1)*M+F.amplitude i*s

theorem term_lip (i : F.Index) (P s M dP ds dM : ℝ) :
    F.term i (P+dP) (s+ds) (M+dM) ≤ F.term i P s M+
      (3/4:ℝ)*|dP|+(3/4:ℝ)*|ds|+|dM| := by
  have hp := linear_increment_le
    (show |F.density i| ≤ (3/4:ℝ) by rw [abs_of_nonneg (F.density_mem i).1]; exact (F.density_mem i).2) dP
  have hs := linear_increment_le
    (show |F.amplitude i| ≤ (3/4:ℝ) by rw [abs_of_nonneg (F.amplitude_mem i).1]; exact (F.amplitude_mem i).2) ds
  have hm := linear_increment_le
    (show |F.rate i-1| ≤ (1:ℝ) by rw [abs_of_nonpos (by linarith [(F.rate_mem i).2])]; linarith [(F.rate_mem i).1]) dM
  unfold term
  linarith

def high (P s M : ℝ) : ℝ := ⨆ i : F.Index, F.term i P s M

theorem bounded (P s M : ℝ) : BddAbove (range fun i : F.Index => F.term i P s M) := by
  refine ⟨(3/4:ℝ)*|P|+(3/4:ℝ)*|s|+|M|, ?_⟩
  rintro _ ⟨i,rfl⟩
  simpa [term] using F.term_lip i 0 0 0 P s M

theorem term_le (i : F.Index) (P s M : ℝ) : F.term i P s M ≤ F.high P s M :=
  le_ciSup (F.bounded P s M) i

theorem high_le {P s M a : ℝ} (h : ∀ i, F.term i P s M ≤ a) : F.high P s M ≤ a := by
  haveI : Nonempty F.Index := F.nonempty
  exact ciSup_le h

theorem high_lip (P s M dP ds dM : ℝ) :
    F.high (P+dP) (s+ds) (M+dM) ≤ F.high P s M+
      (3/4:ℝ)*|dP|+(3/4:ℝ)*|ds|+|dM| := by
  apply F.high_le
  intro i
  exact (F.term_lip i P s M dP ds dM).trans (by linarith [F.term_le i P s M])

theorem high_mono {P P' s s' M : ℝ} (hP : P' ≤ P) (hs : s' ≤ s) :
    F.high P' s' M ≤ F.high P s M := by
  apply F.high_le
  intro i
  have hp := mul_le_mul_of_nonneg_left hP (F.density_mem i).1
  have hslot := mul_le_mul_of_nonneg_left hs (F.amplitude_mem i).1
  have hi := F.term_le i P s M
  unfold term at *
  linarith
end WeightedFamily

/-- Global extension of the weighted HIGH supremum and genuine LOW deletion
price. The family may depend on the live width, never on P, s or M. -/
def weightedPrice (B0 L0 c0 : ℝ) (hL : 0 < L0)
    (q : ℝ → ℝ) (hq : ∀ w, q w ∈ Icc (0:ℝ) 1)
    (family : ℝ → WeightedFamily) : QRH.SilDensitySplit.CubeFree.Price where
  f w P s M := max (q w*deletionNeed B0 L0 c0 P s M) ((family w).high P s M)
  nonneg w P s M := le_max_of_le_left (mul_nonneg (hq w).1 (deletionNeed_nonneg _ _ _ _ _ _))
  mono w P P' s s' M hP hs := max_le_max
    (mul_le_mul_of_nonneg_left (deletionNeed_mono hL hP hs) (hq w).1)
    ((family w).high_mono hP hs)
  lip := needLip B0 L0 c0
  lip_nonneg := zero_le_one.trans (one_le_needLip _ _ _)
  lipP w P s M d hd := by
    apply max_le_max_add
    · exact lowPart_lip (hq w).1 (hq w).2
        (mul_nonneg (zero_le_one.trans (one_le_needLip _ _ _)) hd)
        (deletionNeed_lipP hL hd)
    · have h := (family w).high_lip P s M d 0 0
      simp only [add_zero, abs_zero, mul_zero, abs_of_nonneg hd] at h
      have hK := one_le_needLip B0 L0 c0
      nlinarith
  lipS w P s M d hd := by
    apply max_le_max_add
    · exact lowPart_lip (hq w).1 (hq w).2
        (mul_nonneg (zero_le_one.trans (one_le_needLip _ _ _)) hd)
        (deletionNeed_lipS hL hd)
    · have h := (family w).high_lip P s M 0 d 0
      simp only [add_zero, abs_zero, mul_zero, zero_add, abs_of_nonneg hd] at h
      have hK := one_le_needLip B0 L0 c0
      nlinarith
  lipM w P s M d := by
    apply max_le_max_add
    · exact lowPart_lip (hq w).1 (hq w).2
        (mul_nonneg (zero_le_one.trans (one_le_needLip _ _ _)) (abs_nonneg d))
        (deletionNeed_lipM hL)
    · have h := (family w).high_lip P s M 0 0 d
      simp only [add_zero, abs_zero, mul_zero] at h
      have hK := one_le_needLip B0 L0 c0
      nlinarith [abs_nonneg d]

end
end Qrh.JointDetector.RepeatedMarks
