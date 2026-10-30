/-
The selected-leaf price.

Rows whose deleted slots carry little mass delete them at the selected cut `K` (in place of the
native `3/4`); rows whose deleted slots carry large mass are priced by the reflected selected
large sieve summed over sixth roots, whose excess over the envelope is

  `selExcess P s M = max 0 (P + s + max 0 ((M - P)/5) - M)`.

The leaf price is the larger of the two (`e5Price`).
-/
import Submissions.sil_density_split_20261026.CubeFree.Price

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf
noncomputable section
open QRH.SilDensitySplit.CubeFree

/-- Excess of the reflected selected large sieve over the envelope `M`, at ordinary width `P` and
marked width `s`: the root sum costs `(M - P)₊/5`. -/
def selExcess (P s M : ℝ) : ℝ := max 0 (P + s + max 0 ((M - P)/5) - M)

theorem selExcess_nonneg (P s M : ℝ) : 0 ≤ selExcess P s M := le_max_left _ _

theorem selExcess_mono {P P' s s' M : ℝ} (hP : P' ≤ P) (hs : s' ≤ s) :
    selExcess P' s' M ≤ selExcess P s M := by
  unfold selExcess
  apply max_le_max le_rfl
  rcases le_total 0 ((M - P')/5) with h | h <;> rcases le_total 0 ((M - P)/5) with h' | h'
  · rw [max_eq_right h, max_eq_right h']; linarith
  · rw [max_eq_right h, max_eq_left h']; linarith
  · rw [max_eq_left h, max_eq_right h']; linarith
  · rw [max_eq_left h, max_eq_left h']; linarith

/-- The selected price as a Seam A price (Lipschitz constant `2`). -/
def selPrice : Price where
  f _ P s M := selExcess P s M
  nonneg _ P s M := selExcess_nonneg P s M
  mono _ _ _ _ _ _ hP hs := selExcess_mono hP hs
  lip := 2
  lip_nonneg := by norm_num
  lipP _ P s M δ hδ := by
    unfold selExcess
    have h1 : max 0 ((M - (P+δ))/5) ≤ max 0 ((M - P)/5) :=
      max_le_max le_rfl (by linarith)
    have h2 : (P + δ) + s + max 0 ((M - (P+δ))/5) - M ≤
        (P + s + max 0 ((M - P)/5) - M) + 2*δ := by linarith
    calc max 0 ((P + δ) + s + max 0 ((M - (P+δ))/5) - M)
        ≤ max 0 ((P + s + max 0 ((M - P)/5) - M) + 2*δ) := max_le_max le_rfl h2
      _ ≤ max 0 (P + s + max 0 ((M - P)/5) - M) + 2*δ :=
          max_le (by positivity) (by linarith [le_max_right 0 (P + s + max 0 ((M - P)/5) - M)])
  lipS _ P s M δ hδ := by
    unfold selExcess
    calc max 0 (P + (s+δ) + max 0 ((M - P)/5) - M)
        ≤ max 0 (P + s + max 0 ((M - P)/5) - M) + δ :=
          max_le (by positivity) (by linarith [le_max_right 0 (P + s + max 0 ((M - P)/5) - M)])
      _ ≤ max 0 (P + s + max 0 ((M - P)/5) - M) + 2*δ := by linarith
  lipM _ P s M δ := by
    unfold selExcess
    have hab := abs_nonneg δ
    have hd1 := neg_abs_le δ
    have hd2 := le_abs_self δ
    have h1 : max 0 ((M + δ - P)/5) ≤ max 0 ((M - P)/5) + |δ|/5 := by
      apply max_le (by positivity)
      have := le_max_right 0 ((M - P)/5)
      linarith
    calc max 0 (P + s + max 0 ((M + δ - P)/5) - (M + δ))
        ≤ max 0 ((P + s + max 0 ((M - P)/5) - M) + 2*|δ|) :=
          max_le_max le_rfl (by linarith)
      _ ≤ max 0 (P + s + max 0 ((M - P)/5) - M) + 2*|δ| :=
          max_le (by positivity) (by linarith [le_max_right 0 (P + s + max 0 ((M - P)/5) - M)])

theorem selPrice_f (w P s M : ℝ) : selPrice.f w P s M = selExcess P s M := rfl

/-- The larger of two Seam A prices is a Seam A price. -/
def maxPrice (p q : Price) : Price where
  f w P s M := max (p.f w P s M) (q.f w P s M)
  nonneg w P s M := (p.nonneg w P s M).trans (le_max_left _ _)
  mono w P P' s s' M hP hs := max_le_max (p.mono w P P' s s' M hP hs) (q.mono w P P' s s' M hP hs)
  lip := max p.lip q.lip
  lip_nonneg := p.lip_nonneg.trans (le_max_left _ _)
  lipP w P s M δ hδ := by
    have h1 := p.lipP w P s M δ hδ
    have h2 := q.lipP w P s M δ hδ
    have e1 : p.lip*δ ≤ max p.lip q.lip*δ := mul_le_mul_of_nonneg_right (le_max_left _ _) hδ
    have e2 : q.lip*δ ≤ max p.lip q.lip*δ := mul_le_mul_of_nonneg_right (le_max_right _ _) hδ
    exact max_le (by linarith [le_max_left (p.f w P s M) (q.f w P s M)])
      (by linarith [le_max_right (p.f w P s M) (q.f w P s M)])
  lipS w P s M δ hδ := by
    have h1 := p.lipS w P s M δ hδ
    have h2 := q.lipS w P s M δ hδ
    have e1 : p.lip*δ ≤ max p.lip q.lip*δ := mul_le_mul_of_nonneg_right (le_max_left _ _) hδ
    have e2 : q.lip*δ ≤ max p.lip q.lip*δ := mul_le_mul_of_nonneg_right (le_max_right _ _) hδ
    exact max_le (by linarith [le_max_left (p.f w P s M) (q.f w P s M)])
      (by linarith [le_max_right (p.f w P s M) (q.f w P s M)])
  lipM w P s M δ := by
    have h1 := p.lipM w P s M δ
    have h2 := q.lipM w P s M δ
    have e1 : p.lip*|δ| ≤ max p.lip q.lip*|δ| :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg δ)
    have e2 : q.lip*|δ| ≤ max p.lip q.lip*|δ| :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg δ)
    exact max_le (by linarith [le_max_left (p.f w P s M) (q.f w P s M)])
      (by linarith [le_max_right (p.f w P s M) (q.f w P s M)])

theorem maxPrice_f (p q : Price) (w P s M : ℝ) :
    (maxPrice p q).f w P s M = max (p.f w P s M) (q.f w P s M) := rfl

/-- **The selected-leaf price**: deletion at the cut `K` against the parent face, or the reflected
selected large sieve, whichever is larger. -/
def e5Price (K B₀ L₀ c₀ : ℝ) (hK : 0 ≤ K) (hL : 0 < L₀) : Price :=
  maxPrice (parentPrice K B₀ L₀ c₀ hK hL) selPrice

theorem e5Price_f (K B₀ L₀ c₀ : ℝ) (hK : 0 ≤ K) (hL : 0 < L₀) (w P s M : ℝ) :
    (e5Price K B₀ L₀ c₀ hK hL).f w P s M =
      max (K * deletionNeed B₀ L₀ c₀ P s M) (selExcess P s M) := rfl

end
end QRH.ArviSelectedLeaf
