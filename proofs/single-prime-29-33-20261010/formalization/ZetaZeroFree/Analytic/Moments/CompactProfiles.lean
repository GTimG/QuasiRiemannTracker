import ZetaZeroFree.Analytic.Moments.Sharp

namespace ZetaZeroFree.Analytic.Moments.D3
noncomputable section
open scoped Classical SchwartzMap
open OAI.SevenEighths
open HeckeFamily

/-- The usual finite derivative supremum; on supported smooth tests it is a C^J norm. -/
def compactNorm (J : ℕ) : Seminorm ℝ 𝓢(ℝ, ℂ) :=
  (Finset.range (J + 1)).sup (fun n => SchwartzMap.seminorm ℝ 0 n)

lemma compactNorm_nonneg (J : ℕ) (W : 𝓢(ℝ, ℂ)) : 0 ≤ compactNorm J W :=
  apply_nonneg _ _

lemma derivative_le_compactNorm (J n : ℕ) (hn : n ≤ J)
    (W : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (W : ℝ → ℂ) x‖ ≤ compactNorm J W :=
  (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ W n x).trans
    (Seminorm.le_finset_sup_apply (Finset.mem_range.mpr (by omega)))

def supportRadius (a b : ℝ) : ℝ := max 1 (max |a| |b|)

lemma supportRadius_ge_one (a b : ℝ) : 1 ≤ supportRadius a b := le_max_left _ _

lemma norm_le_supportRadius (a b x : ℝ) (hx : x ∈ Set.Icc a b) :
    ‖x‖ ≤ supportRadius a b := by
  have ha : |a| ≤ supportRadius a b := (le_max_left _ _).trans (le_max_right _ _)
  have hb : |b| ≤ supportRadius a b := (le_max_right _ _).trans (le_max_right _ _)
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨(neg_le_neg ha).trans ((neg_abs_le a).trans hx.1),
    hx.2.trans ((le_abs_self b).trans hb)⟩

theorem seminorm_le_compactNorm (a b : ℝ) (J K k n : ℕ)
    (hk : k ≤ K) (hn : n ≤ J) (W : 𝓢(ℝ, ℂ))
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) :
    SchwartzMap.seminorm ℝ k n W ≤ supportRadius a b ^ K * compactNorm J W := by
  apply SchwartzMap.seminorm_le_bound ℝ k n W (by
    exact mul_nonneg (pow_nonneg (zero_le_one.trans (supportRadius_ge_one a b)) _)
      (compactNorm_nonneg J W))
  intro x
  by_cases hx : x ∈ Set.Icc a b
  · have hpow : ‖x‖ ^ k ≤ supportRadius a b ^ K :=
      (pow_le_pow_left₀ (norm_nonneg _) (norm_le_supportRadius a b x hx) k).trans
        (pow_le_pow_right₀ (supportRadius_ge_one a b) hk)
    exact mul_le_mul hpow (derivative_le_compactNorm J n hn W x)
      (norm_nonneg _) (pow_nonneg (zero_le_one.trans (supportRadius_ge_one a b)) _)
  · have hd : iteratedFDeriv ℝ n (W : ℝ → ℂ) x = 0 := by
      by_contra hd
      have hx' := support_iteratedFDeriv_subset (𝕜 := ℝ) (f := (W : ℝ → ℂ)) n hd
      exact hx ((closure_minimal hs isClosed_Icc) hx')
    rw [hd, norm_zero, mul_zero]
    exact mul_nonneg (pow_nonneg (zero_le_one.trans (supportRadius_ge_one a b)) _)
      (compactNorm_nonneg J W)

theorem finite_schwartz_le_compactNorm (a b : ℝ) (S : Finset (ℕ × ℕ))
    (W : 𝓢(ℝ, ℂ))
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) :
    S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤
      supportRadius a b ^ (S.sup Prod.fst) * compactNorm (S.sup Prod.snd) W := by
  apply Seminorm.finset_sup_apply_le (mul_nonneg
    (pow_nonneg (zero_le_one.trans (supportRadius_ge_one a b)) _)
    (compactNorm_nonneg _ _))
  intro p hp
  exact seminorm_le_compactNorm a b (S.sup Prod.snd) (S.sup Prod.fst) p.1 p.2
    (Finset.le_sup (f := Prod.fst) hp) (Finset.le_sup (f := Prod.snd) hp) W hs

theorem compactNorm_mono (J K : ℕ) (hJK : J ≤ K) (W : 𝓢(ℝ, ℂ)) :
    compactNorm J W ≤ compactNorm K W := by
  apply Seminorm.finset_sup_apply_le (compactNorm_nonneg K W)
  intro n hn
  exact Seminorm.le_finset_sup_apply (Finset.mem_range.mpr (by
    have hn' := Finset.mem_range.mp hn
    omega))

theorem finite_schwartz_le_compactNorm_of_order (a b : ℝ) (S : Finset (ℕ × ℕ))
    (J : ℕ) (hJ : S.sup Prod.snd ≤ J) (W : 𝓢(ℝ, ℂ))
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) :
    S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤
      supportRadius a b ^ (S.sup Prod.fst) * compactNorm J W :=
  (finite_schwartz_le_compactNorm a b S W hs).trans
    (mul_le_mul_of_nonneg_left (compactNorm_mono _ _ hJ W)
      (pow_nonneg (zero_le_one.trans (supportRadius_ge_one a b)) _))

end
end ZetaZeroFree.Analytic.Moments.D3

