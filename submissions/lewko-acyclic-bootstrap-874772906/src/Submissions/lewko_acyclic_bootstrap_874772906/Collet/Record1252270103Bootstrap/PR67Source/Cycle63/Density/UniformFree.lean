import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Density.SmallHeight
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Density.CountingSetup
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OAI
noncomputable section
open scoped Classical BigOperators
open Set Filter
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros ProbeHighRowFamily

/-- The independent height is chosen after the returned moment degree, which precedes the dictionary.
The eventual threshold is common to every boundary and every height. -/
theorem actual_uniform_free_density_normalized {Label : Type*} [Fintype Label]
    (loss : ℝ) (hloss : 0 < loss) (hβhi : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃ J : ℕ, ∀ D : FixedUnmarkedDictionary Label, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ a T : ℝ, 4/5 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, rowNorm u ≤ U ∧ rawZeroBin D.data a (7/8) T ⟨u.val, u.property.1⟩) →
      (∀ u ∈ rows, ∀ j, ((D.naturalFamily u j).modulus.absNorm : ℝ) ≤ U) →
        (rows.card : ℝ) ≤ C*(1+T)^J*U^(unmarkedDensity (2*a-1)+loss) := by
  by_cases hβlo : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta
  · let ε : ℝ := min (loss/1000) (1/1000)
    let e : ℝ := min (ε/2000) (1/2000)
    have hε : 0 < ε := lt_min (by positivity) (by norm_num)
    have hεcap : ε ≤ 1/1000 := min_le_right _ _
    have hεloss : ε ≤ loss/1000 := min_le_left _ _
    have he : 0 < e := lt_min (by positivity) (by norm_num)
    have heε : e ≤ ε/2000 := min_le_left _ _
    have hecap : e ≤ 1/2000 := min_le_right _ _
    obtain ⟨J₀, hsmall⟩ := actual_small_height_density (Label := Label)
      canonicalDensityCountingSetup (loss/10) (loss/10) ε e e e
      (by positivity) (by positivity) hε hεcap he (by linarith)
      he (by linarith) he.le (by linarith) hβlo hβhi
    let τ : ℝ := min (e/8) (min (loss/(10*((J₀ : ℝ)+1))) (1/4))
    have hJ : 0 ≤ (J₀ : ℝ) := Nat.cast_nonneg _
    have hτ : 0 < τ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
    have hτe : τ ≤ e/8 := min_le_left _ _
    have hτcap : τ ≤ 1/4 := (min_le_right _ _).trans (min_le_right _ _)
    have hτloss : τ ≤ loss/(10*((J₀ : ℝ)+1)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hτbudget : (J₀ : ℝ)*τ ≤ loss/10 := by
      have h := (le_div_iff₀ (by positivity : 0 < 10*((J₀ : ℝ)+1))).mp hτloss
      nlinarith
    have hbudget : 156*ε+loss/10+loss/10+3*e+(J₀ : ℝ)*τ ≤ loss := by
      linarith
    let J : ℕ := ⌈(1 : ℝ)/τ⌉₊
    have hJτ : 1 ≤ τ*(J : ℝ) := by
      have h := Nat.le_ceil ((1 : ℝ)/τ)
      have hh := (div_le_iff₀ hτ).mp h
      dsimp [J]
      nlinarith
    refine ⟨J, fun D => ?_⟩
    obtain ⟨C₀, hC₀, hsmall⟩ := hsmall D
    let C : ℝ := C₀+129
    have hC : 0 < C := by dsimp [C]; linarith
    refine ⟨C, hC, ?_⟩
    filter_upwards [hsmall τ hτ (by linarith) (by linarith)] with U hs
    have hUp : 0 < U := zero_lt_one.trans hs.1
    refine ⟨hs.1, ?_⟩
    intro a T ha ha' hT rows hrows hmod
    have hδcap : 2*a-1 ≤ 3/4 := by linarith
    have hρ : 0 ≤ unmarkedDensity (2*a-1)+loss := by
      linarith [unmarkedDensity_ge_two_sevenths hδcap]
    have hweight : 1 ≤ (1+T)^J := one_le_pow₀ (by linarith)
    have hpower : 1 ≤ U^(unmarkedDensity (2*a-1)+loss) := Real.one_le_rpow hs.1.le hρ
    by_cases ht : T ≤ U^τ
    · have hh := hs.2 a T ha ha' ht rows hrows hmod
      apply hh.trans
      have hexp : unmarkedDensity (2*a-1)+156*ε+loss/10+loss/10+3*e+(J₀ : ℝ)*τ ≤
          unmarkedDensity (2*a-1)+loss := by linarith
      calc
        _ ≤ C₀*U^(unmarkedDensity (2*a-1)+loss) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hs.1.le hexp) hC₀
        _ ≤ C*(1+T)^J*U^(unmarkedDensity (2*a-1)+loss) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hUp.le _)
          dsimp [C]
          nlinarith
    · have ht' : U^τ ≤ 1+T := by linarith [lt_of_not_ge ht]
      have hheight : U ≤ (1+T)^J := by
        calc
          U = U^(1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ U^(τ*(J : ℝ)) := Real.rpow_le_rpow_of_exponent_le hs.1.le hJτ
          _ = (U^τ)^J := by rw [Real.rpow_mul hUp.le, Real.rpow_natCast]
          _ ≤ (1+T)^J := pow_le_pow_left₀ (Real.rpow_nonneg hUp.le _) ht' J
      have hc := freeRow_count rows U hs.1.le (fun u hu => (hrows u hu).1)
      calc
        (rows.card : ℝ) ≤ 128*U := hc
        _ ≤ 128*(1+T)^J := mul_le_mul_of_nonneg_left hheight (by norm_num)
        _ ≤ C*(1+T)^J := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)
        _ ≤ C*(1+T)^J*U^(unmarkedDensity (2*a-1)+loss) :=
          le_mul_of_one_le_right (by positivity) hpower
  · refine ⟨0, fun D => ⟨1, by norm_num, ?_⟩⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with U hU
    refine ⟨hU, ?_⟩
    intro a T ha ha' hT rows hrows hmod
    have hnone : rows = ∅ := by
      by_contra hn
      have hne := Finset.nonempty_iff_ne_empty.mpr hn
      exact hβlo (beta_lower_of_nonempty_bin D.data a (7/8) T (by linarith)
        rows hne (fun u hu => (hrows u hu).2))
    rw [hnone, Finset.card_empty, Nat.cast_zero]
    positivity

end SevenEighths.LocalMoment
end
end OAI

end Record1252270103Bootstrap.PR67
