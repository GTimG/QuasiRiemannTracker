import Cycle25.Numerator.Imported.NumeratorPacketMellin
import Cycle25.Numerator.ReflectionMass
import Cycle25.Numerator.ReflectionRetained

/-! Fourth-moment removal of row-dependent numerator coefficient packets. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators Classical
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths Cycle25WeightedNumeratorReflection

theorem packet_fourth_selection {ι : Type*} [Fintype ι] {α : ι → Type*}
    (base : ∀ i, α i) (A S : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ)
    (hN : ∀ i e, 0 < N i e) (L : ι → ℝ) (rho : ℝ) (Q : ι → ℂ) (M E : ℝ)
    (hM : 0 ≤ M)
    (hs : ∀ i, Summable (fun e => ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L i * N i e)^rho))
    (hm : ∀ i, (∑' e, ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L i * N i e)^rho) ≤ M)
    (hselection : ∀ e : ∀ i, α i,
      (∑ i, ‖S i (e i) / ((max 1 (L i * N i (e i))^rho : ℝ) : ℂ)‖^4 * ‖Q i‖^2) ≤ E) :
    (∑ i, ‖∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * S i e‖^4 * ‖Q i‖^2) ≤ M^4 * E := by
  let D (i : ι) (e : α i) : ℝ := max 1 (L i * N i e)^rho
  have hD (i : ι) (e : α i) : 0 < D i e :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) rho
  let w (i : ι) (e : α i) := A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * (D i e : ℂ)
  let f (i : ι) (e : α i) := (S i e / (D i e : ℂ)) * (Real.sqrt ‖Q i‖ : ℂ)
  have hnorm (i : ι) (e : α i) : ‖w i e‖ =
      ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) * max 1 (L i * N i e)^rho := by
    dsimp only [w]
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hN i e),
      show (-(1 / 2 : ℂ)).re = -(1 / 2 : ℝ) by norm_num,
      Complex.norm_real,Real.norm_of_nonneg (hD i e).le]
  have hw : ∀ i, Summable (fun e => ‖w i e‖) := by
    intro i
    simpa only [hnorm] using hs i
  have hwm : ∀ i, (∑' e, ‖w i e‖) ≤ M := by
    intro i
    simpa only [hnorm] using hm i
  have hf : ∀ e : ∀ i, α i, (∑ i, ‖f i (e i)‖^4) ≤ E := by
    intro e
    simpa only [f,norm_mul_sqrt_fourth,D] using hselection e
  have hh := weighted_fourth_selection base w f M E hM hw hwm hf
  have he (i : ι) (e : α i) : w i e * f i e =
      (A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * S i e) * (Real.sqrt ‖Q i‖ : ℂ) := by
    dsimp only [w,f]
    have hd : (D i e : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hD i e).ne'
    field_simp
  have hsum (i : ι) : (∑' e, w i e * f i e) =
      (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * S i e) * (Real.sqrt ‖Q i‖ : ℂ) := by
    simp_rw [he]
    exact tsum_mul_right
  simpa only [hsum,norm_mul_sqrt_fourth] using hh.2

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/
