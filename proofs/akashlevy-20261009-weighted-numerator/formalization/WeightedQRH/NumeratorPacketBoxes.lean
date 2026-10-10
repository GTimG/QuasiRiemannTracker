import WeightedQRH.NumeratorDilationBoxes

/-! Coefficient removal inside a finite dilation box. The polynomial moment
is applied only to active coefficient choices; the resulting packet is
normalized by its actual absolute coefficient mass. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace WeightedQRH.Numerator

variable {ι : Type*} [Fintype ι] {α : ι → Type*}

theorem packet_box_fourth
    (base : ∀ i, α i) (A S : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ)
    (hN : ∀ i e, 0 < N i e) (L : ι → ℝ) (rho U v : ℝ)
    (active : ∀ i, α i → Prop) [∀ i e, Decidable (active i e)]
    (Q : ι → ℂ) (M E : ℝ) (hM : 0 < M) (hU : 0 < U) (hrho : 0 ≤ rho)
    (hlower : ∀ i e, active i e → U^v ≤ max 1 (L i * N i e))
    (hs : ∀ i, Summable (fun e => ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L i * N i e)^rho))
    (hm : ∀ i, (∑' e, ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L i * N i e)^rho) ≤ M)
    (hselection : ∀ e : ∀ i, α i,
      (∑ i, ‖if active i (e i) then S i (e i) else 0‖^4 * ‖Q i‖^2) ≤ E) :
    (∑ i, ‖((U^(rho*v) / M : ℝ) : ℂ) *
      (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) *
        (if active i e then S i e else 0))‖^4 * ‖Q i‖^2) ≤ E := by
  let B (i : ι) (e : α i) := if active i e then S i e else 0
  let T (i : ι) (e : α i) := ((U^(rho*v) : ℝ) : ℂ) * B i e
  have hfactor (i : ι) (e : α i) :
      ‖T i e / ((max 1 (L i * N i e)^rho : ℝ) : ℂ)‖ ≤ ‖B i e‖ := by
    by_cases ha : active i e
    · have hD : 0 < max 1 (L i * N i e)^rho :=
        Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
      have hpow : U^(rho*v) ≤ max 1 (L i * N i e)^rho := by
        calc
          _ = (U^v)^rho := by rw [←Real.rpow_mul hU.le]; congr 1; ring
          _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hU.le _) (hlower i e ha) hrho
      dsimp only [T]
      rw [norm_div,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg hU.le _),
        Complex.norm_real,Real.norm_of_nonneg hD.le]
      exact (div_le_iff₀ hD).mpr (by nlinarith [norm_nonneg (B i e)])
    · simp [T,B,ha]
  have hsel : ∀ e : ∀ i, α i,
      (∑ i, ‖T i (e i) / ((max 1 (L i * N i (e i))^rho : ℝ) : ℂ)‖^4 * ‖Q i‖^2) ≤ E := by
    intro e
    refine (Finset.sum_le_sum (fun i _ => ?_)).trans (hselection e)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hfactor i (e i)) 4) (sq_nonneg _)
  have hp := packet_fourth_selection base A T N hN L rho Q M E hM.le hs hm hsel
  have he (i : ι) :
      (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * T i e) =
      ((U^(rho*v) : ℝ) : ℂ) * (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * B i e) := by
    rw [←tsum_mul_left]
    apply tsum_congr
    intro e
    dsimp only [T]
    ring
  simp only [he] at hp
  have hnorm (i : ι) :
      ‖((U^(rho*v) / M : ℝ) : ℂ) * (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * B i e)‖^4 * ‖Q i‖^2 =
      (‖((U^(rho*v) : ℝ) : ℂ) * (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * B i e)‖^4 * ‖Q i‖^2) / M^4 := by
    rw [Complex.ofReal_div]
    have hmul (z : ℂ) : (((U^(rho*v) : ℝ) : ℂ) / (M : ℂ)) * z = (((U^(rho*v) : ℝ) : ℂ)*z)/(M : ℂ) := by ring
    rw [hmul,norm_div,Complex.norm_real,Real.norm_of_nonneg hM.le,div_pow]
    ring
  change (∑ i, ‖((U^(rho*v) / M : ℝ) : ℂ) * (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * B i e)‖^4 * ‖Q i‖^2) ≤ E
  simp_rw [hnorm]
  rw [←Finset.sum_div]
  exact (div_le_iff₀ (pow_pos hM 4)).mpr (by simpa only [mul_comm E] using hp)

end WeightedQRH.Numerator
