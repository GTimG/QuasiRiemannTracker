/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.SelectedTails

/-!
# Physical selected-pair tail

The pair transform has scale `L / (Nr * Ns)` and prefactor
`L / sqrt (Nr * Ns)`. This file matches both to the actual radial tail,
retaining arbitrary Gauss phases of norm at most one.
-/

namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

/-- The genuine dyadic pair scale, prefactor and far-frequency cutoff imply
an absolute tail bound for the actual `paperRadialFourier` kernel. -/
theorem physical_pair_radial_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {R : Type*} [Fintype R] (W : 𝓢(ℝ, ℂ))
        (frequencies : Set O) (B L T : ℝ),
      0 < B → 0 < L → 0 ≤ T →
      ∀ (rowNorm : R → ℝ), (∀ r, B ≤ rowNorm r) → (∀ r, rowNorm r ≤ 2 * B) →
      (∀ h ∈ frequencies, (4 * B ^ 2 / L) * T ≤ ‖eisEmbedding h‖ ^ 2) →
      ∀ G : R → R → O → ℂ, (∀ r t h, h ∈ frequencies → ‖G r t h‖ ≤ 1) →
      ∀ z : R → ℂ,
      ‖∑ r, ∑ t, (z r * star (z t)) *
          (∑' h : frequencies,
            (((L / Real.sqrt (rowNorm r * rowNorm t) : ℝ) : ℂ) * G r t h.val) *
              paperRadialFourier W
                ((L / (rowNorm r * rowNorm t)) * ‖eisEmbedding h.val‖ ^ 2))‖ ≤
        (L / B) * (Fintype.card R : ℝ) * (∑ r, ‖z r‖ ^ 2) *
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            ((min 1 (L / (4 * B ^ 2))) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, htail⟩ := selected_pair_radial_tail A
  refine ⟨s, C, hC, ?_⟩
  intro R _ W frequencies B L T hB hL hT rowNorm hlo hhi hfreq G hG z
  have hpos (r : R) : 0 < rowNorm r := hB.trans_le (hlo r)
  have hprod (r t : R) : rowNorm r * rowNorm t ≤ 4 * B ^ 2 := by
    calc
      _ ≤ (2 * B) * (2 * B) :=
        mul_le_mul (hhi r) (hhi t) (hpos t).le (by positivity)
      _ = _ := by ring
  have hscale (r t : R) : L / (4 * B ^ 2) ≤ L / (rowNorm r * rowNorm t) :=
    div_le_div_of_nonneg_left hL.le (mul_pos (hpos r) (hpos t)) (hprod r t)
  have hfreq' (h : O) (hh : h ∈ frequencies) :
      T ≤ (L / (4 * B ^ 2)) * ‖eisEmbedding h‖ ^ 2 := by
    calc
      T = (L / (4 * B ^ 2)) * ((4 * B ^ 2 / L) * T) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hfreq h hh) (by positivity)
  have hq (r t : R) (h : O) (hh : h ∈ frequencies) :
      ‖(((L / Real.sqrt (rowNorm r * rowNorm t) : ℝ) : ℂ) * G r t h)‖ ≤ L / B := by
    have hroot : B ≤ Real.sqrt (rowNorm r * rowNorm t) := by
      apply (Real.le_sqrt hB.le (mul_pos (hpos r) (hpos t)).le).2
      simpa only [pow_two] using
        mul_le_mul (hlo r) (hlo t) hB.le (hpos r).le
    calc
      _ = (L / Real.sqrt (rowNorm r * rowNorm t)) * ‖G r t h‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hL.le (Real.sqrt_nonneg _))]
      _ ≤ L / Real.sqrt (rowNorm r * rowNorm t) :=
        mul_le_of_le_one_right (by positivity) (hG r t h hh)
      _ ≤ _ := div_le_div_of_nonneg_left hL.le hB hroot
  exact htail W frequencies (L / (4 * B ^ 2)) T (L / B) (by positivity)
    hT (by positivity) hfreq' (fun r t => L / (rowNorm r * rowNorm t)) hscale
    (fun r t h => (((L / Real.sqrt (rowNorm r * rowNorm t) : ℝ) : ℂ) * G r t h)) hq z


/-- The physical tail prefactor has polynomial growth at most `Z^(7P)`.
The numerical loss is then absorbed by the chosen Schwartz decay order. -/
theorem physical_tail_budget_le
    (Z P B L ε N n C₀ Crows : ℝ) (A : ℕ)
    (hZ : 2 ≤ Z) (hP : 0 ≤ P) (hB : 1 ≤ B) (hBU : B ≤ Z ^ P)
    (hL : 0 < L) (hLlo : Z ^ (-P) ≤ L) (hLhi : L ≤ Z ^ P)
    (hrows : n ≤ Crows * B) (hCrows : 0 ≤ Crows) (hC₀ : 0 ≤ C₀)
    (hA : N + 7 * P ≤ ε * (A : ℝ)) :
    (L / B) * n * C₀ /
        ((min 1 (L / (4 * B ^ 2))) ^ 2 * (1 + Z ^ ε) ^ A) ≤
      16 * Crows * C₀ * Z ^ (-N) := by
  have hZ0 : 0 < Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hB0 : 0 < B := by linarith
  let U := Z ^ P
  have hU1 : 1 ≤ U := by
    dsimp [U]
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hZ1 hP
  have hU0 : 0 < U := by linarith
  have hBU' : B ≤ U := hBU
  have hLhi' : L ≤ U := hLhi
  have hLlo' : 1 / U ≤ L := by
    simpa only [U, Real.rpow_neg hZ0.le, one_div] using hLlo
  let M := 4 * U ^ 3
  have hM1 : 1 ≤ M := by
    have := one_le_pow₀ hU1 (n := 3)
    dsimp [M]
    linarith
  have hM0 : 0 < M := by linarith
  have hlow : 1 / M ≤ min 1 (L / (4 * B ^ 2)) := by
    apply le_min
    · exact (div_le_iff₀ hM0).2 (by simpa using hM1)
    · calc
        1 / M = (1 / U) / (4 * U ^ 2) := by dsimp [M]; field_simp
        _ ≤ L / (4 * B ^ 2) := by
          apply div_le_div₀ hL.le hLlo' (by positivity)
          gcongr
  let δ := min 1 (L / (4 * B ^ 2))
  have hδ0 : 0 < δ := lt_min zero_lt_one (by positivity)
  have hMδ : 1 ≤ M * δ := by
    have := (div_le_iff₀ hM0).1 hlow
    simpa only [δ, mul_comm] using this
  have hMδsq : 1 ≤ M ^ 2 * δ ^ 2 := by
    have := one_le_pow₀ hMδ (n := 2)
    simpa only [mul_pow, one_pow] using this
  have hpref : (L / B) * n ≤ Crows * U := by
    calc
      _ ≤ (L / B) * (Crows * B) := mul_le_mul_of_nonneg_left hrows (by positivity)
      _ = Crows * L := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hLhi' hCrows
  have hnum : (L / B) * n * C₀ / δ ^ 2 ≤ (Crows * U * C₀) * M ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hδ0)).2
    calc
      _ ≤ Crows * U * C₀ := mul_le_mul_of_nonneg_right hpref hC₀
      _ ≤ (Crows * U * C₀) * (M ^ 2 * δ ^ 2) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hMδsq
          (show 0 ≤ Crows * U * C₀ by positivity)
      _ = _ := by ring
  have hpow : U ^ 7 / (Z ^ ε) ^ A ≤ Z ^ (-N) := by
    have hU7 : U ^ 7 = Z ^ (7 * P) := by
      dsimp [U]
      rw [← Real.rpow_mul_natCast hZ0.le]
      congr 1
      norm_num
      ring
    rw [hU7, ← Real.rpow_mul_natCast hZ0.le, ← Real.rpow_sub hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  calc
    _ = ((L / B) * n * C₀ / δ ^ 2) / (1 + Z ^ ε) ^ A := by dsimp [δ]; ring
    _ ≤ ((Crows * U * C₀) * M ^ 2) / (1 + Z ^ ε) ^ A :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ ((Crows * U * C₀) * M ^ 2) / (Z ^ ε) ^ A := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by linarith) A
    _ = (16 * Crows * C₀) * (U ^ 7 / (Z ^ ε) ^ A) := by dsimp [M]; ring
    _ ≤ (16 * Crows * C₀) * Z ^ (-N) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)


/-- On polynomial physical scales, the genuine far-frequency pair tail is
smaller than every prescribed power, uniformly in the selected vector. -/
theorem physical_pair_radial_tail_power
    (W : 𝓢(ℝ, ℂ)) (ε N P Crows : ℝ)
    (hε : 0 < ε) (hP : 0 ≤ P) (hCrows : 0 < Crows) :
    ∃ Ctail : ℝ, 0 < Ctail ∧
      ∀ {R : Type*} [Fintype R] (Z B L : ℝ),
      2 ≤ Z → 1 ≤ B → B ≤ Z ^ P → Z ^ (-P) ≤ L → L ≤ Z ^ P →
      (Fintype.card R : ℝ) ≤ Crows * B →
      ∀ (rowNorm : R → ℝ), (∀ r, B ≤ rowNorm r) → (∀ r, rowNorm r ≤ 2 * B) →
      ∀ frequencies : Set O,
      (∀ h ∈ frequencies, (4 * B ^ 2 / L) * Z ^ ε ≤ ‖eisEmbedding h‖ ^ 2) →
      ∀ G : R → R → O → ℂ, (∀ r t h, h ∈ frequencies → ‖G r t h‖ ≤ 1) →
      ∀ z : R → ℂ,
      ‖∑ r, ∑ t, (z r * star (z t)) *
          (∑' h : frequencies,
            (((L / Real.sqrt (rowNorm r * rowNorm t) : ℝ) : ℂ) * G r t h.val) *
              paperRadialFourier W
                ((L / (rowNorm r * rowNorm t)) * ‖eisEmbedding h.val‖ ^ 2))‖ ≤
        Ctail * Z ^ (-N) * ∑ r, ‖z r‖ ^ 2 := by
  obtain ⟨A, hAge⟩ := exists_nat_ge ((N + 7 * P) / ε)
  have hA : N + 7 * P ≤ ε * (A : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hε).1 hAge
  obtain ⟨s, C, hC, htail⟩ := physical_pair_radial_tail A
  let C₀ := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hC₀ : 0 ≤ C₀ := mul_nonneg hC.le (apply_nonneg _ _)
  refine ⟨16 * Crows * (C₀ + 1), by positivity, ?_⟩
  intro R _ Z B L hZ hB hBU hLlo hLhi hrows rowNorm hlo hhi frequencies hfreq G hG z
  have hZ0 : 0 < Z := by linarith
  have hB0 : 0 < B := by linarith
  have hL0 : 0 < L := (Real.rpow_pos_of_pos hZ0 (-P)).trans_le hLlo
  have hmass : 0 ≤ ∑ r, ‖z r‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h := htail W frequencies B L (Z ^ ε) hB0 hL0
    (Real.rpow_nonneg hZ0.le ε) rowNorm hlo hhi hfreq G hG z
  have hbudget := physical_tail_budget_le Z P B L ε N
    (Fintype.card R : ℝ) C₀ Crows A hZ hP hB hBU hL0 hLlo hLhi hrows hCrows.le hC₀ hA
  apply h.trans
  change (L / B) * (Fintype.card R : ℝ) * (∑ r, ‖z r‖ ^ 2) * C₀ /
    ((min 1 (L / (4 * B ^ 2))) ^ 2 * (1 + Z ^ ε) ^ A) ≤ _
  calc
    _ = ((L / B) * (Fintype.card R : ℝ) * C₀ /
        ((min 1 (L / (4 * B ^ 2))) ^ 2 * (1 + Z ^ ε) ^ A)) *
          (∑ r, ‖z r‖ ^ 2) := by ring
    _ ≤ (16 * Crows * C₀ * Z ^ (-N)) * (∑ r, ‖z r‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hbudget hmass
    _ ≤ (16 * Crows * (C₀ + 1)) * Z ^ (-N) * (∑ r, ‖z r‖ ^ 2) := by
      gcongr
      linarith

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.physical_pair_radial_tail
#print axioms Qrh.JointDetector.physical_tail_budget_le
#print axioms Qrh.JointDetector.physical_pair_radial_tail_power
