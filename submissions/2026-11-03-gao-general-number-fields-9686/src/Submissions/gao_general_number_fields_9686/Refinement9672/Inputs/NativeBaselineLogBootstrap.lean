/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9686;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Noncircular successor input module, 2026-11-03, Zhongpai Gao with AI assistance.
Apache-2.0. Original theorem/dependency attribution below is retained.
Input module paths are relocated only; declaration namespaces stay original.
The old Hecke endpoint is supplied from the disjoint frozen original proof DAG.
Full native-import checking and successor endpoint verification remain pending.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.ZeroDetection.Conductors.HolomorphicLogarithmControl

@[expose] public section

noncomputable section
open scoped Classical
open Set Metric Complex

namespace BaselineLogBootstrap

private theorem exp_one_ge_one : (1 : ℝ) ≤ Real.exp 1 :=
  Real.one_le_exp (by norm_num)

/-- Uniform polynomial normalization. All powers and constants precede Q and T. -/
theorem polynomial_absorption (K r v : ℝ) (hK : 0 ≤ K) (hr : 0 ≤ r) (hv : 0 ≤ v) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ Q T : ℝ, 1 ≤ Q → 1 ≤ T →
      K * Q ^ r * T ^ v ≤ (Real.exp 1 * Q * T) ^ M := by
  let p : ℝ := max r v
  have hp : 0 ≤ p := hr.trans (le_max_left _ _)
  obtain ⟨M, hM, hbound⟩ :=
    DedekindZetaZeroFree.LogarithmicControl.absorb_polynomial_constant (K := K) hp
  refine ⟨M, hM, fun Q T hQ hT => ?_⟩
  have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hQT : 1 ≤ Q * T := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hQ) (sub_nonneg.mpr hT)]
  have hC : Real.exp 1 ≤ Real.exp 1 * Q * T := by
    calc Real.exp 1 = Real.exp 1 * 1 := by ring
      _ ≤ Real.exp 1 * (Q * T) := mul_le_mul_of_nonneg_left hQT (Real.exp_pos _).le
      _ = _ := by ring
  have hQT_C : Q * T ≤ Real.exp 1 * Q * T := by
    calc Q * T = 1 * (Q * T) := by ring
      _ ≤ Real.exp 1 * (Q * T) :=
        mul_le_mul_of_nonneg_right exp_one_ge_one (mul_nonneg hQ0 hT0)
      _ = _ := by ring
  have hQr : Q ^ r ≤ Q ^ p :=
    Real.rpow_le_rpow_of_exponent_le hQ (le_max_left _ _)
  have hTv : T ^ v ≤ T ^ p :=
    Real.rpow_le_rpow_of_exponent_le hT (le_max_right _ _)
  calc K * Q ^ r * T ^ v ≤ K * Q ^ p * T ^ p := by gcongr
    _ = K * (Q * T) ^ p := by rw [Real.mul_rpow hQ0 hT0]; ring
    _ ≤ K * (Real.exp 1 * Q * T) ^ p :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (mul_nonneg hQ0 hT0) hQT_C hp) hK
    _ ≤ _ := hbound _ hC

/-- Generic conditional component. The hypotheses identify precisely what must be
hooked to the frozen old all-Hecke theorem and the actual primitive family. -/
theorem subpower_line_97
    {ι : Type*} (L E : ι → ℂ → ℂ) (Q : ι → ℝ)
    (A K r v : ℝ) (hA : 1 ≤ A) (hK : 0 ≤ K) (hr : 0 ≤ r) (hv : 0 ≤ v)
    (hQ : ∀ i, 1 ≤ Q i)
    (hL : ∀ i, Differentiable ℂ (L i))
    (hnz : ∀ i s, (31 / 32 : ℝ) < s.re → L i s ≠ 0)
    (hpoly : ∀ i (t : ℝ) z,
      z ∈ ball ((2 : ℂ) + (t : ℂ) * Complex.I)
        (2 - (31 / 32 : ℝ) - 3 * (1 / 10000 : ℝ)) →
      ‖L i z‖ ≤ K * Q i ^ r * (2 + |t|) ^ v)
    (hE : ∀ i, DifferentiableOn ℂ (E i) {s : ℂ | 1 < s.re})
    (hexp : ∀ i s, (1 : ℝ) < s.re → Complex.exp (E i s) = L i s)
    (hEuler : ∀ i s, (3 / 2 : ℝ) ≤ s.re → ‖E i s‖ ≤ A) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ i (t : ℝ),
      ‖L i (((97 / 100 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * Q i ^ ε * (2 + |t|) := by
  obtain ⟨M, hM, habsorb⟩ := polynomial_absorption K r v hK hr hv
  intro ε hε
  let δ : ℝ := min ε 1
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  obtain ⟨D, hD, hlog⟩ :=
    DedekindZetaZeroFree.LogarithmicControl.logarithmic_control
      (e := (1 / 10000 : ℝ)) (A := A) (M := M) (ε := δ)
      (by norm_num) (by norm_num) hA hM hδ
  refine ⟨D * Real.exp 1, mul_pos hD (Real.exp_pos _), fun i t => ?_⟩
  let c : ℂ := (2 : ℂ) + (t : ℂ) * Complex.I
  let T : ℝ := 2 + |t|
  let V : ℝ := Real.exp 1 * Q i * T
  have hT : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hQi0 : 0 ≤ Q i := zero_le_one.trans (hQ i)
  have hV : Real.exp 1 ≤ V := by
    have hQi : 1 ≤ Q i := hQ i
    have hQT : 1 ≤ Q i * T := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hQi) (sub_nonneg.mpr hT)]
    dsimp [V]
    calc Real.exp 1 = Real.exp 1 * 1 := by ring
      _ ≤ Real.exp 1 * (Q i * T) :=
        mul_le_mul_of_nonneg_left hQT (Real.exp_pos _).le
      _ = _ := by ring
  have hre_of_dist : ∀ z : ℂ, |z.re - 2| ≤ ‖z - c‖ := by
    intro z
    have heq : (z - c).re = z.re - 2 := by simp [c]
    rw [← heq]
    exact Complex.abs_re_le_norm _
  have hEulerBall : ∀ z ∈ ball c (1 / 2 : ℝ), (1 : ℝ) < z.re := by
    intro z hz
    have hd : ‖z - c‖ < (1 / 2 : ℝ) := by simpa [mem_ball, dist_eq_norm] using hz
    have hb := hre_of_dist z
    linarith [neg_le_abs (z.re - 2)]
  have hEulerClosed : ∀ z ∈ closedBall c (49 / 100 : ℝ), (3 / 2 : ℝ) ≤ z.re := by
    intro z hz
    have hd : ‖z - c‖ ≤ (49 / 100 : ℝ) := by simpa [mem_closedBall, dist_eq_norm] using hz
    have hb := hre_of_dist z
    linarith [neg_le_abs (z.re - 2)]
  have hnonzero : ∀ z ∈ ball c (2 - (31 / 32 : ℝ) - 2 * (1 / 10000 : ℝ)),
      L i z ≠ 0 := by
    intro z hz
    have hb := DedekindZetaZeroFree.LogarithmicControl.disk_re_gt hz
    exact hnz i z (by linarith)
  have houter : ∀ z ∈ ball c (2 - (31 / 32 : ℝ) - 3 * (1 / 10000 : ℝ)),
      ‖L i z‖ ≤ V ^ M := by
    intro z hz
    exact (hpoly i t z hz).trans (habsorb (Q i) T (hQ i) hT)
  have hEL : EqOn (Complex.exp ∘ E i) (L i) (ball c (1 / 2 : ℝ)) := by
    intro z hz
    exact hexp i z (hEulerBall z hz)
  have hEb : ∀ z ∈ closedBall c (49 / 100 : ℝ), ‖E i z‖ ≤ A :=
    fun z hz => hEuler i z (hEulerClosed z hz)
  have hb := (hlog (31 / 32) V (L i) (E i) c (by norm_num) (by norm_num) hV
    (hL i).differentiableOn hnonzero houter
    ((hE i).mono (fun z hz => hEulerBall z hz)) hEL hEb).1
  have hpoint : (((97 / 100 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ∈
      closedBall c (2 - (31 / 32 : ℝ) - 6 * (1 / 10000 : ℝ)) := by
    rw [mem_closedBall, dist_eq_norm]
    have heq : (((97 / 100 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - c =
        (((97 / 100 - 2 : ℝ)) : ℂ) := by dsimp [c]; push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hbase : ‖L i (((97 / 100 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ D * V ^ δ :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans (hb _ hpoint)
  have hexpδ : (Real.exp 1) ^ δ ≤ Real.exp 1 := by
    calc (Real.exp 1) ^ δ ≤ (Real.exp 1) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le exp_one_ge_one hδ1
      _ = _ := Real.rpow_one _
  have hQδ : Q i ^ δ ≤ Q i ^ ε := Real.rpow_le_rpow_of_exponent_le (hQ i) hδε
  have hTδ : T ^ δ ≤ T := by
    calc T ^ δ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT hδ1
      _ = T := Real.rpow_one _
  have hVpow : V ^ δ ≤ Real.exp 1 * Q i ^ ε * T := by
    dsimp [V]
    rw [Real.mul_rpow (mul_nonneg (Real.exp_pos _).le hQi0) hT0,
      Real.mul_rpow (Real.exp_pos _).le hQi0]
    exact mul_le_mul (mul_le_mul hexpδ hQδ (Real.rpow_nonneg hQi0 _) (Real.exp_pos _).le)
      hTδ (Real.rpow_nonneg hT0 _) (by positivity)
  calc ‖L i (((97 / 100 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ D * V ^ δ := hbase
    _ ≤ D * (Real.exp 1 * Q i ^ ε * T) := mul_le_mul_of_nonneg_left hVpow hD.le
    _ = (D * Real.exp 1) * Q i ^ ε * (2 + |t|) := by dsimp [T]; ring

#print axioms polynomial_absorption
#print axioms subpower_line_97

end BaselineLogBootstrap
