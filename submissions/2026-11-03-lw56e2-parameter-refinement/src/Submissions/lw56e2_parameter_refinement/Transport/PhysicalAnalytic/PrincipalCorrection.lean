/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalAnalytic/PrincipalCorrection.lean
Original SHA-256: 39c1f3b67d4d33f37fffabbe010baf3bafc0fe8ec53504cc7920b6a03814507a
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.LocalBounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalProduct

/-!
# The actual principal Euler correction on the transported half-plane

The local factor and infinite Euler product here are exactly those in the
pinned OpenAI source, not abstract replacements. The coordinate norm bounds,
finite local defect estimate, and normal-product theorem are reused from that
source. We extend the numerical domain to Re(s)>7/8-p/4, for 0<p<1/1000.

The theorem constructs a uniform finite prime cutoff giving an analytic
correction within one half of 1. It does not prove the physical probe's
comparison with the Hecke signal or either probe estimate.
-/

namespace LW56e2.Transport.PhysicalAnalytic

noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss SmoothMobiusCorrection ProbeEuler
open LW56e2.Transport.LocalBounds
local notation "O" => ActualEisensteinCubic.O

/-- Actual local correction bound, with the transported summable exponent. -/
theorem unramifiedClosed_transported_region_bound
    (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 1000)
    (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : Geometry.boundary p ≤ x.re)
    (hw : (19 / 20 : ℝ) ≤ w.re) (hz : (33 / 200 : ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤
      240 * Q ^ goodCap p := by
  dsimp [Geometry.boundary] at hx
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  have hV : ‖V‖ ≤ Q ^ (-(99 / 100 : ℝ)) := by
    rw [show V = coordV Q z from rfl, coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖ ≤ Q ^ (-(56 / 25 : ℝ) + 3 * p / 2) :=
    (coordR_norm_le Q hQ0 A x z hA).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖ ≤ Q ^ (-(19 / 20 : ℝ)) :=
    (coordW_norm_le Q hQ0 v w hv).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖ ≤ Q ^ (-(7 / 8 : ℝ) + p / 4) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖ ≤ Q ^ (-(33 / 40 : ℝ) + p / 4) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖ ≤ 1 / 2 :=
    hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖ ≤ 1 / 2 :=
    hR.trans (rpow_le_half Q _ hQ (by linarith))
  have hDh : ‖D‖ ≤ 1 / 2 :=
    hD.trans (rpow_le_half Q _ hQ (by linarith))
  have hWh : ‖W‖ ≤ 1 :=
    hW.trans ((Real.rpow_le_rpow_of_exponent_le hQ1
      (by norm_num : -(19 / 20 : ℝ) ≤ 0)).trans_eq (Real.rpow_zero Q))
  have hqi : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  let T := Q ^ goodCap p
  have hT : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hRT : ‖R‖ ≤ T := hR.trans
    (Real.rpow_le_rpow_of_exponent_le hQ1 (by dsimp [goodCap]; linarith))
  have hprod (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (haa : a ≤ Q ^ a') (hbb : b ≤ Q ^ b')
      (he : a' + b' ≤ goodCap p) : a * b ≤ T := by
    calc
      a * b ≤ Q ^ a' * Q ^ b' :=
        mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _ = Q ^ (a' + b') := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 he
  have hKV : ‖K‖ * ‖V‖ ≤ T :=
    hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by dsimp [goodCap]; linarith)
  have hDV : ‖D‖ * ‖V‖ ≤ T :=
    hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV (by dsimp [goodCap]; linarith)
  have hDW : ‖D‖ * ‖W‖ ≤ T :=
    hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hW (by dsimp [goodCap]; linarith)
  have hVW : ‖V‖ * ‖W‖ ≤ T :=
    hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW (by dsimp [goodCap]; linarith)
  have hDVW : ‖D‖ * ‖V‖ * ‖W‖ ≤ T :=
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWh).trans hDV
  let P := markedFactor R V (Q : ℂ)⁻¹ K (-D + W * R) 1
  have hE : ‖P + D‖ ≤ 28 * T := by
    have hh := ProbeLocal.unramified_marked_error_bound
      R V (Q : ℂ)⁻¹ K W D hRh hVh hqi hDh
    have hrw : ‖R‖ * (1 + ‖W‖) ≤ 2 * T := by
      calc
        _ ≤ ‖R‖ * 2 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ _ := by nlinarith
    dsimp only [P]
    nlinarith
  have hh := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P - 1‖ ≤ 240 * T
  have hWE : (1 + ‖W‖) * ‖P + D‖ ≤ 56 * T := by
    calc
      _ ≤ 2 * (28 * T) := mul_le_mul (by linarith) hE (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  nlinarith

theorem principalClosed_transported_analytic
    (p : ℝ) (hp : p < 1 / 1000)
    (Q : ℝ) (hQ : 4 ≤ Q) (A eta : ℂ)
    (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) :
    AnalyticOnNhd ℂ (fun s : ℂ => unramifiedClosed Q A eta 1 s 1 (1 / 6))
      {s : ℂ | Geometry.boundary p < s.re} := by
  have hQ0 : 0 < Q := by linarith
  have hv : 1 - coordV Q (1 / 6) ≠ 0 := by
    apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
    rw [coordV_norm Q hQ0]
    apply rpow_le_half Q _ hQ
    norm_num
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro s hs
  change Geometry.boundary p < s.re at hs
  dsimp [Geometry.boundary] at hs
  apply (unramifiedClosed_differentiableAt Q hQ0 A eta 1 s 1 (1 / 6)
    ?_ hv ?_).differentiableWithinAt
  · apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
    apply (coordR_norm_le Q hQ0 A s (1 / 6) hA).trans
    apply rpow_le_half Q _ hQ
    norm_num
    linarith
  · apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
    apply (coordD_norm_le Q hQ0 eta 1 s heta (by simp)).trans
    apply rpow_le_half Q _ hQ
    linarith

def transportPrimeDefectBound (p : ℝ) (P : PrimeIdeal) : ℝ :=
  240 * (Ideal.absNorm P.val : ℝ) ^ goodCap p

theorem transportPrimeDefectBound_nonneg (p : ℝ) (P : PrimeIdeal) :
    0 ≤ transportPrimeDefectBound p P := by
  unfold transportPrimeDefectBound
  positivity

theorem transportPrimeDefectBound_summable (p : ℝ) (hp : p < 1 / 1000) :
    Summable (transportPrimeDefectBound p) := by
  have hexp : (1 : ℝ) < -goodCap p := by
    have hh := good_cap_lt_neg_one hp
    linarith
  have hh := (CubicEisenstein.fullIdealWeight_summable_norm
    ((-goodCap p : ℝ) : ℂ) (by simpa using hexp)).comp_injective
      (Subtype.val_injective : Function.Injective (fun P : PrimeIdeal => P.val))
  apply (hh.mul_left 240).congr
  intro P
  change 240 * ‖CubicEisenstein.fullIdealWeight ((-goodCap p : ℝ) : ℂ) P.val‖ =
    transportPrimeDefectBound p P
  unfold transportPrimeDefectBound CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero, ite_false]
  rw [Complex.norm_natCast_cpow_of_pos
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  simp

theorem principalLocal_transported_bound
    (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 1000)
    (eta : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4 ≤ Ideal.absNorm P.val) (s : ℂ) (hs : Geometry.boundary p < s.re) :
    ‖principalLocal eta P s - 1‖ ≤ transportPrimeDefectBound p P := by
  apply unramifiedClosed_transported_region_bound p hp0 hp
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one eta _
  · exact ProbeRow.targetMonoid_norm_le_one eta _
  · simp
  · exact hs.le
  · norm_num
  · norm_num

theorem principalLocal_transported_analytic
    (p : ℝ) (hp : p < 1 / 1000)
    (eta : HeckeFamily.Character) (P : PrimeIdeal) (hP : 4 ≤ Ideal.absNorm P.val) :
    AnalyticOnNhd ℂ (principalLocal eta P) {s : ℂ | Geometry.boundary p < s.re} := by
  apply principalClosed_transported_analytic p hp
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one eta _
  · exact ProbeRow.targetMonoid_norm_le_one eta _

/-- One finite norm cutoff works for every actual finite-order Hecke character. -/
theorem exists_uniform_transported_principal_cutoff
    (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 1000) :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ (S : Finset (Ideal O)),
      (∀ P : PrimeIdeal, Ideal.absNorm P.val ≤ N → P.val ∈ S) →
      ∀ eta : HeckeFamily.Character,
        AnalyticOnNhd ℂ (principalCorrection eta S)
          {s : ℂ | Geometry.boundary p < s.re} ∧
        ∀ s : ℂ, Geometry.boundary p < s.re →
          ‖principalCorrection eta S s - 1‖ ≤ (1 / 2 : ℝ) := by
  have hsumm := transportPrimeDefectBound_summable p hp
  have ht := (tendsto_order.1
    (tendsto_tsum_compl_atTop_zero (transportPrimeDefectBound p))).2 (1 / 6) (by norm_num)
  obtain ⟨F, hF⟩ := ht.exists
  let N := max 4 (F.sup (fun P => Ideal.absNorm P.val))
  refine ⟨N, le_max_left _ _, ?_⟩
  intro S hS eta
  let T := {P : PrimeIdeal // P.val ∉ S}
  have hnot (P : T) : P.val ∉ F := by
    intro hm
    apply P.property
    apply hS P.val
    exact (Finset.le_sup (f := fun Q : PrimeIdeal => Ideal.absNorm Q.val) hm).trans
      (le_max_right _ _)
  let inc : T → {P : PrimeIdeal // P ∉ F} := fun P => ⟨P.val, hnot P⟩
  have hi : Function.Injective inc := by
    intro P Q hh
    apply Subtype.ext
    exact congrArg (fun t : {P : PrimeIdeal // P ∉ F} => t.val) hh
  have hnorm (P : T) : 4 ≤ Ideal.absNorm P.val.val := by
    have hh : ¬Ideal.absNorm P.val.val ≤ N := fun hh => P.property (hS P.val hh)
    exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hh))
  have hsum : Summable (fun P : T => transportPrimeDefectBound p P.val) :=
    hsumm.subtype _
  have hsmall : (∑' P : T, transportPrimeDefectBound p P.val) ≤ 1 / 6 := by
    apply le_trans ?_ hF.le
    exact Summable.tsum_le_tsum_of_inj inc hi
      (fun P _ => transportPrimeDefectBound_nonneg p P.val) (fun _ => le_rfl)
      hsum (hsumm.subtype _)
  have hhalf (P : T) : transportPrimeDefectBound p P.val ≤ 1 / 2 := by
    have hterm := Summable.le_tsum hsum P
      (fun Q _ => transportPrimeDefectBound_nonneg p Q.val)
    linarith
  constructor
  · exact normalProduct_analytic (fun P : T => principalLocal eta P.val)
      (fun P : T => transportPrimeDefectBound p P.val) _ (Complex.isOpen_re_gt _) hsum
      (fun P => principalLocal_transported_analytic p hp eta P.val (hnorm P))
      (fun P s hs => principalLocal_transported_bound p hp0 hp eta P.val (hnorm P) s hs)
      hhalf
  · intro s hs
    exact product_defect_le (fun P : T => principalLocal eta P.val s)
      (fun P : T => transportPrimeDefectBound p P.val) hsum
      (fun P => principalLocal_transported_bound p hp0 hp eta P.val (hnorm P) s hs)
      hhalf hsmall

theorem exists_transported_principal_correction
    (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 1000)
    (S₀ : Finset (Ideal O)) :
    ∃ S : Finset (Ideal O), S₀ ⊆ S ∧ ∀ eta : HeckeFamily.Character,
      AnalyticOnNhd ℂ (principalCorrection eta S)
        {s : ℂ | Geometry.boundary p < s.re} ∧
      ∀ s : ℂ, Geometry.boundary p < s.re →
        ‖principalCorrection eta S s - 1‖ ≤ (1 / 2 : ℝ) := by
  obtain ⟨N, _, hcut⟩ := exists_uniform_transported_principal_cutoff p hp0 hp
  refine ⟨S₀ ∪ smallPrimeSet N, Finset.subset_union_left, ?_⟩
  apply hcut
  intro P hP
  exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)

end
end LW56e2.Transport.PhysicalAnalytic
