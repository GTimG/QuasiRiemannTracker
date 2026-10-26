/- Copyright (c) 2026 Sil. Apache-2.0.
The same actual branch has both reference length caps after extraction.
All profile constants and the annular cutoff remain visible in the bounds.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.ReferenceNaturalLengths
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedLedger

set_option autoImplicit false
namespace Candidate.FourthPower.ReferenceExtractionGeometry
noncomputable section

def branchCap (b A X U : ℝ) : ℝ :=
  if X ≤ Real.sqrt U then b*X else 4*A*(U/X)

theorem branchCap_nonneg (b A X U : ℝ)
    (hb : 0 ≤ b) (hA : 0 ≤ A) (hX : 0 < X) (hU : 0 ≤ U) :
    0 ≤ branchCap b A X U := by unfold branchCap; split_ifs <;> positivity

theorem branchCap_bounds (b A X U : ℝ)
    (hb : 0 ≤ b) (hA : 1 ≤ A) (hX : 0 < X) (hU : 0 ≤ U) :
    branchCap b A X U ≤ (b+4)*A*Real.sqrt U ∧
    branchCap b A X U ≤ (b+4)*A*(U/X) := by
  have hs := Real.sqrt_nonneg U
  have hs2 := Real.sq_sqrt hU
  have hbase : b ≤ (b+4)*A := by nlinarith
  have hfour : 4*A ≤ (b+4)*A := by nlinarith
  have hratio : 0 ≤ U/X := div_nonneg hU hX.le
  unfold branchCap
  split_ifs with hsmall
  · have hh : X ≤ U/X := (le_div_iff₀ hX).mpr (by nlinarith)
    exact ⟨mul_le_mul hbase hsmall hX.le (by positivity),
      mul_le_mul hbase hh hX.le (by positivity)⟩
  · have hh : U/X ≤ Real.sqrt U := (div_le_iff₀ hX).mpr (by nlinarith)
    exact ⟨mul_le_mul hfour hh hratio (by positivity),
      mul_le_mul_of_nonneg_right hfour hratio⟩

/-- The frozen marked product is present in the denominator of the second
cap. It is not discarded when choosing the shorter branch. -/
theorem extracted_bounds (b A X₁ X₂ U V d₁ d₂ f : ℝ)
    (hb : 0 ≤ b) (hA : 1 ≤ A) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hd₁ : 1 ≤ d₁) (hd₂ : 0 < d₂) (hf : 1 ≤ f) :
    let N := (X₁/d₁)*branchCap b A (X₂/d₂) U*(V/f)
    N ≤ (b+4)*A*X₁*V*Real.sqrt U ∧
    N ≤ (b+4)*A*(X₁*V*U/X₂)*(d₂/(d₁*f)) := by
  have hd₁p : 0 < d₁ := zero_lt_one.trans_le hd₁
  have hfp : 0 < f := zero_lt_one.trans_le hf
  have hh := branchCap_bounds b A (X₂/d₂) U hb hA (div_pos hX₂ hd₂) hU
  have hfirst : X₁/d₁ ≤ X₁ := (div_le_iff₀ hd₁p).mpr (by nlinarith)
  have hmarked : V/f ≤ V := (div_le_iff₀ hfp).mpr (by nlinarith)
  dsimp only
  constructor
  · calc
      _ ≤ X₁*((b+4)*A*Real.sqrt U)*V :=
        mul_le_mul (mul_le_mul hfirst hh.1
          (branchCap_nonneg b A _ U hb (zero_le_one.trans hA) (div_pos hX₂ hd₂) hU) hX₁.le)
          hmarked (div_nonneg hV hfp.le) (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ (X₁/d₁)*((b+4)*A*(U/(X₂/d₂)))*(V/f) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hh.2 (div_pos hX₁ hd₁p).le) (div_nonneg hV hfp.le)
      _ = _ := by field_simp

theorem sqrt_power (Z k : ℝ) (hZ : 0 ≤ Z) : Real.sqrt (Z^k) = Z^(k/2) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul hZ]
  congr 1
  ring

/-- Convert the actual two caps to the two exponents accepted by the
unconditional sieve. A fixed geometric constant is paid only once. -/
theorem power_caps (Z C δ a l s k P N T : ℝ)
    (hZ : 1 ≤ Z) (hC : C ≤ Z^δ) (hT : 0 ≤ T)
    (hmax : N ≤ C*Z^a*Z^l*Z^s*Real.sqrt (Z^k))
    (href : N ≤ C*Z^a*(Z^l*Z^s*Z^k/Z^(P-l))*T) :
    N ≤ Z^(l+k/2+s+a+δ) ∧ N ≤ Z^(k+2*l-P+s+a+δ)*T := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  constructor
  · apply hmax.trans
    calc
      _ ≤ Z^δ*Z^a*Z^l*Z^s*Real.sqrt (Z^k) := by gcongr
      _ = _ := by
        rw [sqrt_power Z k hZp.le]
        simp_rw [← Real.rpow_add hZp]
        congr 1
        ring
  · apply href.trans
    calc
      _ ≤ Z^δ*Z^a*(Z^l*Z^s*Z^k/Z^(P-l))*T := by gcongr
      _ = _ := by
        rw [← Real.rpow_add hZp l s,← Real.rpow_add hZp (l+s) k,
          ← Real.rpow_sub hZp,← Real.rpow_add hZp δ a,← Real.rpow_add hZp]
        congr 2
        ring

/-- Strict reference gates provide one positive allowance shared by the
annular cutoff, the conductor constant and every fixed geometric constant. -/
theorem margin (R l k P s : ℝ)
    (hmax : l+k/2+s < (4/5)*R) (href : k+2*l-P+s < R/2) :
    ∃ δ : ℝ, 0 < δ ∧
      l+k/2+s+2*δ ≤ (4/5)*R ∧ k+2*l-P+s+2*δ ≤ R/2 := by
  let δ := min ((4/5)*R-(l+k/2+s)) (R/2-(k+2*l-P+s))/4
  have hδ : 0 < δ := div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  have hm := min_le_left ((4/5)*R-(l+k/2+s)) (R/2-(k+2*l-P+s))
  have hr := min_le_right ((4/5)*R-(l+k/2+s)) (R/2-(k+2*l-P+s))
  refine ⟨δ,hδ,?_,?_⟩ <;> dsimp [δ] at * <;> linarith

theorem mixed_margin (R P s d l : ℝ) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hcap : P+2*s+4*d < R) (hcenter : (5/6)*R-(7/3)*d < P+s)
    (hl : MixedLedger.lower R P s d < l) (hu : l < MixedLedger.upper R P s d) :
    ∃ δ : ℝ, 0 < δ ∧
      l+(R+d)/2+s+2*δ ≤ (4/5)*R ∧ R+d+2*l-P+s+2*δ ≤ R/2 := by
  have h := MixedLedger.reference_gate hs hd hcap hcenter hl hu
  exact margin R l (R+d) P s h.2.2.2 h.2.2.1

/-- On the reflected branch, a conductor bound by Z^K automatically gives
the polynomial lower-length condition required by the true tail theorem. -/
theorem reflected_tail_cap (U X M Z K : ℝ) (hU : 1 ≤ U) (hZ : 0 ≤ Z)
    (hX : Real.sqrt U < X) (hM : M ≤ Z^K) : M ≤ Z^K*X := by
  have hs : 1 ≤ Real.sqrt U := by
    simpa using Real.sqrt_le_sqrt hU
  have hXp : 1 ≤ X := hs.trans hX.le
  exact hM.trans (le_mul_of_one_le_right (Real.rpow_nonneg hZ _) hXp)

theorem mixed_exponents_nonneg (R P s d l : ℝ)
    (hR : 0 ≤ R) (hs : 0 ≤ s) (hd : 0 ≤ d) (hl : 0 ≤ l)
    (hcap : P+2*s+4*d < R) :
    0 ≤ l+(R+d)/2+s ∧ 0 ≤ R+d+2*l-P+s := by constructor <;> linarith

/-- Rounding the whole convolution length to one is harmless when both
reference exponents are nonnegative. This does not round the retained-factor
length: an empty retained factor is handled by ReferenceEmptyEnergy. -/
theorem whole_length_caps (Z v y N T : ℝ) (hZ : 1 ≤ Z) (hv : 0 ≤ v) (hy : 0 ≤ y)
    (hmax : N ≤ Z^v) (href : N ≤ Z^y*T) :
    max 1 N ≤ Z^v ∧ max 1 N ≤ Z^y*max 1 T := by
  have hv1 : 1 ≤ Z^v := Real.one_le_rpow hZ hv
  have hy1 : 1 ≤ Z^y := Real.one_le_rpow hZ hy
  refine ⟨max_le hv1 hmax,max_le ?_ ?_⟩
  · exact one_le_mul_of_one_le_of_one_le hy1 (le_max_left _ _)
  · exact href.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (zero_le_one.trans hy1))

theorem rounded_critical_cost (T : ℝ) (hT : 0 ≤ T) :
    3+(max 1 T)^(1/3 : ℝ) ≤ (4/3)*(3+T^(1/3 : ℝ)) := by
  have ht := Real.rpow_nonneg hT (1/3 : ℝ)
  by_cases h : T ≤ 1
  · rw [max_eq_left h,Real.one_rpow]
    nlinarith
  · rw [max_eq_right (le_of_not_ge h)]
    nlinarith

theorem fixed_constant_cap (C δ Z : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ)
    (_hZ : 0 ≤ Z) (hthreshold : C^(1/δ) ≤ Z) : C ≤ Z^δ := by
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hC _) hthreshold hδ.le
  rw [← Real.rpow_mul hC] at h
  simpa only [one_div,mul_inv_cancel₀ hδ.ne',inv_mul_cancel₀ hδ.ne',Real.rpow_one] using h

/-- Logarithmic scale-box losses use only an arbitrary small power, with a
constant independent of the extraction choices and physical rows. -/
theorem log_box_bound (Z Y C k δ : ℝ)
    (hZ : 1 ≤ Z) (hY : 1 ≤ Y) (hC : 1 ≤ C) (hk : 0 ≤ k) (hδ : 0 < δ)
    (hcap : Y ≤ C*Z^k) :
    1+2*Real.log Y ≤ (1+2*Real.log C+2*k/δ)*Z^δ := by
  have hZp := zero_lt_one.trans_le hZ
  have hCp := zero_lt_one.trans_le hC
  have hp : 1 ≤ Z^δ := Real.one_le_rpow hZ hδ.le
  have hl : Real.log Z ≤ Z^δ/δ := by
    apply (le_div_iff₀ hδ).mpr
    have hh := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hZp δ)
    rw [Real.log_rpow hZp] at hh
    linarith
  have hy : Real.log Y ≤ Real.log C+k*Real.log Z := by
    have hh := Real.log_le_log (zero_lt_one.trans_le hY) hcap
    rwa [Real.log_mul hCp.ne' (Real.rpow_pos_of_pos hZp k).ne',Real.log_rpow hZp] at hh
  have hc0 : 0 ≤ 1+2*Real.log C := by linarith [Real.log_nonneg hC]
  calc
    _ ≤ (1+2*Real.log C)+2*k*(Z^δ/δ) := by nlinarith [mul_le_mul_of_nonneg_left hl hk]
    _ ≤ (1+2*Real.log C)*Z^δ+2*k*(Z^δ/δ) :=
      add_le_add (le_mul_of_one_le_right hc0 hp) le_rfl
    _ = _ := by ring

theorem log_box_absorbed (Z Y C k R ε : ℝ)
    (hZ : 1 ≤ Z) (hY : 1 ≤ Y) (hC : 1 ≤ C) (hk : 0 ≤ k) (hε : 0 < ε)
    (hcap : Y ≤ C*Z^k) :
    (1+2*Real.log Y)*Z^(R+ε/2) ≤
      (1+2*Real.log C+2*k/(ε/2))*Z^(R+ε) := by
  have hZp := zero_lt_one.trans_le hZ
  calc
    _ ≤ ((1+2*Real.log C+2*k/(ε/2))*Z^(ε/2))*Z^(R+ε/2) :=
      mul_le_mul_of_nonneg_right (log_box_bound Z Y C k (ε/2) hZ hY hC hk (half_pos hε) hcap)
        (Real.rpow_nonneg hZp.le _)
    _ = _ := by
      rw [mul_assoc,← Real.rpow_add hZp]
      congr 2
      ring

end
end Candidate.FourthPower.ReferenceExtractionGeometry
