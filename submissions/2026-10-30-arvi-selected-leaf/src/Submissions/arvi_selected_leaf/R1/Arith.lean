/-
The exponent arithmetic of R1.

With `P = ℓ₁ + ℓ₂` (`ℓ₂ ≤ ℓ₁`), slot weight `s` and row width `M`, every term of the root sum is at most
`Z^{M + selExcess P s M + 2u}`:
* the sixth-power term and the small-root term: exponent at most `M`;
* the root count times the short length: `ℓ₂ + s + M/6 ≤ M + selExcess` (`exp_count`);
* the interpolated direct/reflected term: `P + s + θ(M − 2ℓ₁ + u)` with `θ = (1+η)/5` (`exp_interp`).
-/
import Submissions.arvi_selected_leaf.R1.Peel

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf.R1
noncomputable section
open QRH.ArviSelectedLeaf

theorem selExcess_ge (P s M : ℝ) :
    P + s + max 0 ((M - P)/5) ≤ M + selExcess P s M := by
  unfold selExcess
  have := le_max_right 0 (P + s + max 0 ((M - P)/5) - M)
  linarith

theorem selExcess_nonneg' (P s M : ℝ) : 0 ≤ selExcess P s M := by
  unfold selExcess; exact le_max_left _ _

/-- The root count term. -/
theorem exp_count (M ℓ₁ ℓ₂ s : ℝ) (hℓ₂ : 0 ≤ ℓ₂) (hℓ : ℓ₂ ≤ ℓ₁) (hM : 0 ≤ M) :
    ℓ₂ + s + M/6 ≤ M + selExcess (ℓ₁ + ℓ₂) s M := by
  have h1 := selExcess_ge (ℓ₁ + ℓ₂) s M
  have h2 : (M - (ℓ₁ + ℓ₂))/5 ≤ max 0 ((M - (ℓ₁ + ℓ₂))/5) := le_max_right _ _
  have h3 : 0 ≤ max 0 ((M - (ℓ₁ + ℓ₂))/5) := le_max_left _ _
  -- M/6 ≤ ℓ₁ + max 0 ((M - P)/5)
  have h4 : M/6 ≤ ℓ₁ + max 0 ((M - (ℓ₁ + ℓ₂))/5) := by
    rcases le_total ℓ₁ (M/6) with h | h
    · linarith
    · linarith
  linarith

/-- The interpolated term. -/
theorem exp_interp (M Mcap ℓ₁ ℓ₂ s u : ℝ) (hℓ₂ : 0 ≤ ℓ₂) (hℓ : ℓ₂ ≤ ℓ₁) (hM : 0 ≤ M)
    (hMc : M ≤ Mcap) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    (ℓ₁ + ℓ₂ + s) + (1 + u/(Mcap+1))/5 * (M - 2*ℓ₁ + u) ≤ M + selExcess (ℓ₁ + ℓ₂) s M + 2*u := by
  have hMc1 : 0 < Mcap + 1 := by linarith
  set η := u/(Mcap+1) with hη
  have hη0 : 0 ≤ η := div_nonneg hu hMc1.le
  have hηM : η * M ≤ u := by
    rw [hη, div_mul_eq_mul_div, div_le_iff₀ hMc1]
    nlinarith
  have hη1 : η ≤ u := by
    rw [hη, div_le_iff₀ hMc1]
    nlinarith
  have h1 := selExcess_ge (ℓ₁ + ℓ₂) s M
  have h2 : (M - (ℓ₁ + ℓ₂))/5 ≤ max 0 ((M - (ℓ₁ + ℓ₂))/5) := le_max_right _ _
  have h3 : 0 ≤ max 0 ((M - (ℓ₁ + ℓ₂))/5) := le_max_left _ _
  have hθ1 : (1 + η)/5 ≤ 1 := by linarith
  have hθu : (1 + η)/5 * u ≤ u := by
    calc (1 + η)/5 * u ≤ 1 * u := mul_le_mul_of_nonneg_right hθ1 hu
      _ = u := one_mul u
  rcases le_total (2*ℓ₁) M with h | h
  · -- M ≥ 2ℓ₁
    have h5 : (1 + η)/5 * (M - 2*ℓ₁) ≤ (M - (ℓ₁ + ℓ₂))/5 + η * M / 5 := by
      have : η * (M - 2*ℓ₁) ≤ η * M := mul_le_mul_of_nonneg_left (by linarith) hη0
      nlinarith
    nlinarith
  · -- M < 2ℓ₁
    have h5 : (1 + η)/5 * (M - 2*ℓ₁) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    nlinarith

/-- **The root-sum bracket** is at most `Z^{M + selExcess + 2u}` up to a constant. -/
theorem bracket_bound (Z M Mmin Mcap ℓ₁ ℓ₂ s u bΦ cR ζ C₆ : ℝ) (hZ : 1 < Z) (hMmin : 0 < Mmin)
    (hMM : Mmin ≤ M) (hMc : M ≤ Mcap) (hℓ₂ : 0 ≤ ℓ₂) (hℓ : ℓ₂ ≤ ℓ₁) (hs : 0 ≤ s) (hu : 0 < u)
    (hu1 : u ≤ 1) (hbΦ : 1 ≤ bΦ) (hcR : 0 ≤ cR) (hζ : 0 ≤ ζ) (hC₆ : 0 ≤ C₆) :
    (Z^(Mmin/20) + cR * Z^(ℓ₂ + s)) * (ζ * (bΦ * Z^M)^((1 + u/(Mcap+1))/6)) + C₆ * (bΦ * Z^M) +
      ζ * ((9/4 * cR * Z^(ℓ₁ + ℓ₂ + s))^(1 - (1 + u/(Mcap+1))/5) *
        (cR * Z^(ℓ₂ + s) * Z^(M - ℓ₁ + u))^((1 + u/(Mcap+1))/5)) ≤
    (ζ * bΦ * (1 + cR) + C₆ * bΦ + ζ * (9/4) * cR) * Z^(M + selExcess (ℓ₁ + ℓ₂) s M + 2*u) := by
  have hZ0 : 0 < Z := by linarith
  have hM : 0 ≤ M := hMmin.le.trans hMM
  have hMc1 : 0 < Mcap + 1 := by linarith
  set η := u/(Mcap+1) with hη
  have hη0 : 0 ≤ η := div_nonneg hu.le hMc1.le
  have hηM : η * M ≤ u := by
    rw [hη, div_mul_eq_mul_div, div_le_iff₀ hMc1]
    nlinarith
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_iff₀ hMc1]
    nlinarith
  set E := M + selExcess (ℓ₁ + ℓ₂) s M + 2*u with hE
  have hsel0 := selExcess_nonneg' (ℓ₁ + ℓ₂) s M
  have hZE : 0 ≤ Z^E := Real.rpow_nonneg hZ0.le _
  set e6 := (1 + η)/6 with he6
  set θ := (1 + η)/5 with hθ
  have he60 : 0 ≤ e6 := by rw [he6]; positivity
  have he61 : e6 ≤ 1 := by rw [he6]; linarith
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  -- the sixth-power factor
  have hB : (bΦ * Z^M)^e6 ≤ bΦ * Z^(M*e6) := by
    rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg hZ0.le _), ← Real.rpow_mul hZ0.le]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ0.le _)
    calc bΦ^e6 ≤ bΦ^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hbΦ he61
      _ = bΦ := Real.rpow_one bΦ
  have hBnn : 0 ≤ (bΦ * Z^M)^e6 := Real.rpow_nonneg (by positivity) _
  have hMe6 : M * e6 ≤ M/6 + u := by
    rw [he6]
    nlinarith
  -- exponents
  have hE1 : Mmin/20 + M*e6 ≤ E := by rw [hE]; nlinarith
  have hE2 : ℓ₂ + s + M*e6 ≤ E := by
    have := exp_count M ℓ₁ ℓ₂ s hℓ₂ hℓ hM
    rw [hE]; linarith
  have hE3 : (ℓ₁ + ℓ₂ + s)*(1 - θ) + ((ℓ₂ + s) + (M - ℓ₁ + u))*θ ≤ E := by
    have := exp_interp M Mcap ℓ₁ ℓ₂ s u hℓ₂ hℓ hM hMc hu.le hu1
    have heq : (ℓ₁ + ℓ₂ + s)*(1 - θ) + ((ℓ₂ + s) + (M - ℓ₁ + u))*θ =
        (ℓ₁ + ℓ₂ + s) + (1 + u/(Mcap+1))/5 * (M - 2*ℓ₁ + u) := by rw [hθ, hη]; ring
    rw [heq, hE]; linarith
  have hE4 : M ≤ E := by rw [hE]; linarith
  -- term 1
  have t1a : Z^(Mmin/20) * (ζ * (bΦ * Z^M)^e6) ≤ ζ * bΦ * Z^E := by
    calc Z^(Mmin/20) * (ζ * (bΦ * Z^M)^e6) ≤ Z^(Mmin/20) * (ζ * (bΦ * Z^(M*e6))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hζ) (Real.rpow_nonneg hZ0.le _)
      _ = ζ * bΦ * Z^(Mmin/20 + M*e6) := by rw [Real.rpow_add hZ0 (Mmin/20) (M*e6)]; ring
      _ ≤ ζ * bΦ * Z^E := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hZ.le hE1) (by positivity)
  have t1b : cR * Z^(ℓ₂ + s) * (ζ * (bΦ * Z^M)^e6) ≤ ζ * bΦ * cR * Z^E := by
    calc cR * Z^(ℓ₂ + s) * (ζ * (bΦ * Z^M)^e6) ≤ cR * Z^(ℓ₂ + s) * (ζ * (bΦ * Z^(M*e6))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hζ)
            (mul_nonneg hcR (Real.rpow_nonneg hZ0.le _))
      _ = ζ * bΦ * cR * Z^(ℓ₂ + s + M*e6) := by rw [Real.rpow_add hZ0 (ℓ₂ + s) (M*e6)]; ring
      _ ≤ ζ * bΦ * cR * Z^E := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hZ.le hE2) (by positivity)
  have t2 : C₆ * (bΦ * Z^M) ≤ C₆ * bΦ * Z^E := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le hE4) (by positivity)
  -- term 3
  have t3 : ζ * ((9/4 * cR * Z^(ℓ₁ + ℓ₂ + s))^(1 - θ) * (cR * Z^(ℓ₂ + s) * Z^(M - ℓ₁ + u))^θ) ≤
      ζ * (9/4) * cR * Z^E := by
    have h1θ : 0 ≤ 1 - θ := by linarith
    have hc : cR^(1 - θ) * cR^θ = cR := by
      rw [← Real.rpow_add' hcR (by norm_num : (1 - θ) + θ ≠ 0)]
      simp
    have h94 : (9/4:ℝ)^(1 - θ) ≤ 9/4 := by
      calc (9/4:ℝ)^(1 - θ) ≤ (9/4:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 9/4 := Real.rpow_one _
    have hA : (9/4 * cR * Z^(ℓ₁ + ℓ₂ + s))^(1 - θ) =
        (9/4:ℝ)^(1 - θ) * cR^(1 - θ) * Z^((ℓ₁ + ℓ₂ + s)*(1 - θ)) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hZ0.le _), Real.mul_rpow (by norm_num) hcR,
        ← Real.rpow_mul hZ0.le]
    have hB' : (cR * Z^(ℓ₂ + s) * Z^(M - ℓ₁ + u))^θ =
        cR^θ * Z^(((ℓ₂ + s) + (M - ℓ₁ + u))*θ) := by
      rw [mul_assoc, ← Real.rpow_add hZ0, Real.mul_rpow hcR (Real.rpow_nonneg hZ0.le _),
        ← Real.rpow_mul hZ0.le]
    have hexpand : (9/4 * cR * Z^(ℓ₁ + ℓ₂ + s))^(1 - θ) * (cR * Z^(ℓ₂ + s) * Z^(M - ℓ₁ + u))^θ =
        (9/4:ℝ)^(1 - θ) * (cR^(1 - θ) * cR^θ) *
          Z^((ℓ₁ + ℓ₂ + s)*(1 - θ) + ((ℓ₂ + s) + (M - ℓ₁ + u))*θ) := by
      rw [hA, hB', Real.rpow_add hZ0 ((ℓ₁ + ℓ₂ + s)*(1 - θ))]
      ring
    rw [hexpand, hc]
    calc ζ * ((9/4:ℝ)^(1 - θ) * cR * Z^((ℓ₁ + ℓ₂ + s)*(1 - θ) + ((ℓ₂ + s) + (M - ℓ₁ + u))*θ))
        ≤ ζ * ((9/4) * cR * Z^E) := by
          apply mul_le_mul_of_nonneg_left _ hζ
          apply mul_le_mul (mul_le_mul_of_nonneg_right h94 hcR)
            (Real.rpow_le_rpow_of_exponent_le hZ.le hE3) (Real.rpow_nonneg hZ0.le _) (by positivity)
      _ = ζ * (9/4) * cR * Z^E := by ring
  calc (Z^(Mmin/20) + cR * Z^(ℓ₂ + s)) * (ζ * (bΦ * Z^M)^e6) + C₆ * (bΦ * Z^M) +
        ζ * ((9/4 * cR * Z^(ℓ₁ + ℓ₂ + s))^(1 - θ) * (cR * Z^(ℓ₂ + s) * Z^(M - ℓ₁ + u))^θ)
      = Z^(Mmin/20) * (ζ * (bΦ * Z^M)^e6) + cR * Z^(ℓ₂ + s) * (ζ * (bΦ * Z^M)^e6) +
        C₆ * (bΦ * Z^M) +
        ζ * ((9/4 * cR * Z^(ℓ₁ + ℓ₂ + s))^(1 - θ) * (cR * Z^(ℓ₂ + s) * Z^(M - ℓ₁ + u))^θ) := by ring
    _ ≤ ζ * bΦ * Z^E + ζ * bΦ * cR * Z^E + C₆ * bΦ * Z^E + ζ * (9/4) * cR * Z^E := by
        linarith [t1a, t1b, t2, t3]
    _ = (ζ * bΦ * (1 + cR) + C₆ * bΦ + ζ * (9/4) * cR) * Z^E := by ring

end
end QRH.ArviSelectedLeaf.R1
