/-
The direct and the reflected bound of one root class, normalized for the root sum.

Both have the form `diag Φ · 2Kn · Λ · Γ · (c₁ c₂)² · ∏ ms · (X + Y)` with `c₁, c₂` the sup controls of the two
plain profiles, `Λ` the divisor factor and `Γ` the constant of the route.
-/
import Submissions.arvi_selected_leaf.R1.Rows

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf.R1
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths CanonicalRowCompletion HeckeFamily HeckeDyadic ConcreteTraceCRT
open QuadraticInitialBound
open CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentSourceMass CenteredMomentOriginalRadialComparison CenteredMomentScaleSupremum
open Qrh.JointDetector Qrh.JointDetector.FineDetectorWords
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

/-- **The direct bound of a root class.** -/
theorem root_bound_direct {ι : Type*} [Fintype ι] (cores : Finset O) (Y δ Kn Xmax Xd : ℝ)
    (hY : 0 ≤ Y) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hnorm : SelectedAllSourceNormBound cores Y δ Kn Xmax)
    (εd : ℝ) (hεd : 0 < εd) (η : Character) (m g : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m)
    (hm2 : (2:O) ∣ m) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (U : ℝ)
    (hΦ : ∀ z : O, 0 ≤ (Φ (‖eisEmbedding z‖^2/U)).re)
    (hcover : ∀ z, keep z → Φ (‖eisEmbedding z‖^2/U) ≠ 0 → ∃ u ∈ cores, z = u * g^6)
    (hnz : ∀ u ∈ cores, u * g^6 ≠ 0)
    (Wl Ws : 𝓢(ℝ,ℂ)) (hsl : Function.support (Wl:ℝ→ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hss : Function.support (Ws:ℝ→ℂ) ⊆ Set.Icc (1/4) (9/4))
    (c₁ c₂ : ℝ) (hc₁ : ∀ x, ‖Wl x‖ ≤ c₁) (hc₂ : ∀ x, ‖Ws x‖ ≤ c₂)
    (pool : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t : ℝ) (B ms : ι → ℝ)
    (hB : ∀ i, (slotPoly η m g (pool i) (β i) t (P i)).NormLe (B i) ∧ 1 ≤ B i)
    (hms : ∀ i, (slotPoly η m g (pool i) (β i) t (P i)).mass ≤ ms i)
    (Xl Xs : ℝ) (hXl : 0 < Xl) (hXs : 0 < Xs)
    (hXd : max 1 (9/4*Xl) * (max 1 (9/4*Xs) * ∏ i, B i) ≤ Xd) (hXdmax : Xd ≤ Xmax)
    (Λ : ℝ) (hΛ : (idealDivisorConstant εd hεd * Xd^εd)^(2 + Fintype.card ι) ≤ Λ) :
    radialEnergy (fun z => polynomial (radRow η m z hm hmLam hm2) false Wl Xl 0 t *
        polynomial (radRow η m z hm hmLam hm2) false Ws Xs 0 t *
        ∏ i, normalizedSlot η m 1 z (pool i) (β i) t (P i)) keep Φ U ≤
      diagonalControl Φ * (2*Kn) * Λ * ((128*(9/4))^2 * c₁^2 * c₂^2 * ∏ i, ms i) * (Xd + Y) := by
  have hsl' : Function.support (Wl:ℝ→ℂ) ⊆ Set.Iic (9/4) := hsl.trans Set.Icc_subset_Iic_self
  have hss' : Function.support (Ws:ℝ→ℂ) ⊆ Set.Iic (9/4) := hss.trans Set.Icc_subset_Iic_self
  have h := direct_class cores Y δ Kn Xmax Xd hY hδ0 hδ1 hnorm εd hεd η m g hm hmLam hm2 keep Φ U hΦ
    hcover hnz Wl Ws Xl Xs t t (9/4) (9/4) c₁ c₂ hXl hXs (by norm_num) (by norm_num) hsl' hss' hc₁ hc₂
    pool β P t B ms hB hms hXd hXdmax
  refine h.trans ?_
  have hdiag := diagonalControl_nonneg Φ
  have hK := hnorm.1
  have hB0 : 0 ≤ ∏ i, B i := Finset.prod_nonneg (fun i _ => zero_le_one.trans (hB i).2)
  have hXd1 : 1 ≤ Xd := by
    refine le_trans ?_ hXd
    have h3 : 1 ≤ ∏ i, B i := by
      have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ => (1:ℝ)) (g := B)
        (fun i _ => zero_le_one) (fun i _ => (hB i).2)
      simpa using this
    have h4 := le_max_left (1:ℝ) (9/4*Xl)
    have h5 := le_max_left (1:ℝ) (9/4*Xs)
    exact one_le_mul_of_one_le_of_one_le h4 (one_le_mul_of_one_le_of_one_le h5 h3)
  have hms0 : 0 ≤ ∏ i, ms i := Finset.prod_nonneg (fun i _ => (OrdPoly.mass_nonneg _).trans (hms i))
  have hpre : 0 ≤ diagonalControl Φ * (2 * Kn * (Xd + Y)) := by
    have : 0 ≤ Xd + Y := by linarith
    positivity
  have hmass0 : 0 ≤ 128 * (9/4:ℝ) * c₁^2 * (128 * (9/4) * c₂^2 * ∏ i, ms i) := by positivity
  calc diagonalControl Φ * (2 * Kn * (Xd + Y)) *
        ((idealDivisorConstant εd hεd * Xd^εd)^(2 + Fintype.card ι) *
          (128 * (9/4) * c₁^2 * (128 * (9/4) * c₂^2 * ∏ i, ms i)))
      ≤ diagonalControl Φ * (2 * Kn * (Xd + Y)) *
        (Λ * (128 * (9/4) * c₁^2 * (128 * (9/4) * c₂^2 * ∏ i, ms i))) := by
        apply mul_le_mul_of_nonneg_left _ hpre
        exact mul_le_mul_of_nonneg_right hΛ hmass0
    _ = _ := by ring

set_option maxHeartbeats 4000000 in
/-- **The reflected bound of a root class.** -/
theorem root_bound_reflected (n : ℕ) (S : Finset (ℕ×ℕ)) (Ce De La epsilon Cscale xi L Z : ℝ)
    (hrefl : ReflectedClassAt n S Ce De La epsilon Cscale xi L Z) (hZ : 1 < Z) (hCe : 0 < Ce)
    (hDe : 0 < De) (hLa : 1 ≤ La)
    (cores : Finset O) (Y δ Kn Xmax Xe : ℝ) (hY : 0 ≤ Y) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hnorm : SelectedAllSourceNormBound cores Y δ Kn Xmax)
    (εd : ℝ) (hεd : 0 < εd) (η : Character) (m g : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m)
    (hm2 : (2:O) ∣ m) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (U : ℝ)
    (hΦ : ∀ z : O, 0 ≤ (Φ (‖eisEmbedding z‖^2/U)).re) (hU : 0 < U)
    (hcover : ∀ z, keep z → Φ (‖eisEmbedding z‖^2/U) ≠ 0 → ∃ u ∈ cores, z = u * g^6)
    (hnz : ∀ u ∈ cores, u * g^6 ≠ 0)
    (Wl Ws : 𝓢(ℝ,ℂ)) (hsl : Function.support (Wl:ℝ→ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hss : Function.support (Ws:ℝ→ℂ) ⊆ Set.Icc (1/4) (9/4))
    (c₁ c₂ Csc : ℝ) (hSl : S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wl ≤ c₁)
    (hsc : ∀ (k : Fin 2) (x : ℝ), ‖scaleTest Ws k x‖ ≤ Csc * c₂)
    {ι : Type} [Fintype ι] (pool : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t : ℝ)
    (B ms : ι → ℝ)
    (hB : ∀ i, (slotPoly η m g (pool i) (β i) t (P i)).NormLe (B i) ∧ 1 ≤ B i)
    (hms : ∀ i, (slotPoly η m g (pool i) (β i) t (P i)).mass ≤ ms i)
    (hres : ∀ z, keep z → (radRow η m z hm hmLam hm2).residue ≠ 1)
    (Xl Xs : ℝ) (hXl : 0 < Xl) (hXs : 0 < Xs) (Mr Rcap : ℝ)
    (hML : Mr ≤ L + Real.logb Z Xl)
    (hmod : ∀ z, keep z → ((radRow η m z hm hmLam hm2).modulus.absNorm : ℝ) ≤ Cscale * Z^Mr)
    (hRcap : 1 ≤ Rcap) (hcap : ∀ z, keep z → ((radRow η m z hm hmLam hm2).modulus.absNorm : ℝ) ≤ Rcap)
    (hXe : max 1 (Z^(max 0 (Mr - Real.logb Z Xl + xi))) * (max 1 (9/4 * Xs) * ∏ i, B i) ≤ Xe)
    (hXemax : Xe ≤ Xmax) (Λ : ℝ)
    (hΛ2 : (idealDivisorConstant εd hεd * Xe^εd)^(2 + Fintype.card ι) ≤ Λ)
    (hΛ1 : (idealDivisorConstant εd hεd * Xe^εd)^(1 + Fintype.card ι) ≤ Λ) (Ξ : ℝ)
    (hΞ : Ce * Rcap^epsilon * (1 + 2*(max 0 (Mr - Real.logb Z Xl + xi) * Real.log Z)) +
      De * Rcap^(2*epsilon) ≤ Ξ) :
    radialEnergy (fun z => polynomial (radRow η m z hm hmLam hm2) false Wl Xl 0 t *
        polynomial (radRow η m z hm hmLam hm2) false Ws Xs 0 t *
        ∏ i, normalizedSlot η m 1 z (pool i) (β i) t (P i)) keep Φ U ≤
      diagonalControl Φ * (2*Kn) * Λ *
        (Ξ * (1+‖t‖)^(2*n) * (128 * La^2 * (128*(9/4)) * Csc^2) * c₁^2 * c₂^2 * ∏ i, ms i) *
        (Xe + Y) := by
  have hZ0 : 0 < Z := by linarith
  have hZne : Z ≠ 1 := ne_of_gt hZ
  have hl : Z^(Real.logb Z Xl) = Xl := Real.rpow_logb hZ0 hZne hXl
  have hs : Z^(Real.logb Z Xs) = Xs := Real.rpow_logb hZ0 hZne hXs
  have hXe' : max 1 (Z^(max 0 (Mr - Real.logb Z Xl + xi))) *
      (max 1 (9/4 * Z^(Real.logb Z Xs)) * ∏ i, B i) ≤ Xe := by rw [hs]; exact hXe
  have h := hrefl cores Y δ Kn Xmax Xe hY hδ0 hδ1 hnorm εd hεd η m g hm hmLam hm2 keep Φ U hΦ hU
    hcover hnz Wl Ws hsl hss (Csc * c₂) hsc ι pool β P t (Real.logb Z Xl) (Real.logb Z Xs) Mr Rcap B ms
    hB hms hres hML hmod hRcap hcap hXe' hXemax
  rw [hl, hs] at h
  refine h.trans ?_
  -- abbreviations
  have hdiag := diagonalControl_nonneg Φ
  have hK := hnorm.1
  have hB0 : 0 ≤ ∏ i, B i := Finset.prod_nonneg (fun i _ => zero_le_one.trans (hB i).2)
  have hXe1 : 1 ≤ Xe := by
    refine le_trans ?_ hXe
    have h3 : 1 ≤ ∏ i, B i := by
      have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ => (1:ℝ)) (g := B)
        (fun i _ => zero_le_one) (fun i _ => (hB i).2)
      simpa using this
    have h4 := le_max_left (1:ℝ) (Z^(max 0 (Mr - Real.logb Z Xl + xi)))
    have h5 := le_max_left (1:ℝ) (9/4*Xs)
    exact one_le_mul_of_one_le_of_one_le h4 (one_le_mul_of_one_le_of_one_le h5 h3)
  have hms0 : 0 ≤ ∏ i, ms i := Finset.prod_nonneg (fun i _ => (OrdPoly.mass_nonneg _).trans (hms i))
  set a := diagonalControl Φ * (2 * Kn * (Xe + Y)) with ha
  have ha0 : 0 ≤ a := by
    have : 0 ≤ Xe + Y := by linarith
    rw [ha]; positivity
  set m₂ := 128 * (9/4) * (Csc * c₂)^2 * ∏ i, ms i with hm₂
  have hm₂0 : 0 ≤ m₂ := by rw [hm₂]; positivity
  set Dp := idealDivisorConstant εd hεd * Xe^εd with hDp
  have hDp0 : 0 ≤ Dp := by
    rw [hDp]
    exact mul_nonneg (idealDivisorConstant_pos εd hεd).le (Real.rpow_nonneg (zero_le_one.trans hXe1) _)
  have hSl0 : 0 ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wl := apply_nonneg _ _
  have hc₁0 : 0 ≤ c₁ := hSl0.trans hSl
  have hsq : (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wl)^2 ≤ c₁^2 := pow_le_pow_left₀ hSl0 hSl 2
  have hT : 0 ≤ (1+‖t‖)^(2*n) := by positivity
  have hRe : 0 ≤ Rcap^epsilon := Real.rpow_nonneg (zero_le_one.trans hRcap) _
  have hRe2 : 0 ≤ Rcap^(2*epsilon) := Real.rpow_nonneg (zero_le_one.trans hRcap) _
  have hlog : 0 ≤ 1 + 2*(max 0 (Mr - Real.logb Z Xl + xi) * Real.log Z) := by
    have := Real.log_pos hZ
    have := le_max_left 0 (Mr - Real.logb Z Xl + xi)
    positivity
  have hZ0' : Z^(-2*(0:ℝ)) = 1 := by simp
  rw [hZ0']
  have hLa2 : 1 ≤ 128 * La^2 := by
    have : 1 ≤ La^2 := one_le_pow₀ hLa
    linarith
  -- first term
  have h1 : Ce * Rcap^epsilon * (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wl)^2 * (1+‖t‖)^(2*n) *
      (1 + 2*(max 0 (Mr - Real.logb Z Xl + xi) * Real.log Z)) *
      (a * (Dp^(2 + Fintype.card ι) * (128 * 1 * La^2 * m₂))) ≤
      (Ce * Rcap^epsilon * (1 + 2*(max 0 (Mr - Real.logb Z Xl + xi) * Real.log Z))) *
        (c₁^2 * (1+‖t‖)^(2*n) * a * Λ * (128 * La^2 * m₂)) := by
    have hD2 : Dp^(2 + Fintype.card ι) * (128 * 1 * La^2 * m₂) ≤ Λ * (128 * La^2 * m₂) := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_right hΛ2 (by positivity)
    have hA : 0 ≤ Ce * Rcap^epsilon * (1 + 2*(max 0 (Mr - Real.logb Z Xl + xi) * Real.log Z)) := by
      positivity
    calc Ce * Rcap^epsilon * (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wl)^2 * (1+‖t‖)^(2*n) *
          (1 + 2*(max 0 (Mr - Real.logb Z Xl + xi) * Real.log Z)) *
          (a * (Dp^(2 + Fintype.card ι) * (128 * 1 * La^2 * m₂)))
        = (Ce * Rcap^epsilon * (1 + 2*(max 0 (Mr - Real.logb Z Xl + xi) * Real.log Z))) *
            ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wl)^2 * (1+‖t‖)^(2*n) * a *
              (Dp^(2 + Fintype.card ι) * (128 * 1 * La^2 * m₂))) := by ring
      _ ≤ (Ce * Rcap^epsilon * (1 + 2*(max 0 (Mr - Real.logb Z Xl + xi) * Real.log Z))) *
            (c₁^2 * (1+‖t‖)^(2*n) * a * (Λ * (128 * La^2 * m₂))) := by
          apply mul_le_mul_of_nonneg_left _ hA
          apply mul_le_mul _ hD2 (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hT) ha0
      _ = _ := by ring
  -- second term
  have h2 : De * Rcap^(2*epsilon) * (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wl)^2 * (1+‖t‖)^(2*n) * 1 *
      (a * (Dp^(1 + Fintype.card ι) * m₂)) ≤
      (De * Rcap^(2*epsilon)) * (c₁^2 * (1+‖t‖)^(2*n) * a * Λ * (128 * La^2 * m₂)) := by
    have hD1 : Dp^(1 + Fintype.card ι) * m₂ ≤ Λ * (128 * La^2 * m₂) := by
      calc Dp^(1 + Fintype.card ι) * m₂ ≤ Λ * m₂ := mul_le_mul_of_nonneg_right hΛ1 hm₂0
        _ ≤ Λ * (128 * La^2 * m₂) := by
            have hm : m₂ ≤ 128 * La^2 * m₂ := by
              calc m₂ = 1 * m₂ := (one_mul m₂).symm
                _ ≤ 128 * La^2 * m₂ := mul_le_mul_of_nonneg_right hLa2 hm₂0
            exact mul_le_mul_of_nonneg_left hm ((pow_nonneg hDp0 _).trans hΛ1)
    have hA : 0 ≤ De * Rcap^(2*epsilon) := by positivity
    calc De * Rcap^(2*epsilon) * (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wl)^2 * (1+‖t‖)^(2*n) * 1 *
          (a * (Dp^(1 + Fintype.card ι) * m₂))
        = (De * Rcap^(2*epsilon)) * ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wl)^2 * (1+‖t‖)^(2*n) * a *
            (Dp^(1 + Fintype.card ι) * m₂)) := by ring
      _ ≤ (De * Rcap^(2*epsilon)) * (c₁^2 * (1+‖t‖)^(2*n) * a * (Λ * (128 * La^2 * m₂))) := by
          apply mul_le_mul_of_nonneg_left _ hA
          apply mul_le_mul _ hD1 (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hT) ha0
      _ = _ := by ring
  have hΛ0 : 0 ≤ Λ := (pow_nonneg hDp0 _).trans hΛ2
  have hrest : 0 ≤ c₁^2 * (1+‖t‖)^(2*n) * a * Λ * (128 * La^2 * m₂) := by positivity
  calc _ ≤ (Ce * Rcap^epsilon * (1 + 2*(max 0 (Mr - Real.logb Z Xl + xi) * Real.log Z))) *
          (c₁^2 * (1+‖t‖)^(2*n) * a * Λ * (128 * La^2 * m₂)) +
        (De * Rcap^(2*epsilon)) * (c₁^2 * (1+‖t‖)^(2*n) * a * Λ * (128 * La^2 * m₂)) := add_le_add h1 h2
    _ = (Ce * Rcap^epsilon * (1 + 2*(max 0 (Mr - Real.logb Z Xl + xi) * Real.log Z)) +
          De * Rcap^(2*epsilon)) * (c₁^2 * (1+‖t‖)^(2*n) * a * Λ * (128 * La^2 * m₂)) := by ring
    _ ≤ Ξ * (c₁^2 * (1+‖t‖)^(2*n) * a * Λ * (128 * La^2 * m₂)) := mul_le_mul_of_nonneg_right hΞ hrest
    _ = _ := by rw [ha, hm₂]; ring

end
end QRH.ArviSelectedLeaf.R1
