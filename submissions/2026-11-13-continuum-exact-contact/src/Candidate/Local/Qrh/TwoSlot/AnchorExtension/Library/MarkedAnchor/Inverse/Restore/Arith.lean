/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Restore.Datum

/-!
# Inverse.Restore.Arith — scale and constant bookkeeping of the restoration

* `g1_scale` (the frozen tuple pays the frozen widths → the separated scale
  `Xc 2^{|I|} ≤ 2^{K+1} ∏_I H · Q`),
* `xmax_le`, `slot_width_le` (the rectangle hypotheses of `RestoreChildAt` as products),
* `mainConst_le` (the main-column constant in final form).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators SchwartzMap
open MeasureTheory

/-- **Frozen scale**: the frozen tuple pays the frozen widths. -/
theorem g1_scale {σ : Type*} [DecidableEq σ] (S Js : Finset σ) (hJs : Js ⊆ S) (H : σ → ℝ)
    (hH : ∀ i ∈ S, 0 < H i) (K : ℕ) (hK : S.card ≤ K) (Xc Xmax Q : ℝ) (hXc : 0 < Xc)
    (hQ : 0 ≤ Q) (hfro : Xc * ∏ i ∈ Js, (H i / 2) ≤ 2 * Xmax)
    (hXmax : Xmax ≤ (∏ i ∈ S, H i) * Q) :
    Xc * 2^(S \ Js).card ≤ 2^(K+1) * (∏ i ∈ S \ Js, H i) * Q := by
  set A := ∏ i ∈ S \ Js, H i with hA
  set B := ∏ i ∈ Js, H i with hB
  have hA0 : 0 < A := Finset.prod_pos (fun i hi => hH i (Finset.mem_sdiff.mp hi).1)
  have hB0 : 0 < B := Finset.prod_pos (fun i hi => hH i (hJs hi))
  have hprod : A * B = ∏ i ∈ S, H i := Finset.prod_sdiff hJs
  have hB2 : ∏ i ∈ Js, (H i / 2) = B / 2^Js.card := by
    rw [Finset.prod_div_distrib, Finset.prod_const]
  rw [hB2, mul_div_assoc', div_le_iff₀ (by positivity)] at hfro
  have hcard : (S \ Js).card + Js.card = S.card := Finset.card_sdiff_add_card_eq_card hJs
  have h1 : Xc * B ≤ 2 * 2^Js.card * (A * B * Q) := by
    calc Xc * B ≤ 2 * Xmax * 2^Js.card := hfro
      _ ≤ 2 * ((∏ i ∈ S, H i) * Q) * 2^Js.card := by gcongr
      _ = 2 * 2^Js.card * (A * B * Q) := by rw [← hprod]; ring
  have h2 : Xc ≤ 2 * 2^Js.card * (A * Q) := by
    have : Xc * B ≤ (2 * 2^Js.card * (A * Q)) * B := by nlinarith
    exact le_of_mul_le_mul_right this hB0
  calc Xc * 2^(S \ Js).card ≤ 2 * 2^Js.card * (A * Q) * 2^(S \ Js).card := by gcongr
    _ = 2^((S \ Js).card + Js.card + 1) * A * Q := by rw [pow_add, pow_add]; ring
    _ ≤ 2^(K+1) * A * Q := by
        gcongr
        · norm_num
        · omega

/-- The free-width hypothesis as a product bound. -/
theorem xmax_le (Z Xmax P E : ℝ) (hZ : 1 < Z) (hX : 0 < Xmax) (hP : 0 < P)
    (h : Real.logb Z Xmax - Real.logb Z P ≤ E) : Xmax ≤ P * Z^E := by
  rw [← Real.logb_div hX.ne' hP.ne', Real.logb_le_iff_le_rpow hZ (div_pos hX hP),
    div_le_iff₀ hP] at h
  linarith

/-- The slot-width hypothesis bounds the total slot width. -/
theorem slot_width_le {σ : Type*} (S : Finset σ) (ell H : σ → ℝ) (Z E : ℝ) (hZ : 1 < Z)
    (hH : ∀ i ∈ S, Z^(ell i) ≤ H i) (h : Real.logb Z (∏ i ∈ S, H i) ≤ E) :
    ∑ i ∈ S, ell i ≤ E := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hprod : Z^(∑ i ∈ S, ell i) ≤ ∏ i ∈ S, H i := by
    rw [Real.rpow_sum_of_pos hZ0]
    exact Finset.prod_le_prod₀ (fun i _ => (Real.rpow_pos_of_pos hZ0 _).le) hH
  have hpos : 0 < Z^(∑ i ∈ S, ell i) := Real.rpow_pos_of_pos hZ0 _
  have := Real.logb_le_logb_of_le hZ hpos hprod
  rw [Real.logb_rpow hZ0 hZ.ne'] at this
  linarith

/-- **The main-column constant in final form.** -/
theorem mainConst_le (b : 𝓢(ℝ, ℂ)) (d K : ℕ) (c₀ Cb C Z Hc' x ε hv s Ib : ℝ) (hC : 0 ≤ C)
    (hZ : 1 ≤ Z) (hHc : 0 ≤ Hc') (hHc2 : Hc' ≤ 2) (hε : 0 ≤ ε) (hv0 : 0 ≤ hv)
    (hIb : ∫ τ, ‖b τ‖ * (1 + ‖τ‖)^d ≤ Ib) :
    mainConst b d K c₀ Cb C (Z^Hc') (x + ε/4) ((1 + 2 * Real.pi) * hv) s ≤
      ((Ib^2 + 1) * (QRH.Record1252270103Source.Collision.collisionProjectionCost 1 256 K *
        ((smallConst c₀ K * max 1 Cb)^2 * (C * 64^(2*d))))) *
        (1 + hv)^(2*d) * Z^(Hc' * (1 + x) + ε/2) * (1 + ‖s‖)^(2*d) := by
  unfold mainConst
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hcost : 0 ≤ QRH.Record1252270103Source.Collision.collisionProjectionCost 1 256 K := by
    unfold QRH.Record1252270103Source.Collision.collisionProjectionCost; positivity
  have hI0 : 0 ≤ ∫ τ, ‖b τ‖ * (1 + ‖τ‖)^d :=
    integral_nonneg (fun τ => by positivity)
  have hI2 : (∫ τ, ‖b τ‖ * (1 + ‖τ‖)^d)^2 ≤ Ib^2 + 1 := by
    have := pow_le_pow_left₀ hI0 hIb 2
    linarith
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hbase : 8 * (1 + (1 + 2 * Real.pi) * hv) * (1 + ‖s‖) ≤ 64 * (1 + hv) * (1 + ‖s‖) := by
    have hs := norm_nonneg s
    have : 8 * (1 + (1 + 2 * Real.pi) * hv) ≤ 64 * (1 + hv) := by nlinarith
    nlinarith
  have hpow : ((8 * (1 + (1 + 2 * Real.pi) * hv) * (1 + ‖s‖))^d)^2 ≤
      64^(2*d) * (1 + hv)^(2*d) * (1 + ‖s‖)^(2*d) := by
    rw [← pow_mul, mul_comm d 2]
    calc (8 * (1 + (1 + 2 * Real.pi) * hv) * (1 + ‖s‖))^(2*d)
        ≤ (64 * (1 + hv) * (1 + ‖s‖))^(2*d) := pow_le_pow_left₀ (by positivity) hbase _
      _ = 64^(2*d) * (1 + hv)^(2*d) * (1 + ‖s‖)^(2*d) := by rw [mul_pow, mul_pow]
  have hZpow : (Z^Hc')^((1:ℝ) + (x + ε/4)) ≤ Z^(Hc' * (1 + x) + ε/2) := by
    rw [← Real.rpow_mul hZ0.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    nlinarith
  have hZp0 : 0 ≤ (Z^Hc')^((1:ℝ) + (x + ε/4)) := Real.rpow_nonneg (Real.rpow_nonneg hZ0.le _) _
  have hS0 : 0 ≤ (smallConst c₀ K * max 1 Cb)^2 := sq_nonneg _
  calc (∫ τ, ‖b τ‖ * (1 + ‖τ‖)^d)^2 *
        (QRH.Record1252270103Source.Collision.collisionProjectionCost 1 256 K *
          ((smallConst c₀ K * max 1 Cb)^2 * (C * (Z^Hc')^((1:ℝ) + (x + ε/4)) *
            ((8 * (1 + (1 + 2 * Real.pi) * hv) * (1 + ‖s‖))^d)^2)))
      ≤ (Ib^2 + 1) * (QRH.Record1252270103Source.Collision.collisionProjectionCost 1 256 K *
          ((smallConst c₀ K * max 1 Cb)^2 * (C * Z^(Hc' * (1 + x) + ε/2) *
            (64^(2*d) * (1 + hv)^(2*d) * (1 + ‖s‖)^(2*d))))) := by
        gcongr
    _ = _ := by ring

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.g1_scale
#print axioms Qrh.MarkedAnchor.Inverse.Restore.mainConst_le
