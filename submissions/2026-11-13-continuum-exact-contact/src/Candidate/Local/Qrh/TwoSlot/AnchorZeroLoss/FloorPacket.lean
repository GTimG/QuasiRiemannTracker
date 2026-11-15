/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Empty-selection specialization of Hailey Collet's physical numerator packet
theorem. The actual coefficient packet and natural character zeros are retained.
This module assumes neither Geometry.BoundsN nor its old floor_margin. -/
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.ActualBin
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.RowCount

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical ContDiff

namespace Qrh.TwoSlot.AnchorZeroLoss

open Cycle25.Numerator Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical
open HeckeInverseAmplification
local notation "O" => HeckeFamily.O

/-- The packet's trivial count is available for every actual finite row set
inside the row ball, with the baseline constant and natural row definition. -/
theorem floor_row_count (R : Finset FreeRow) (U : ℝ) (hU : 1 ≤ U)
    (hR : ∀ u ∈ R, ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ≤ U) :
    (Fintype.card R : ℝ) ≤ 128 * U := by
  simpa only [Fintype.card_coe] using freeRow_count R U hU hR

/-- Dividing by a deterministic positive cap gives a bounded multiplier;
no row-dependent physical amplitude is inverted. -/
theorem normalized_main_bound {κ : Type*} (P : κ → ℂ) {B : ℝ}
    (hB : 0 < B) (hP : ∀ i, ‖P i‖ ≤ B) (i : κ) :
    ‖P i / (B : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
  exact (div_le_one hB).mpr (hP i)

/-- The cap is restored exactly outside the positive packet norm. This
identity retains every zero and every coefficient of the physical product. -/
theorem restore_main_cap {κ : Type*} [Fintype κ] (A P : κ → ℂ)
    {B : ℝ} (hB : 0 < B) :
    (∑ i, ‖A i * P i‖) = B * ∑ i, ‖A i * (P i / (B : ℂ))‖ := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have he : A i * P i = (B : ℂ) * (A i * (P i / (B : ℂ))) := by
    field_simp
  calc
    ‖A i * P i‖ = ‖(B : ℂ) * (A i * (P i / (B : ℂ)))‖ := congrArg norm he
    _ = B * ‖A i * (P i / (B : ℂ))‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]

/-- The inclusive floor packet, with trivial row count and empty selected
product. Its only analytic input is the unmarked physical fourth moment on
the displayed active dilation boxes. The bounded multiplier is arbitrary,
so it can be the physical main-prime product divided by its deterministic cap. -/
theorem floor_packet_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (massEps cp bp Bp : ℝ) (hmass : 0 < massEps)
    (hcp : 0 < cp) (hbp : 0 < bp) (hBp : 0 ≤ Bp) :
    ∃ Cmass : ℝ, 0 < Cmass ∧ ∀
      (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character)
      (T : ι → Finset ProbePhysical.PrimeIdeal) (hT : ∀ i P, P ∈ T i → P.val ∉ S)
      (hdis : ∀ P : ∀ i, T i, Function.Injective (fun i => (P i).val))
      (hη : ∀ i P, P ∈ T i → IsCoprime P.val η.modulus)
      (Pbase : ∀ i, T i) (W : ι → ℝ → ℂ) (Yp : ι → ℝ),
      (∀ i, 1 ≤ Yp i) → (∀ i, Function.support (W i) ⊆ Set.Icc cp bp) →
      (∀ i y, ‖W i y‖ ≤ Bp) → ∀ (x z : ℂ) (eps : ℝ),
      0 < eps → eps ≤ 1 / 1000 →
      x.re = 51 / 100 + 16 * eps → z.re = 17 / 50 →
      ∀ (κ : Type) [Fintype κ] (u : κ → FreeRow)
      (W1 : ℝ → ℂ) (a b Y : ℝ), 0 < a → Function.support W1 ⊆ Set.Icc a b →
      ContDiff ℝ ∞ W1 → 0 < Y →
      ∀ (U xi : ℝ) (n : ℕ) (Cu : κ → ℝ) (Ccond : ℝ)
      (P : κ → ℂ) (momentEps Cmoment : ℝ),
      1 ≤ U → 0 ≤ xi → 1 ≤ Cmoment →
      1 + firsteps ≤ x.re + 49 / 100 → 0 < Ccond →
      (∀ i, 0 ≤ Cu i) →
      (∀ i, Cu i ≤ Ccond * ((Ideal.span {(u i).val} : Ideal O).radical.absNorm : ℝ)) →
      (∀ i, ((Ideal.span {(u i).val} : Ideal O).absNorm : ℝ) ≤ U) →
      (∀ i, (rowCharacter S hS.prime (u i)).residue ≠ 1) →
      b * Y ≤ U ^ ((n : ℝ) * xi) →
      (Fintype.card κ : ℝ) ≤ 128 * U → (∀ i, ‖P i‖ ≤ 1) →
      let Lc (i : κ) := Cu i / (Ccond * ((Ideal.span {(u i).val} : Ideal O).absNorm : ℝ))
      (∀ j ∈ Finset.range (n + 1), ∀ e : ∀ i, LabelPacketIndex S (u i) T,
        (∑ i, ‖if (labelPacketScale S (u i) T (e i) : ℝ) ≤ b * Y ∧
          dilationBox U xi n (max 1 (Lc i * (labelPacketScale S (u i) T (e i) : ℝ))) = j
          then HeckeDyadic.polynomial (rowCharacter S hS.prime (u i)) false W1
            (Y / (labelPacketScale S (u i) T (e i) : ℝ)) 0 0 else 0‖ ^ 4)
          ≤ Cmoment * U ^ (1 + momentEps)) →
      (∑ i, ‖labelPolynomialPacket S hS η (u i) T hT W Yp x z W1 Y * P i‖) ≤
        Y ^ (-(1 / 2 : ℝ)) * ((n + 1 : ℕ) : ℝ) *
          (Cmass * U ^ massEps * ∏ i, (Yp i) ^ (-(4 / 25 : ℝ))) *
          128 * Cmoment * U ^ (1 + momentEps / 4 + xi / 100) := by
  obtain ⟨Cmass, hCmass, hb⟩ := Cycle25.Numerator.actual_label_packet_bin_bound
    (ι := ι) (7 / 10) massEps cp bp Bp (by norm_num) hmass hcp hbp hBp
  refine ⟨Cmass, hCmass, ?_⟩
  intro S hS firsteps hfirst η T hT hdis hη Pbase W Yp hYp hWS hWB
    x z eps heps heps1 hx hz κ _ u W1 a b Y ha hsupp hW1 hY
    U xi n Cu Ccond P momentEps Cmoment hU hxi hm hmargin hCcond
    hCu0 hCu hNu hrow hcut hcard hP Lc hfourth
  have hfourth' : ∀ j ∈ Finset.range (n + 1), ∀ e : ∀ i, LabelPacketIndex S (u i) T,
      (∑ i, ‖if (labelPacketScale S (u i) T (e i) : ℝ) ≤ b * Y ∧
        dilationBox U xi n (max 1 (Lc i * (labelPacketScale S (u i) T (e i) : ℝ))) = j
        then HeckeDyadic.polynomial (rowCharacter S hS.prime (u i)) false W1
          (Y / (labelPacketScale S (u i) T (e i) : ℝ)) 0 0 else 0‖ ^ 4 * ‖(1 : ℂ)‖ ^ 2)
        ≤ Cmoment * U ^ (1 + momentEps) := by
    simpa only [norm_one, one_pow, mul_one] using hfourth
  have h := hb S hS firsteps hfirst η T hT hdis hη Pbase W Yp hYp hWS hWB
    x z (51 / 100) eps (by norm_num) (by norm_num) heps heps1 hx hz
    κ u W1 a b Y ha hsupp hW1 hY U xi n Cu Ccond (fun _ _ => 1) P
    1 0 0 0 (1 / 25) 0 momentEps 128 Cmoment
    hU hxi (by norm_num) hm (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by linarith) (by norm_num)
    (by convert hmargin using 1 <;> norm_num) hCcond hCu0 hCu hNu hrow hcut
    (by simpa only [Real.rpow_one] using hcard)
    (by intro j hj i; simp) (by simpa using hP) hfourth'
  have hexp : (0 : ℝ) * 0 - 0 * 0 / 2 + (3 * 1 + 1 + momentEps) / 4 +
      0 / 2 + (1 / 25) * xi / 4 = 1 + momentEps / 4 + xi / 100 := by ring
  simpa only [hexp] using h

end Qrh.TwoSlot.AnchorZeroLoss

#print axioms Qrh.TwoSlot.AnchorZeroLoss.floor_packet_bound
