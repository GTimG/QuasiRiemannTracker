/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Inverse.Row
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Inverse.Contract
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Inverse.Inputs
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.LeafClass
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.LeafBudget
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.CofactorW
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Cofactor.Tiny
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeGlobal
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.IncumbentInput

/-!
# High.Inverse.LeafAux — scale-level inputs of the inverse HIGH leaf

* `PrincipalSpikeHyp` — verbatim the statement of `Principal.PrincipalInverseSpike`: the inverse
  dyadic spike of a PRINCIPAL character.
* `RowInputsAt`, `CoreBatchAt` — the scale-level bodies of `inverse_row_inputs` and
  `High.core_class_batch` (so that the leaf can pass them around as hypotheses).
* `whole_row_spike` — every row of the ball (principal row member included, via the spike
  hypothesis) has `‖M_θ(w)‖² ≤ Cw Z^(3/4 r + 2ε₁)` at small heights (`|θ| < Z^A`).
* `gate_eventually`, `gate_bound` — the height gates `(3+(3j+2)Z^τ)^4 ≤ Z^((2/25)ηw)` for all
  height indices `j ≤ ⌈7|θ|+hv⌉ + Ne` when `|θ| + hv < Z^A`, `τ ≤ A`, `8A < (2/25)ηw`.
* `large_height_bound` — the large-height case (`Z^A ≤ ‖θ‖ + hv`) is paid by the height degree.
* `slotHighT_lt` — the LOW slot supplier on a finite slot set.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High.Inverse
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDyadic
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal
local instance leafAuxQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- **The principal inverse spike** (verbatim `Principal.PrincipalInverseSpike`). -/
def PrincipalSpikeHyp : Prop :=
  ∀ (Φ : ℝ → ℂ) (ao bo : ℝ), 0 < ao → Function.support Φ ⊆ Set.Icc ao bo → ContDiff ℝ ∞ Φ →
  ∀ (R d A ε : ℝ), 0 ≤ R → 0 < d → 0 ≤ A → 0 < ε →
  ∃ C : ℝ, 0 < C ∧ ∀ (Z : ℝ), 1 ≤ Z → ∀ (χ : Character), χ.residue = 1 →
    (χ.modulus.absNorm : ℝ) ≤ Z^d → ∀ (r om : ℝ), 0 ≤ r → r ≤ R → |om| ≤ Z^A →
    ‖polynomial χ true Φ ((Z^d)^r) 0 om‖^2 ≤
      C * (Z^d)^((2*HeckeZeroSupremum.beta-1)*r + ε)

/-- The scale-level body of `inverse_row_inputs`. -/
def RowInputsAt (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
    (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (W : ℝ → ℂ) (Φ : ℝ → ℂ) (data : RowData)
    (τ εpw ε₁ e ηw Cr Cs : ℝ) (tw : RayQuotient.Characters rayM G.twist) (Z : ℝ) : Prop :=
  ∀ (c : FreeRow) (B : NZIdeal)
    (hnc : ∀ j, (coreFamily rayM G.pool (hHpool G hH) (dataBase data)
      (twistEta rayM G hH data tw) c j).residue ≠ 1),
    ((Ideal.span {(ProbePhysical.sixthFrequencyEquiv (c, B)).val}).absNorm : ℝ) ≤ Z →
  ∀ (a : ℝ) (j : ℕ), 51/100 ≤ a → a ≤ 1 →
    HeckeDetectorZeros.zeroMaximum (coreFamily rayM G.pool (hHpool G hH) (dataBase data)
      (twistEta rayM G hH data tw) c) hnc (3*(j+1 : ℕ)*Z^τ) < a + 2*e →
    (3+(3*j+2 : ℕ)*Z^τ)^4 ≤ (Z^(2:ℝ))^ηw →
    (∀ (r θ : ℝ), 0 ≤ r → r ≤ 1 → |2*Real.pi*θ| + Z^τ/2 ≤ (3*j+2 : ℕ)*Z^τ →
      ‖polynomial (data.character ⟨(ProbePhysical.sixthFrequencyEquiv (c, B)).val,
        (ProbePhysical.sixthFrequencyEquiv (c, B)).property⟩) true
        (InverseMoment.childLogTest Φ θ) (Z^r) 0 0‖^2 ≤ Cr * Z^((2*a-1)*r + 2*εpw)) ∧
    (∀ (ell v : ℝ), 0 ≤ ell → ell ≤ 1 → |v| + Z^τ/2 ≤ (3*j+2 : ℕ)*Z^τ →
      ‖naturalSlot (naturalRow (dataBase data) (ProbePhysical.sixthFrequencyEquiv (c, B)).val
          (ProbePhysical.sixthFrequencyEquiv (c, B)).property).character
        (primePool rayM G.pool 2 (Z^ell))
        (fun I => idealCoeff (relativeCharacter rayM G.pool (hHpool G hH)
            (twistEta rayM G hH data tw) 1) I *
          HeckePrimeAnnular.annularWeight W (Z^ell) (33/50) v I) (Z^ell)‖^2 ≤
        Cs^2 * Z^((2*a-1)*ell + 4*ε₁))

/-- `inverse_row_inputs` with its scale-level body named. -/
theorem inverse_row_inputs_at (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
    (hH : RayOrthogonality.globalUnits rayM ≤ G.twist)
    (W : ℝ → ℂ) (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (Φ : ℝ → ℂ) (ao bo : ℝ) (hao : 0 < ao) (hΦs : Function.support Φ ⊆ Icc ao bo)
    (hΦ : ContDiff ℝ ∞ Φ) (data : RowData)
    (τ εpw ε₁ e ηw : ℝ) (hτ : 0 < τ) (hεpw : 0 < εpw) (hε₁ : 0 < ε₁) (he : 0 < e)
    (he' : e < 1/1000) (hηw : 0 ≤ ηw) (hbpw : 12*e*(1+2) + 8*e + 2*ηw ≤ εpw)
    (hbsl : 8*e*(1/2) + e ≤ ε₁) :
    ∃ Cr : ℝ, 0 < Cr ∧ ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ tw : RayQuotient.Characters rayM G.twist,
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ 2 < Z^τ ∧
      RowInputsAt rayM G hH W Φ data τ εpw ε₁ e ηw Cr Cs tw Z :=
  inverse_row_inputs rayM G hH W hWs hW Φ ao bo hao hΦs hΦ data τ εpw ε₁ e ηw hτ hεpw hε₁ he he'
    hηw hbpw hbsl

/-- The scale-level body of `High.core_class_batch`. -/
def CoreBatchAt (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (W : ℝ → ℂ) (η η₀ : Character)
    (α : Type) [Fintype α] [DecidableEq α] (a0 a1 wlo εm meshm wmin dmin dmax : ℝ) (J : ℕ)
    (τ ε ηw bw ηd margin Broot d ε₁ v e Kc Cc Z : ℝ) : Prop :=
  ∀ (dB : ℝ), dmin ≤ dB + margin → dB + margin ≤ dmax →
    ∀ (B : NZIdeal) (F : Finset FreeRow) (T big : Finset α)
      (θ : α → RayQuotient.Characters rayM H) (w σ vv : α → ℝ)
      (t height mesh a k P ε' K1 Csm : ℝ) (i : ℕ)
      (rowsq : FreeRow → ℝ) (ns : FreeRow → α → ℝ),
    (B.val.absNorm : ℝ) ≤ Z^Broot →
    (∀ u ∈ F, ProbeHighRowFamily.rowNorm u ≤ Z^dB) →
    (∀ u ∈ F, RegularCore rayM H hH η η₀ u) →
    big ⊆ T → (∀ x ∈ big, wmin ≤ w x) → (∀ x ∈ big, w x ≤ 1) → 0 ≤ mesh →
    (∀ x ∈ big, w x ≤ mesh) → mesh/(dB+margin) ≤ meshm →
    (∀ x ∈ big, σ x = 33/50) → (∀ x ∈ big, |vv x| ≤ height) → 0 ≤ height → |t| ≤ height →
    (∀ x ∈ big, |t + vv x| + Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
    (3+(3*i+2 : ℕ)*Z^τ)^4 ≤ (Z^(dB+margin))^ηw →
    (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^v →
    51/100 < a → a ≤ 1 → 2*a-1 ≤ 3/4 → 0 ≤ k → k ≤ 2*a-1 → wlo ≤ cutHi → 0 ≤ a1 →
    a1 ≤ 1/2 → 0 < ε' → 0 ≤ K1 → 1 ≤ Csm →
    (∀ u ∈ F, ∀ hn : (∀ j, (coreFamily rayM H hH η η₀ u j).residue ≠ 1),
      HeckeDetectorZeros.zeroMaximum (coreFamily rayM H hH η η₀ u) hn (3*(i+1 : ℕ)*Z^τ) <
        a+2*e ∧
      a ≤ HeckeDetectorZeros.zeroMaximum (coreFamily rayM H hH η η₀ u) hn ((3*i : ℕ)*Z^τ)) →
    (∀ u ∈ F, ∀ x ∈ T, 0 ≤ ns u x) →
    (∀ u ∈ F, rowsq u ≤ K1 * Z^((2*a-1)*P) * ∏ x ∈ T, ns u x) →
    (∀ u ∈ F, ∀ x ∈ T, x ∉ big → ns u x ≤ Csm) →
    (∀ u ∈ F, ∀ x ∈ big, ns u x = ‖naturalSlot
      (excluded (naturalRow η (ProbePhysical.sixthFrequencyEquiv (u, B)).val
        (ProbePhysical.sixthFrequencyEquiv (u, B)).property).character 1)
      (primePool rayM H 2 (Z^(w x)))
      (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ x)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w x)) (σ x) (t + vv x) I) (Z^(w x))‖^2) →
    ∑ u ∈ F, rowsq u ≤ K1 * Csm^(T \ big).card * 4^big.card *
      (((Cc * Z^(ε₁*d))^2)^big.card *
        (Kc * (1 + (2*Real.pi*((Z^(dB+margin))^(τ/(2*dmax))) + ((3*i : ℕ) : ℝ)*Z^τ +
          (|t| + height)))^(J+1)) *
        (Z^(dB+margin))^(1 + max 0 (detPriceW a0 a1 k wlo (P/(dB+margin))
            (∑ x ∈ big, w x / (dB+margin)) 1) + ε' +
          (154*ε + (2*a-1)*(mesh/(dB+margin)) + εm + 2*bw*(∑ x ∈ big, w x / (dB+margin))) +
          ηd))

/-- `High.core_class_batch` with its scale-level body named. -/
theorem core_class_batch_at (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) {a0 a1 wlo : ℝ}
    (hM : HighMarkedCoreInputsH a0 a1 wlo) (εm : ℝ) (hεm : 0 < εm) :
    ∃ meshm : ℝ, 0 < meshm ∧
    ∀ (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
      (hH : RayOrthogonality.globalUnits rayM ≤ H)
      (W : ℝ → ℂ), Function.support W ⊆ Set.Icc (1:ℝ) 2 → ContDiff ℝ ∞ W →
      ∀ (η η₀ : Character) {α : Type} [Fintype α] [DecidableEq α] (wmin dmin dmax : ℝ),
      0 < wmin → 0 < dmin → dmin ≤ dmax →
      ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (τ ε e ηw bw ηd margin Broot d ε₁ kap v : ℝ), 0 < τ → 0 < ε → ε ≤ 1/1000000 →
        0 < e → e < 1/1000 → 0 ≤ ηw → ηw ≤ 2 → 12*e*((22:ℝ)+2)+8*e+2*ηw ≤ ε/2 → 0 < bw →
        0 < ηd → 0 < margin → 0 ≤ Broot → dmax ≤ d → 0 < ε₁ → 0 < kap → 0 ≤ v →
        8*e*(1/d)+kap ≤ ε₁ →
      ∃ Kc : ℝ, 0 ≤ Kc ∧ ∃ Cc : ℝ, 1 ≤ Cc ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ 2 < Z^τ ∧
        CoreBatchAt rayM H hH W η η₀ α a0 a1 wlo εm meshm wmin dmin dmax J τ ε ηw bw ηd margin
          Broot d ε₁ v e Kc Cc Z := by
  obtain ⟨meshm, hmeshm, h⟩ := core_class_batch hβ hM εm hεm
  exact ⟨meshm, hmeshm, h⟩

/-- **Whole-row spike**: the inverse factor of every row of the ball at a small height. -/
theorem whole_row_spike (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) (hP : PrincipalSpikeHyp)
    (Φ : ℝ → ℂ) (ao bo : ℝ) (hao : 0 < ao) (hΦs : Function.support Φ ⊆ Icc ao bo)
    (hΦ : ContDiff ℝ ∞ Φ) (data : RowData)
    (τ ε₁ e ηw A : ℝ) (hτ : 0 < τ) (hε₁ : 0 < ε₁) (he : 0 < e) (he' : e < 1/1000)
    (hηw : 0 ≤ ηw) (hA : 0 ≤ A) (hbud : 12*e*(1+2) + 8*e + 2*ηw ≤ ε₁) :
    ∃ Cw : ℝ, 0 < Cw ∧ ∀ᶠ Z : ℝ in atTop, ∀ (w : NonzeroElement),
      ((Ideal.span {w.val}).absNorm : ℝ) ≤ Z → ∀ (r θ : ℝ) (j : ℕ), 0 ≤ r → r ≤ 1 →
      |θ| < Z^A → |2*Real.pi*θ| + Z^τ/2 ≤ (3*j+2 : ℕ)*Z^τ →
      (3+(3*j+2 : ℕ)*Z^τ)^4 ≤ (Z^(2:ℝ))^ηw →
      ‖polynomial (data.character w) true (InverseMoment.childLogTest Φ θ) (Z^r) 0 0‖^2 ≤
        Cw * Z^(3/4*r + 2*ε₁) := by
  obtain ⟨Cn, hCn, hpw⟩ := inverse_row_pointwise Φ ao bo hao hΦs hΦ 1 2 τ ε₁ e e ηw
    zero_le_one (by norm_num) hτ hε₁ he he' he (by linarith) hηw (by linarith)
  obtain ⟨Cp, hCp, hsp⟩ := hP Φ ao bo hao hΦs hΦ 1 2 (A+1) ε₁ zero_le_one (by norm_num)
    (by linarith) hε₁
  set K0 : ℝ := ((dataBase data).modulus.absNorm : ℝ) * (fixedConductorFactor : ℝ) + 1
    with hK0
  have hbβ : HeckeZeroSupremum.beta ≤ 7/8 := Candidate.FourthPower.IncumbentInput.baseline_beta
  refine ⟨max Cn Cp, lt_max_of_lt_left hCn, ?_⟩
  filter_upwards [eventually_ge_atTop K0, eventually_ge_atTop (7:ℝ),
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop 2)] with Z hZK hZ7 hZτ
  intro w hw r θ j hr0 hr1 hθ hfreq hgate
  have hZ1 : 1 < Z := by linarith
  have hZ0 : 0 < Z := by linarith
  have hZ2 : Z^(2:ℝ) = Z * Z := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
  set χw := (naturalRow (dataBase data) w.val w.property).character with hχw
  have hmod : (χw.modulus.absNorm : ℝ) ≤ Z^(2:ℝ) := by
    have h1 : (χw.modulus.absNorm : ℝ) ≤ ((dataBase data).modulus.absNorm : ℝ) *
        (fixedConductorFactor : ℝ) * ((Ideal.span {w.val}).absNorm : ℝ) := by
      exact_mod_cast (naturalRow (dataBase data) w.val w.property).natural_modulus_bound
    have hK : ((dataBase data).modulus.absNorm : ℝ) * (fixedConductorFactor : ℝ) ≤ Z := by
      linarith
    have hN0 : (0:ℝ) ≤ ((Ideal.span {w.val}).absNorm : ℝ) := Nat.cast_nonneg _
    rw [hZ2]
    exact h1.trans (mul_le_mul hK hw hN0 hZ0.le)
  have hCmax : Cn ≤ max Cn Cp := le_max_left _ _
  have hCmax' : Cp ≤ max Cn Cp := le_max_right _ _
  rw [polynomial_data_natural]
  by_cases hpr : χw.residue = 1
  · have hD : 0 < Z^r := Real.rpow_pos_of_pos hZ0 _
    rw [polynomial_childLogTest _ _ _ _ _ hD]
    have hom : |2*Real.pi*θ| ≤ Z^(A+1) := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi), Real.rpow_add hZ0,
        Real.rpow_one]
      have hpi : 2*Real.pi ≤ 7 := by linarith [Real.pi_lt_d2]
      have hZA : 0 ≤ Z^A := Real.rpow_nonneg hZ0.le _
      nlinarith [abs_nonneg θ]
    have hb := hsp Z hZ1.le χw hpr hmod (r/2) (2*Real.pi*θ) (by linarith) (by linarith) hom
    rw [scale_rescale hZ0 (by norm_num : (0:ℝ) < 2)] at hb
    refine hb.trans ?_
    rw [← Real.rpow_mul hZ0.le]
    have hexp : (2:ℝ) * ((2*HeckeZeroSupremum.beta-1)*(r/2) + ε₁) ≤ 3/4*r + 2*ε₁ := by
      nlinarith
    calc Cp * Z^((2:ℝ) * ((2*HeckeZeroSupremum.beta-1)*(r/2) + ε₁))
        ≤ Cp * Z^(3/4*r + 2*ε₁) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ1.le hexp) hCp.le
      _ ≤ max Cn Cp * Z^(3/4*r + 2*ε₁) :=
          mul_le_mul_of_nonneg_right hCmax' (Real.rpow_nonneg hZ0.le _)
  · have hn : ∀ _u : Unit, ((fun _ : Unit => χw) _u).residue ≠ 1 := fun _ => hpr
    have hmax : HeckeDetectorZeros.zeroMaximum (fun _ : Unit => χw) hn (3*(j+1 : ℕ)*Z^τ) <
        7/8 + 2*e := by
      have := CenteredMomentPrimeGlobal.zeroMaximum_le_beta (fun _ : Unit => χw) hn
        (3*(j+1 : ℕ)*Z^τ) hβ
      linarith
    have hb := hpw Z 2 hZ1.le (by norm_num) le_rfl hZτ (fun _ : Unit => χw) hn (7/8) j
      (by norm_num) (by norm_num) hmax () (r/2) θ hmod (by linarith) (by linarith) hfreq hgate
    rw [scale_rescale hZ0 (by norm_num : (0:ℝ) < 2)] at hb
    refine hb.trans ?_
    rw [← Real.rpow_mul hZ0.le]
    have hexp : (2:ℝ) * ((2*(7/8:ℝ)-1)*(r/2) + ε₁) = 3/4*r + 2*ε₁ := by ring
    rw [hexp]
    exact mul_le_mul_of_nonneg_right hCmax (Real.rpow_nonneg hZ0.le _)

/-- The height gate, eventually in `Z`. -/
theorem gate_eventually (Ne : ℕ) (A ηw : ℝ) (h : 8*A < (2/25)*ηw) :
    ∀ᶠ Z : ℝ in atTop, (3*(Ne:ℝ)+29)^4 * Z^(8*A) ≤ Z^((2/25)*ηw) := by
  have hpos : 0 < (2/25)*ηw - 8*A := by linarith
  filter_upwards [(tendsto_rpow_atTop hpos).eventually
    (eventually_ge_atTop ((3*(Ne:ℝ)+29)^4)), eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  calc (3*(Ne:ℝ)+29)^4 * Z^(8*A) ≤ Z^((2/25)*ηw - 8*A) * Z^(8*A) :=
        mul_le_mul_of_nonneg_right hZ (Real.rpow_nonneg hZ0.le _)
    _ = Z^((2/25)*ηw) := by rw [← Real.rpow_add hZ0]; congr 1; ring

/-- **The height gate** of every height index `j ≤ ⌈7|θ|+hv⌉ + Ne` at a small height. -/
theorem gate_bound {Z τ A ηw θ hv : ℝ} {j Ne : ℕ} (hZ : 1 ≤ Z) (hτ : 0 ≤ τ) (hτA : τ ≤ A)
    (hv0 : 0 ≤ hv) (hθ : |θ| + hv < Z^A)
    (hj : j ≤ ⌈7*|θ| + hv⌉₊ + Ne)
    (hg : (3*(Ne:ℝ)+29)^4 * Z^(8*A) ≤ Z^((2/25)*ηw)) :
    (3+((3*j+2 : ℕ) : ℝ)*Z^τ)^4 ≤ Z^((2/25)*ηw) := by
  have hA : 0 ≤ A := hτ.trans hτA
  have hZ0 : 0 < Z := by linarith
  have hy1 : 1 ≤ Z^A := Real.one_le_rpow hZ hA
  have hx1 : 1 ≤ Z^τ := Real.one_le_rpow hZ hτ
  have hxy : Z^τ ≤ Z^A := Real.rpow_le_rpow_of_exponent_le hZ hτA
  have hc : ((⌈7*|θ| + hv⌉₊ : ℕ) : ℝ) < 7*|θ| + hv + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hjr : (j:ℝ) ≤ ((⌈7*|θ|+hv⌉₊ : ℕ) : ℝ) + Ne := by exact_mod_cast hj
  have hθy : 7*|θ| + hv ≤ 7*Z^A := by have := abs_nonneg θ; linarith
  have hN : (0:ℝ) ≤ Ne := Nat.cast_nonneg _
  have hjy : (j:ℝ) ≤ 7*Z^A + 1 + Ne := by linarith
  have hbase : 3+((3*j+2 : ℕ) : ℝ)*Z^τ ≤ (3*(Ne:ℝ)+29) * (Z^A)^2 := by
    push_cast
    have h1 : (3*(j:ℝ)+2)*Z^τ ≤ (3*(7*Z^A+1+Ne)+2)*Z^A :=
      mul_le_mul (by linarith) hxy (by linarith) (by positivity)
    have h2 : Z^A ≤ (Z^A)^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hN]
  have hy8 : ((Z^A)^2)^4 = Z^(8*A) := by
    rw [← pow_mul, show 8*A = A*((2*4 : ℕ) : ℝ) by push_cast; ring, Real.rpow_mul hZ0.le,
      Real.rpow_natCast]
  calc (3+((3*j+2 : ℕ) : ℝ)*Z^τ)^4 ≤ ((3*(Ne:ℝ)+29) * (Z^A)^2)^4 :=
        pow_le_pow_left₀ (by positivity) hbase 4
    _ = (3*(Ne:ℝ)+29)^4 * Z^(8*A) := by rw [mul_pow, hy8]
    _ ≤ _ := hg

/-- **Large heights**: paid by the height degree. -/
theorem large_height_bound {Z A θ hv S P ε C0 : ℝ} {deg : ℕ} (hZ : 1 ≤ Z)
    (hθ : Z^A ≤ ‖θ‖ + hv) (hv0 : 0 ≤ hv) (hdeg : 1 + S ≤ A*deg) (hP : 0 ≤ P) (hε : 0 ≤ ε)
    (hC0 : 0 ≤ C0) :
    C0 * Z^(2 + S) ≤ C0 * Z^(1 + P + ε) * ((1+‖θ‖+hv)^deg)^2 := by
  have hZ0 : 0 < Z := by linarith
  have hx1 : 1 ≤ 1+‖θ‖+hv := by have := norm_nonneg θ; linarith
  have h1 : Z^(1+S) ≤ (1+‖θ‖+hv)^deg := by
    calc Z^(1+S) ≤ Z^(A*deg) := Real.rpow_le_rpow_of_exponent_le hZ hdeg
      _ = (Z^A)^deg := by rw [Real.rpow_mul hZ0.le, Real.rpow_natCast]
      _ ≤ (1+‖θ‖+hv)^deg := pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) (by linarith) _
  have h2 : (1+‖θ‖+hv)^deg ≤ ((1+‖θ‖+hv)^deg)^2 := by
    have h1x : 1 ≤ (1+‖θ‖+hv)^deg := one_le_pow₀ hx1
    nlinarith
  have h3 : Z^(2+S) ≤ Z^(1+P+ε) * Z^(1+S) := by
    rw [← Real.rpow_add hZ0]; exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h4 : 0 ≤ Z^(1+P+ε) := Real.rpow_nonneg hZ0.le _
  calc C0 * Z^(2+S) ≤ C0 * (Z^(1+P+ε) * Z^(1+S)) := mul_le_mul_of_nonneg_left h3 hC0
    _ ≤ C0 * (Z^(1+P+ε) * ((1+‖θ‖+hv)^deg)^2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h1.trans h2) h4) hC0
    _ = _ := by ring

/-- **LOW slot supplier on a finite slot set**: a slot above the threshold under the envelope
of the upper guard `a + h` forces `k < 2(a+h)-1`. -/
theorem slotHighT_lt {α : Type*} {T : Finset α} {ns ell : α → ℝ} {c lam k Z A lam' a h : ℝ}
    (hZ : 1 < Z) (hA : 0 < A) (hcA : A ≤ c) (hlam : lam' < lam)
    (hell : ∀ x ∈ T, 0 ≤ ell x)
    (henv : ∀ x ∈ T, ns x ≤ A * Z^((2*(a+h)-1)*ell x + lam'))
    (hhigh : ∃ x ∈ T, c * Z^(k * ell x + lam) < ns x) : k < 2*(a+h)-1 := by
  obtain ⟨x, hx, hi⟩ := hhigh
  have h1 : c * Z^(k * ell x + lam) < A * Z^((2*(a+h)-1)*ell x + lam') :=
    hi.trans_le (henv x hx)
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have h2 : A * Z^(k * ell x + lam) ≤ c * Z^(k * ell x + lam) :=
    mul_le_mul_of_nonneg_right hcA (Real.rpow_nonneg hZ0.le _)
  have h3 : Z^(k * ell x + lam) < Z^((2*(a+h)-1)*ell x + lam') :=
    lt_of_mul_lt_mul_left (h2.trans_lt h1) hA.le
  have h4 : k * ell x + lam < (2*(a+h)-1)*ell x + lam' :=
    (Real.rpow_lt_rpow_left_iff hZ).mp h3
  by_contra hk
  push Not at hk
  have := mul_le_mul_of_nonneg_right hk (hell x hx)
  linarith

end
end Qrh.MarkedAnchor.High.Inverse

#print axioms Qrh.MarkedAnchor.High.Inverse.whole_row_spike
#print axioms Qrh.MarkedAnchor.High.Inverse.gate_bound
