/- Modified by Joseph Bebel (2026-11-12): smaller-tolerance inverse
HIGH leaf; original coefficient, mask and principal-row proofs are retained. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.Trivial
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.Bin

/-!
# High.Inverse.Row — the pointwise inputs of one inverse HIGH row

For the raw row `w = c·B⁶` (`c` a core of the data base `dataBase data`, twist `twistEta tw`) in the
ball `N(w) ≤ Z`, under the CORE-family upper guard `zeroMaximum (coreFamily …) (3(j+1)Z^τ) < a+2e`:

* the inverse factor: `‖M_v(w)‖² ≤ Cr Z^((2a-1) r + 2 εpw)` (`inverse_row_pointwise` on the raw
  family `rawFam`, scale `Z²`, through `rawFam_maximum_eq_core`, `polynomial_data_natural`);
* every raw natural slot (pool `primePool rayM G.pool 2 (Z^ell)`, coefficient
  `relChar(twistEta tw, 1)·annular`, height `v`): `‖slot‖² ≤ Cs² Z^((2a-1) ell + 4 ε₁)`
  (`core_slot_bound` for the raw row, conductors from `raw_conductor_bound`).

Constants before `Z`; `Z` eventually in terms of the data and the twist only.
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High.Inverse
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDyadic
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal
local instance rowQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- **Pointwise inputs of an inverse HIGH row.** -/
theorem inverse_row_inputs (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
    (hH : RayOrthogonality.globalUnits rayM ≤ G.twist)
    (W : ℝ → ℂ) (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (Φ : ℝ → ℂ) (ao bo : ℝ) (hao : 0 < ao) (hΦs : Function.support Φ ⊆ Icc ao bo)
    (hΦ : ContDiff ℝ ∞ Φ) (data : RowData)
    (τ εpw ε₁ e ηw : ℝ) (hτ : 0 < τ) (hεpw : 0 < εpw) (hε₁ : 0 < ε₁) (he : 0 < e)
    (he' : e < 1/1000) (hηw : 0 ≤ ηw) (hbpw : 12*e*(1+2) + 8*e + 2*ηw ≤ εpw)
    (hbsl : 8*e*(1/2) + e ≤ ε₁) :
    ∃ Cr : ℝ, 0 < Cr ∧ ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ tw : RayQuotient.Characters rayM G.twist,
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ 2 < Z^τ ∧
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
          Cs^2 * Z^((2*a-1)*ell + 4*ε₁)) := by
  set H := G.pool with hHdef
  have hHp : RayOrthogonality.globalUnits rayM ≤ H := hHpool G hH
  obtain ⟨Cr, hCr, hpw⟩ := inverse_row_pointwise Φ ao bo hao hΦs hΦ 1 2 τ εpw e e ηw
    zero_le_one (by norm_num) hτ hεpw he he' he (by linarith) hηw (by linarith)
  obtain ⟨Cs, hCs, hsl⟩ := core_slot_bound rayM H hHp W hWs hW (1/2) 2 τ ε₁ e e ηw
    (by norm_num) (by norm_num) hτ hε₁ he he' he hηw hbsl
  refine ⟨Cr, hCr, Cs, hCs, fun tw => ?_⟩
  obtain ⟨Kc, hKc, hcond⟩ := raw_conductor_bound rayM H hHp data (twistEta rayM G hH data tw)
  filter_upwards [eventually_ge_atTop Kc, eventually_ge_atTop (2:ℝ),
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop 2)] with Z hZK hZge hZτ
  have hZ1 : 1 < Z := by linarith
  refine ⟨hZ1, hZτ, ?_⟩
  intro c B hnc hnorm a j ha ha1 hguard hgate4
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hZ2 : Z^(2:ℝ) = Z * Z := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
  have h2Z : 2 ≤ Z^(2:ℝ) := by
    rw [hZ2]; nlinarith
  set w := ProbePhysical.sixthFrequencyEquiv (c, B) with hw
  have hn := rawFam_nonprincipal rayM H hHp data (twistEta rayM G hH data tw) c B hnc
  have hmax : HeckeDetectorZeros.zeroMaximum (rawFam rayM H hHp data (twistEta rayM G hH data tw)
      w.val w.property) hn (3*(j+1 : ℕ)*Z^τ) < a + 2*e := by
    rw [rawFam_maximum_eq_core rayM H hHp data (twistEta rayM G hH data tw) c B hnc hn]
    exact hguard
  have hKN : Kc * ((Ideal.span {w.val}).absNorm : ℝ) ≤ Z^(2:ℝ) := by
    rw [hZ2]
    exact mul_le_mul hZK hnorm (Nat.cast_nonneg _) hZ0.le
  refine ⟨fun r θ hr0 hr1 hfreq => ?_, fun ell v hell0 hell1 hfreq => ?_⟩
  · have hb := hpw Z 2 hZ1.le (by norm_num) le_rfl hZτ
      (rawFam rayM H hHp data (twistEta rayM G hH data tw) w.val w.property) hn a j ha ha1 hmax
      (Sum.inl ()) (r/2) θ ((hcond w.val w.property).1 _ |>.trans hKN) (by linarith)
      (by linarith) hfreq hgate4
    rw [rawFam_inl, scale_rescale hZ0 (by norm_num : (0:ℝ) < 2)] at hb
    rw [polynomial_data_natural]
    refine hb.trans_eq ?_
    rw [← Real.rpow_mul hZ0.le]
    congr 2
    ring
  · have hgate2 : (3+(3*j+2 : ℕ)*Z^τ)^2 ≤ (Z^(2:ℝ))^ηw := by
      have h3 : (1:ℝ) ≤ 3+(3*j+2 : ℕ)*Z^τ := by
        have : (0:ℝ) ≤ ((3*j+2 : ℕ) : ℝ) := Nat.cast_nonneg _
        have := Real.rpow_nonneg hZ0.le τ
        nlinarith
      exact le_trans (pow_le_pow_right₀ h3 (by norm_num)) hgate4
    have hb := hsl Z 2 hZ1.le (by norm_num) le_rfl h2Z hZτ (dataBase data)
      (twistEta rayM G hH data tw) w.val w.property hn 1 a j ha ha1 hmax (ell/2) (33/50) v
      (by linarith) (by linarith) le_rfl le_rfl
      (fun θ' => (hcond w.val w.property).2 1 θ' |>.trans hKN) hfreq hgate2
    rw [scale_rescale hZ0 (by norm_num : (0:ℝ) < 2)] at hb
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
    refine hsq.trans_eq ?_
    rw [mul_pow, ← Real.rpow_mul hZ0.le,
      ← Real.rpow_natCast (Z^((2:ℝ)*((a-1/2)*(ell/2)+ε₁))) 2, ← Real.rpow_mul hZ0.le]
    congr 2
    push_cast
    ring

/-- **Slot envelope of a canonical inverse row** (all widths): slots below the width floor by the
trivial bound, the others through the slot dictionary and the raw slot bound. -/
theorem canonical_envelope (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
    (hH : RayOrthogonality.globalUnits rayM ≤ G.twist)
    (W : ℝ → ℂ) (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (data : RowData)
    (tw : RayQuotient.Characters rayM G.twist) {Z a e ε₁ lam' wmin Cs : ℝ} (hZ : 1 < Z)
    (ha : 51/100 ≤ a) (he : 0 < e) (h4 : 4*ε₁ ≤ lam') (hwl : wmin ≤ lam')
    (hdel : ((DetectorDictionaryInverseRawInitialGates.deletedBase data).modulus.absNorm : ℝ) <
      Z^wmin)
    (hfbm : ((Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm : ℝ) < Z^wmin)
    {ι : Type} (ell v : ι → ℝ) (hell0 : ∀ i, 0 ≤ ell i)
    (hβ : ∀ i, ∀ P ∈ canonicalPool rayM G.pool (Z^(ell i)),
      ‖rayCoeff rayM G hH W (33/50) data tw (Z^(ell i)) (v i) P‖ ≤ 1)
    (w : O) (hw : w ≠ 0)
    (hslot : ∀ i, wmin ≤ ell i →
      ‖naturalSlot (naturalRow (dataBase data) w hw).character
          (primePool rayM G.pool 2 (Z^(ell i)))
          (fun I => idealCoeff (relativeCharacter rayM G.pool (hHpool G hH)
              (twistEta rayM G hH data tw) 1) I *
            HeckePrimeAnnular.annularWeight W (Z^(ell i)) (33/50) (v i) I) (Z^(ell i))‖^2 ≤
        Cs^2 * Z^((2*a-1)*ell i + 4*ε₁)) :
    ∀ i, ‖directSlot w (canonicalPool rayM G.pool (Z^(ell i)))
        (rayCoeff rayM G hH W (33/50) data tw (Z^(ell i)) (v i)) (Z^(ell i))‖^2 ≤
      (65536 + Cs^2) * Z^((2*(a+2*e)-1)*ell i + lam') := by
  intro i
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hD : 1 ≤ Z^(ell i) := Real.one_le_rpow hZ.le (hell0 i)
  have hD0 : 0 < Z^(ell i) := zero_lt_one.trans_le hD
  have hCs2 : 0 ≤ Cs^2 := sq_nonneg _
  have hE0 : 0 ≤ Z^((2*(a+2*e)-1)*ell i + lam') := Real.rpow_nonneg hZ0.le _
  rcases lt_or_ge (ell i) wmin with hsm | hbg
  · have ht := trivial_slot w (canonicalPool rayM G.pool (Z^(ell i)))
      (rayCoeff rayM G hH W (33/50) data tw (Z^(ell i)) (v i)) (Z^(ell i)) hD
      (fun P hP => by
        simp only [canonicalPool, primePool, Finset.mem_filter] at hP
        refine ⟨hP.1.2.1.ne_zero, ?_⟩
        have := (div_le_iff₀ hD0).mp hP.2.2
        linarith) (hβ i)
    have hexp : ell i ≤ (2*(a+2*e)-1)*ell i + lam' := by
      have : (2 - 2*(a+2*e))*ell i ≤ 1*ell i :=
        mul_le_mul_of_nonneg_right (by linarith) (hell0 i)
      linarith
    have hz := Real.rpow_le_rpow_of_exponent_le hZ.le hexp
    calc _ ≤ 65536 * Z^(ell i) := ht
      _ ≤ 65536 * Z^((2*(a+2*e)-1)*ell i + lam') := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hE0
  · have hDdel := lt_of_lt_of_le hdel (Real.rpow_le_rpow_of_exponent_le hZ.le hbg)
    have hDfbm := lt_of_lt_of_le hfbm (Real.rpow_le_rpow_of_exponent_le hZ.le hbg)
    rw [directSlot_eq_natural rayM G hH W hWs (33/50) data tw hD0 (v i) hDdel hDfbm w hw]
    have hexp : (2*a-1)*ell i + 4*ε₁ ≤ (2*(a+2*e)-1)*ell i + lam' := by
      have : 0 ≤ 4*e*ell i := by have := hell0 i; positivity
      nlinarith
    have hz := Real.rpow_le_rpow_of_exponent_le hZ.le hexp
    calc _ ≤ Cs^2 * Z^((2*a-1)*ell i + 4*ε₁) := hslot i hbg
      _ ≤ Cs^2 * Z^((2*(a+2*e)-1)*ell i + lam') := mul_le_mul_of_nonneg_left hz hCs2
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hE0

end
end Qrh.TwoSlot.AnchorZeroLoss.High.Inverse

#print axioms Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.inverse_row_inputs
#print axioms Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.canonical_envelope
