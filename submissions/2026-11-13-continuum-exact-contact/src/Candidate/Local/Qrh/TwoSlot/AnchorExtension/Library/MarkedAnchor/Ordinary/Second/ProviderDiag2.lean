/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Provider, diagonal half: constant absorption and the size bounds of the root source.

* `eventually_absorb`: `K·(log Z + 1)·Z^e ≤ Z^c` eventually, for `e < c`.
* Root sizes: `Mall ≤ Kslot^N`, `fullMarkedCost ≤ 1024^N·Kslot^{3N}`, `slotCost ≤ Kslot^{2N}·2^{4N/3}`,
  `profileCap² ≤ 4·Kslot^{2N}·(sC_c W₁·sC_c W₂)²` for `(0,0) ∈ c`.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ProviderDiag

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.Second.ProviderDiag
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentFiniteProfileExceptional
open QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP Qrh.MarkedAnchor.Ordinary.FP
open MixedPrincipalPair MixedPrincipalBudget MixedOriginalTail MixedFirstExceptionalNormalization
open MixedFirstProfileEnvelope RepairedSourceSideSupply
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- **Absorption**: a fixed constant times `log Z + 1` times a smaller power is eventually below
`Z^c`. -/
theorem eventually_absorb (K e c : ℝ) (hec : e < c) :
    ∀ᶠ Z : ℝ in atTop, K*(Real.log Z + 1)*Z^e ≤ Z^c := by
  set r := (c - e)/2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hlim := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hr0)) (max 0 K*(1/r + 1))
  filter_upwards [hlim, eventually_ge_atTop (1:ℝ)] with Z hZr hZ1
  have hz : 0 < Z := zero_lt_one.trans_le hZ1
  have hlog : Real.log Z ≤ Z^r/r := Real.log_le_rpow_div hz.le hr0
  have hZr1 : 1 ≤ Z^r := Real.one_le_rpow hZ1 hr0.le
  have hlog1 : Real.log Z + 1 ≤ (1/r + 1)*Z^r := by
    have : Z^r/r = (1/r)*Z^r := by ring
    nlinarith
  have hlog0 : 0 ≤ Real.log Z + 1 := by have := Real.log_nonneg hZ1; linarith
  have hZe := Real.rpow_pos_of_pos hz e
  calc K*(Real.log Z + 1)*Z^e ≤ max 0 K*(Real.log Z + 1)*Z^e := by
        apply mul_le_mul_of_nonneg_right _ hZe.le
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hlog0
    _ ≤ max 0 K*((1/r + 1)*Z^r)*Z^e := by
        apply mul_le_mul_of_nonneg_right _ hZe.le
        exact mul_le_mul_of_nonneg_left hlog1 (le_max_left _ _)
    _ = (max 0 K*(1/r + 1))*Z^r*Z^e := by ring
    _ ≤ Z^r*Z^r*Z^e := by
        apply mul_le_mul_of_nonneg_right _ hZe.le
        exact mul_le_mul_of_nonneg_right hZr (Real.rpow_nonneg hz.le _)
    _ = Z^c := by
        rw [← Real.rpow_add hz, ← Real.rpow_add hz]; congr 1; rw [hr]; ring

/-! ### Sizes of a source with bounded marked amplitudes -/

theorem prodM_le (s : Source ι a b) (Kslot : ℝ) (N : ℕ) (hcard : Fintype.card ι ≤ N)
    (hM : ∀ i, s.M i ≤ Kslot) (hK : 1 ≤ Kslot) : (∏ i, s.M i) ≤ Kslot^N := by
  calc (∏ i, s.M i) ≤ ∏ _i : ι, Kslot :=
        Finset.prod_le_prod₀ (fun i _ => zero_le_one.trans (s.hM i)) (fun i _ => hM i)
    _ = Kslot^(Fintype.card ι) := by rw [Finset.prod_const, Finset.card_univ]
    _ ≤ Kslot^N := pow_le_pow_right₀ hK hcard

theorem prodM_ge (s : Source ι a b) : 1 ≤ ∏ i, s.M i := by
  simpa using Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ => (1:ℝ)) (g := s.M)
    (fun _ _ => zero_le_one) (fun i _ => s.hM i)

theorem fullMarkedCost_le (s : Source ι a b) (Kslot : ℝ) (N : ℕ) (hcard : Fintype.card ι ≤ N)
    (hM : ∀ i, s.M i ≤ Kslot) (hK : 1 ≤ Kslot) :
    fullMarkedCost s ≤ (1024:ℝ)^N*(Kslot^N)^3 := by
  rw [fullMarkedCost_eq]
  have h1 : (1024:ℝ)^Fintype.card ι ≤ 1024^N := pow_le_pow_right₀ (by norm_num) hcard
  have h2 := pow_le_pow_left₀ (zero_le_one.trans (prodM_ge s)) (prodM_le s Kslot N hcard hM hK) 3
  have hK0 : 0 ≤ Kslot := zero_le_one.trans hK
  have hP0 := zero_le_one.trans (prodM_ge s)
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

theorem slotCost_le_unit (s : Source ι a b) (hd : s.d = (1,1)) (Kslot : ℝ) (N : ℕ)
    (hcard : Fintype.card ι ≤ N) (hM : ∀ i, s.M i ≤ Kslot) (hK : 1 ≤ Kslot) :
    slotCost s ≤ (Kslot^N)^2*((2:ℝ)^N)^(4/3:ℝ) := by
  unfold slotCost
  rw [hd]
  have hp : pairNorm ((1:Id),(1:Id)) = 1 := by simp [pairNorm]
  rw [hp, div_one]
  have h1 := pow_le_pow_left₀ (zero_le_one.trans (prodM_ge s)) (prodM_le s Kslot N hcard hM hK) 2
  have hK0 : 0 ≤ Kslot := zero_le_one.trans hK
  have h2 : ((2:ℝ)^Fintype.card ι)^(4/3:ℝ) ≤ ((2:ℝ)^N)^(4/3:ℝ) :=
    Real.rpow_le_rpow (by positivity) (pow_le_pow_right₀ (by norm_num) hcard) (by norm_num)
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

theorem profileCap_sq_le (s : Source ι a b) (control : Finset (ℕ×ℕ)) (h00 : (0,0) ∈ control)
    (Kslot : ℝ) (N : ℕ) (hcard : Fintype.card ι ≤ N) (hM : ∀ i, s.M i ≤ Kslot) (hK : 1 ≤ Kslot) :
    (profileCap s)^2 ≤ 4*(Kslot^N)^2*(sourceControl control s.W₁*sourceControl control s.W₂)^2 := by
  unfold profileCap supControl
  have h1 := sourceControl_mono' (Finset.singleton_subset_iff.mpr h00) s.W₁
  have h2 := sourceControl_mono' (Finset.singleton_subset_iff.mpr h00) s.W₂
  have h10 := sourceControl_nonneg {(0,0)} s.W₁
  have h20 := sourceControl_nonneg {(0,0)} s.W₂
  have hP := prodM_le s Kslot N hcard hM hK
  have hP0 := zero_le_one.trans (prodM_ge s)
  have hprod : 2*sourceControl {(0,0)} s.W₁*sourceControl {(0,0)} s.W₂*(∏ i, s.M i) ≤
      2*(Kslot^N)*(sourceControl control s.W₁*sourceControl control s.W₂) := by
    have := mul_le_mul h1 h2 h20 (h10.trans h1)
    have hK0 : 0 ≤ Kslot^N := by positivity
    calc 2*sourceControl {(0,0)} s.W₁*sourceControl {(0,0)} s.W₂*(∏ i, s.M i)
        = 2*(sourceControl {(0,0)} s.W₁*sourceControl {(0,0)} s.W₂)*(∏ i, s.M i) := by ring
      _ ≤ 2*(sourceControl control s.W₁*sourceControl control s.W₂)*(Kslot^N) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left this (by norm_num)) hP hP0
          have := sourceControl_nonneg control s.W₁
          have := sourceControl_nonneg control s.W₂
          positivity
      _ = _ := by ring
  have h0 : 0 ≤ 2*sourceControl {(0,0)} s.W₁*sourceControl {(0,0)} s.W₂*(∏ i, s.M i) := by positivity
  calc (2*sourceControl {(0,0)} s.W₁*sourceControl {(0,0)} s.W₂*(∏ i, s.M i))^2
      ≤ (2*(Kslot^N)*(sourceControl control s.W₁*sourceControl control s.W₂))^2 :=
        pow_le_pow_left₀ h0 hprod 2
    _ = _ := by ring

/-- The side amplitude dominates the square of the profile controls. -/
theorem controls_sq_le_amplitude (s : Source ι a b) (t₀ V : ℝ) (hV : 0 ≤ V) (J : ℕ)
    (control : Finset (ℕ×ℕ)) (Cside : ℝ) (hC : 0 < Cside) :
    (sourceControl control s.W₁*sourceControl control s.W₂)^2 ≤
      amplitude s t₀ V J control Cside/Cside := by
  have hh1 : 1 ≤ height t₀ V s.t₁ s.t₂ := by
    unfold height; have := abs_nonneg t₀; have := norm_nonneg s.t₁; have := norm_nonneg s.t₂; linarith
  have hamp : amplitude s t₀ V J control Cside/Cside =
      (sourceControl control s.W₁*sourceControl control s.W₂)^2*(height t₀ V s.t₁ s.t₂)^J := by
    unfold amplitude; field_simp
  rw [hamp]
  exact le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ hh1)

end
end Qrh.MarkedAnchor.Ordinary.Second.ProviderDiag
