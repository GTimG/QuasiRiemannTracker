/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Label assembly, part 11: subpower multiplicities and the final per-split bound.

* `mult_subpower` (fields `hmultC`, `hmultD`): with cube-free columns and the norm cap
  `N(C₂), N(D₂) ≤ Z^{2B}`, the labels with a given column number at most `C_δ Z^δ`
  (`τ(G²)²·2^{ω(G)} ≤ τ(G²)³`, `Packet.Fibre.divisor_power_subpower`).
* `box_of_scales` (field `hbox`): if every entry of every dyadic range lies in `[Z^{-c}, Z^{c}]`,
  every range vector lies in `[-M, M]⁴` with `M = ⌈c·log₂ Z⌉ + 2`; `box_card_subpower`:
  `(2M+1)⁴ ≤ Z^δ` eventually.
* `split_label_bound_final`: the label part of one split is at most
  `C·(vol/c_low)·gAmp·Z^{A - c + q_C + ε}·(1+|t|)^{2J}` with `ε` arbitrary, when the box radius is
  `≤ c log₂ Z + 2` and the multiplicity is `≤ Z^{ε/4}`.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly10

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteGroup
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open QRH.SilDensitySplit.CubeFree Qrh.MarkedAnchor.Ordinary QRH.SilDensitySplit.CubeFree.Second Qrh.MarkedAnchor.Ordinary.Second

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource RayFourExpansion
open CenteredMomentSecondActiveDyadic CenteredMomentDyadicCount CenteredMomentSectorLocalization
open CenteredMomentChildRows
open OAI.IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-! ### Multiplicities -/

theorem rad_dvd_self (I : Id) (hI : I ≠ ⊥) :
    (∏ P ∈ IdealMobiusDivisorSum.primeSupport I, P) ∣ I :=
  IdealMobiusDivisorSum.support_product_dvd hI (subset_refl _)

theorem card_commonIndex_le (I J : Id) :
    Fintype.card (CommonIndex I J) ≤ (IdealMobiusDivisorSum.primeSupport I).card := by
  rw [Fintype.card_coe]
  exact Finset.card_le_card Finset.inter_subset_left

theorem two_pow_le_card (G : Id) (hG : G ≠ ⊥) :
    2^(IdealMobiusDivisorSum.primeSupport G).card ≤ (idealDivisors G).card := by
  have h := rho_le_card_divisors G hG
  unfold rho at h
  exact_mod_cast h

/-- The label multiplicity of one column. -/
theorem mult_le (S : Finset Id) (side : Bool)
    (hcube : ∀ l : Lab S, l.1.val.1 ∣ (∏ P ∈ IdealMobiusDivisorSum.primeSupport l.1.val.1, P)^2 ∧
      l.1.val.2 ∣ (∏ P ∈ IdealMobiusDivisorSum.primeSupport l.1.val.2, P)^2)
    (G : Id) (A : O) (hG : G ≠ ⊥) :
    ((Finset.univ : Finset (Lab S)).filter (fun l =>
        (if side then l.1.val.1 else l.1.val.2) = G ∧ lA S l = A)).card ≤
      (idealDivisors (G^2)).card^3 := by
  have hG2 : G^2 ≠ ⊥ := pow_ne_zero 2 hG
  have hsub : (Finset.univ : Finset (Lab S)).filter (fun l =>
        (if side then l.1.val.1 else l.1.val.2) = G ∧ lA S l = A) ⊆
      (Finset.univ : Finset (Lab S)).filter
        (fun l => (if side then l.1.val.1 else l.1.val.2) = G) := by
    intro l hl
    rw [Finset.mem_filter] at hl ⊢
    exact ⟨hl.1, hl.2.1⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine (card_Lab_fiber_le S G hG (fun l => if side then l.1.val.1 else l.1.val.2) ?_).trans ?_
  · intro l hl
    have hsupp : IdealMobiusDivisorSum.primeSupport l.1.val.1 =
        IdealMobiusDivisorSum.primeSupport l.1.val.2 := (lab_data S l).2.2
    have h1 := (hcube l).1
    have h2 := (hcube l).2
    have hC0 : l.1.val.1 ≠ ⊥ := (lab_data S l).1.1
    have hD0 : l.1.val.2 ≠ ⊥ := (lab_data S l).2.1.1
    cases side
    · simp only [Bool.false_eq_true, ite_false] at hl
      subst hl
      refine ⟨?_, dvd_pow_self _ two_ne_zero, ?_⟩
      · rw [hsupp] at h1
        exact h1.trans (pow_dvd_pow_of_dvd (rad_dvd_self _ hD0) 2)
      · exact (card_commonIndex_le _ _).trans (le_of_eq (by rw [hsupp]))
    · simp only [ite_true] at hl
      subst hl
      refine ⟨dvd_pow_self _ two_ne_zero, ?_, card_commonIndex_le _ _⟩
      rw [← hsupp] at h2
      exact h2.trans (pow_dvd_pow_of_dvd (rad_dvd_self _ hC0) 2)
  · have h1 := two_pow_le_card G hG
    have h2 : (idealDivisors G).card ≤ (idealDivisors (G^2)).card :=
      card_divisors_mono hG2 (dvd_pow_self G two_ne_zero) hG
    calc (idealDivisors (G^2)).card^2 * 2^(IdealMobiusDivisorSum.primeSupport G).card
        ≤ (idealDivisors (G^2)).card^2 * (idealDivisors (G^2)).card :=
          Nat.mul_le_mul_left _ (h1.trans h2)
      _ = _ := by ring

/-- **Subpower multiplicities** (fields `hmultC`, `hmultD`). -/
theorem mult_subpower (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ Cδ : ℝ, 0 < Cδ ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ (S : Finset Id) (side : Bool),
      (∀ l : Lab S, l.1.val.1 ∣ (∏ P ∈ IdealMobiusDivisorSum.primeSupport l.1.val.1, P)^2 ∧
        l.1.val.2 ∣ (∏ P ∈ IdealMobiusDivisorSum.primeSupport l.1.val.2, P)^2) →
      (∀ l : Lab S, (l.1.val.1.absNorm : ℝ) ≤ Z^(2*B) ∧ (l.1.val.2.absNorm : ℝ) ≤ Z^(2*B)) →
      ∀ (G : Id) (A : O),
        (((Finset.univ : Finset (Lab S)).filter (fun l =>
          (if side then l.1.val.1 else l.1.val.2) = G ∧ lA S l = A)).card : ℝ) ≤ Cδ * Z^δ := by
  obtain ⟨Cδ, hCδ, hdiv⟩ := Packet.Fibre.divisor_power_subpower 3 (4*B) δ (by positivity) hδ
  refine ⟨Cδ, hCδ, ?_⟩
  intro Z hZ S side hcube hnorm G A
  have hZ0 : 0 < Z := by linarith
  by_cases hex : ∃ l : Lab S, (if side then l.1.val.1 else l.1.val.2) = G
  · obtain ⟨l, hl⟩ := hex
    have hG0 : G ≠ ⊥ := by
      rw [← hl]; cases side
      · exact (lab_data S l).2.1.1
      · exact (lab_data S l).1.1
    have hNG : (G.absNorm : ℝ) ≤ Z^(2*B) := by
      rw [← hl]; cases side
      · exact (hnorm l).2
      · exact (hnorm l).1
    have hNG2 : ((G^2).absNorm : ℝ) ≤ Z^(4*B) := by
      rw [map_pow, Nat.cast_pow, show 4*B = 2*B*2 by ring, Real.rpow_mul hZ0.le, Real.rpow_two]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hNG 2
    have hc := mult_le S side hcube G A hG0
    have hd := hdiv Z hZ (G^2) (pow_ne_zero 2 hG0) hNG2
    calc _ ≤ (((idealDivisors (G^2)).card^3 : ℕ) : ℝ) := by exact_mod_cast hc
      _ = ((idealDivisors (G^2)).card : ℝ)^3 := by push_cast; ring
      _ ≤ _ := hd
  · push Not at hex
    rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr (fun l _ h => hex l h.1))]
    push_cast
    positivity

/-! ### The box of dyadic classes -/

theorem indices_subset_Icc (lo hi Zc : ℝ) (M : ℤ) (hlo : 0 < lo)
    (hM1 : -(M:ℝ) ≤ Real.logb 2 lo) (hM2 : Real.logb 2 (4 * hi) ≤ M) :
    ∀ n ∈ indices lo hi, n ∈ Finset.Icc (-M) M := by
  intro n hn
  unfold indices at hn
  rw [Finset.mem_Icc] at hn ⊢
  constructor
  · have := Int.le_ceil (Real.logb 2 lo)
    have h1 : (-M : ℤ) ≤ ⌈Real.logb 2 lo⌉ := by
      have : (-(M:ℝ)) ≤ (⌈Real.logb 2 lo⌉ : ℝ) := hM1.trans (Int.le_ceil _)
      exact_mod_cast this
    exact h1.trans hn.1
  · have h2 : ⌊Real.logb 2 (4 * hi)⌋ ≤ M := Int.floor_le_iff.mpr (by
      have := hM2; push_cast; linarith)
    exact hn.2.trans h2

/-- **Field `hbox` from scale bounds.** -/
theorem box_of_scales (S : Finset Id) (Kc R H : ℝ) (M : ℤ)
    (hsc : ∀ l : Lab S, ∀ i, 0 < sourceLower l.1.val.1 l.1.val.2 (lA S l) Kc i ∧
      -(M:ℝ) ≤ Real.logb 2 (sourceLower l.1.val.1 l.1.val.2 (lA S l) Kc i) ∧
      Real.logb 2 (4 * sourceUpper l.1.val.1 l.1.val.2 (lA S l) Kc R H i) ≤ M) :
    ∀ l n, inRange S Kc R H l n → n ∈ box M := by
  intro l n hr
  unfold box
  rw [Fintype.mem_piFinset]
  intro i
  obtain ⟨h0, h1, h2⟩ := hsc l i
  exact indices_subset_Icc _ _ 0 M h0 h1 h2 (n i) (hr i)

/-- The box radius is logarithmic: `(2M+1)⁴ ≤ Z^δ` eventually, for `M ≤ c log₂ Z + 2`. -/
theorem box_card_subpower (c δ : ℝ) (hc : 0 ≤ c) (hδ : 0 < δ) :
    ∀ᶠ Z : ℝ in atTop, ∀ M : ℤ, 0 ≤ M → (M:ℝ) ≤ c * Real.logb 2 Z + 2 →
      ((box M).card : ℝ) ≤ Z^δ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set e : ℝ := δ/8 with he
  have he0 : 0 < e := by positivity
  set K : ℝ := 2 * c / (e * Real.log 2) + 5 with hK
  have hK0 : 0 ≤ K := by positivity
  have hev : ∀ᶠ Z : ℝ in atTop, K^4 ≤ Z^(δ/2) :=
    (tendsto_rpow_atTop (show (0:ℝ) < δ/2 by positivity)).eventually_ge_atTop (K^4)
  filter_upwards [hev, eventually_gt_atTop (1:ℝ)] with Z hZK hZ1 M hM0 hM
  have hZ0 : 0 < Z := by linarith
  have hZe : 1 ≤ Z^e := Real.one_le_rpow hZ1.le he0.le
  have hlog : Real.log Z ≤ Z^e / e := Real.log_le_rpow_div hZ0.le he0
  have hlb : c * Real.logb 2 Z ≤ (2 * c / (e * Real.log 2)) / 2 * Z^e := by
    unfold Real.logb
    have : c * (Real.log Z / Real.log 2) ≤ c * (Z^e / e / Real.log 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlog hl2.le) hc
    calc c * (Real.log Z / Real.log 2) ≤ c * (Z^e / e / Real.log 2) := this
      _ = (2 * c / (e * Real.log 2)) / 2 * Z^e := by field_simp
  have hbase : 2 * (M:ℝ) + 1 ≤ K * Z^e := by
    have hcl : 0 ≤ 2 * c / (e * Real.log 2) := by positivity
    nlinarith
  have hn : ((2*M+1).toNat : ℝ) = 2*(M:ℝ)+1 := by
    have h := Int.toNat_of_nonneg (show 0 ≤ 2*M+1 by omega)
    rw [show ((2*M+1).toNat : ℝ) = (((2*M+1).toNat : ℤ) : ℝ) from (Int.cast_natCast _).symm, h]
    push_cast; ring
  have hcast : (((2*M+1).toNat ^ 4 : ℕ) : ℝ) = (2*(M:ℝ)+1)^4 := by
    push_cast; rw [hn]
  rw [card_box, hcast]
  have hMr : (0:ℝ) ≤ M := by exact_mod_cast hM0
  have hM0' : (0:ℝ) ≤ 2 * (M:ℝ) + 1 := by linarith
  calc (2*(M:ℝ)+1)^4 ≤ (K * Z^e)^4 := pow_le_pow_left₀ hM0' hbase 4
    _ = K^4 * Z^(δ/2) := by
        have h4 : (Z^e)^4 = Z^(δ/2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]
          congr 1
          rw [he]; push_cast; ring
        rw [mul_pow, h4]
    _ ≤ Z^(δ/2) * Z^(δ/2) := mul_le_mul_of_nonneg_right hZK (by positivity)
    _ = Z^δ := by rw [← Real.rpow_add hZ0]; ring_nf

end
end Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
