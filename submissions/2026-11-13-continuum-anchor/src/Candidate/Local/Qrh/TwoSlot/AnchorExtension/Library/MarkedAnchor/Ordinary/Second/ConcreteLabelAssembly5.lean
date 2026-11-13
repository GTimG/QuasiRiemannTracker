/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Label assembly, part 5: arithmetic of the second-step labels.

* `fibre_rows_sq`: `ConcreteGroup.fibre_rows` with codes and common factor dividing the SQUARE
  of the twist (cube-free genuine factors divide `(A₂)²`, not `A₂`).
* `left_dvd_twist_sq`, `right_dvd_twist_sq`: with multiplicities at most two, `C₂ ∣ (A₂)²` and
  `D₂ ∣ (A₂)²` (`left_ideal_product`, `commonFrequencyGenerator`).
* `normalizer_le_left`, `normalizer_le_right`: `normalizer(C₂, D₂, U) ≤ N(C₂), N(D₂)`.
* `norm_rhoC`: `‖ρ_C(G)‖ = ρ(G)`.
* `dyad_of_range`: a dyad vector in the source range of a label has `N(A₂)·2^{n₁} ≤ 4 max(N(A₂), 4R)`.
* `S0_subset`, `S0_zero`: the active residual columns.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly4
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteGroupFibre

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentSecondActiveDyadic CenteredMomentDyadicCount
open CenteredMomentActiveSource CenteredMomentSourceRow
open OAI.IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-! ### Fibre with squared codes -/

theorem fibre_rows_sq (k : ℕ) (Cexp B ε : ℝ) (hCexp : 0 ≤ Cexp) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop, ∀ (L : ℝ) (θ : GData L) (mesh : ℝ)
      (labels : Finset (GLabel θ mesh Z)) (code : GLabel θ mesh Z → Fin k → Ideal O),
      (∀ x ∈ labels, ‖x.prefactor‖ ≤ 1) →
      (∀ x ∈ labels, x.common ∣ (Ideal.span {x.twist})^2) →
      (∀ x ∈ labels, x.D ≠ 0 ∧ (x.D.absNorm : ℝ) ≤ Z^B) →
      (∀ x ∈ labels, ∀ i, code x i ∣ (Ideal.span {x.twist})^2) →
      Set.InjOn (fun x => (code x, x.D)) labels →
      ∀ y : O, y ≠ 0 → ((Ideal.span {y}).absNorm : ℝ) ≤ Z^Cexp →
        ∑ x ∈ labels.filter (fun x => x.twist ∣ y), gWeight x ≤ Z^(ε/8) := by
  obtain ⟨Cd, hCd, hdiv⟩ := Packet.Fibre.divisor_power_subpower (k+1) (2*Cexp) (ε/32) (by positivity)
    (by positivity)
  obtain ⟨Cl, hCl, hlen⟩ := ConcreteGroup.dyadic_length_subpower B (ε/32) hB (by positivity)
  have hev : ∀ᶠ Z : ℝ in atTop, Cd * Cl ≤ Z^(ε/16) :=
    (tendsto_rpow_atTop (show (0:ℝ) < ε/16 by positivity)).eventually_ge_atTop (Cd * Cl)
  filter_upwards [hev, eventually_ge_atTop (1:ℝ)] with Z hZC hZ1
  intro L θ mesh labels code hpref hcom hD hcode hinj y hy hNy
  have hZ0 : 0 < Z := by linarith
  set Y : Ideal O := (Ideal.span {y})^2 with hYdef
  have hY : Y ≠ ⊥ := pow_ne_zero _ (Ideal.span_singleton_eq_bot.not.mpr hy)
  have hNY : (Ideal.absNorm Y : ℝ) ≤ Z^(2*Cexp) := by
    rw [hYdef, map_pow, Nat.cast_pow, mul_comm, Real.rpow_mul hZ0.le, Real.rpow_two]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hNy 2
  set F := labels.filter (fun x => x.twist ∣ y) with hF
  have hFsub : F ⊆ labels := Finset.filter_subset _ _
  have hdvdY : ∀ x ∈ F, (Ideal.span {x.twist})^2 ∣ Y := by
    intro x hx
    exact pow_dvd_pow_of_dvd
      (Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr (Finset.mem_filter.mp hx).2) 2
  set τY : ℝ := ((idealDivisors Y).card : ℝ) with hτY
  have hτ0 : 0 ≤ τY := Nat.cast_nonneg _
  have hw : ∀ x ∈ F, gWeight x ≤ τY * (1 / (x.D.absNorm : ℝ)) := by
    intro x hx
    have hxl := hFsub hx
    have hc : x.common ∣ Y := (hcom x hxl).trans (hdvdY x hx)
    have hc0 : x.common ≠ ⊥ := by
      intro h0; rw [h0] at hc; exact hY (zero_dvd_iff.mp hc)
    have hrho : rho x.common ≤ τY :=
      (ConcreteGroup.rho_le_card_divisors _ hc0).trans
        (by rw [hτY]; exact_mod_cast ConcreteGroup.card_divisors_mono hY hc hc0)
    have hN : 0 < (x.D.absNorm : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hD x hxl).1)
    unfold gWeight
    rw [div_eq_mul_one_div (rho x.common * ‖x.prefactor‖)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc rho x.common * ‖x.prefactor‖ ≤ rho x.common * 1 :=
          mul_le_mul_of_nonneg_left (hpref x hxl) (by unfold rho; positivity)
      _ ≤ τY := by rw [mul_one]; exact hrho
  have hsum : ∑ x ∈ F, 1 / (x.D.absNorm : ℝ) ≤
      ((Packet.Fibre.divisorTuples k Y).card : ℝ) *
        ∑ D ∈ F.image (fun x => x.D), 1 / (D.absNorm : ℝ) := by
    have hinjF : Set.InjOn (fun x => (code x, x.D)) F := hinj.mono (by exact_mod_cast hFsub)
    rw [← Finset.sum_image (f := fun p : (Fin k → Ideal O) × Ideal O => 1 / (p.2.absNorm : ℝ))
      hinjF]
    have himg : F.image (fun x => (code x, x.D)) ⊆
        Packet.Fibre.divisorTuples k Y ×ˢ F.image (fun x => x.D) := by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      refine Finset.mem_product.mpr ⟨?_, Finset.mem_image_of_mem _ hx⟩
      rw [Packet.Fibre.mem_divisorTuples hY]
      exact fun i => (hcode x (hFsub hx) i).trans (hdvdY x hx)
    calc ∑ p ∈ F.image (fun x => (code x, x.D)), 1 / (p.2.absNorm : ℝ)
        ≤ ∑ p ∈ Packet.Fibre.divisorTuples k Y ×ˢ F.image (fun x => x.D),
            1 / (p.2.absNorm : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)
      _ = _ := by
          rw [Finset.sum_product]
          simp only [Finset.sum_const, nsmul_eq_mul]
  have hinv : ∑ D ∈ F.image (fun x => x.D), 1 / (D.absNorm : ℝ) ≤
      256 * ((CanonicalQuadraticSieve.columnDyadicLength (Z^B) : ℝ) + 1) := by
    apply CanonicalQuadraticSieve.finite_inverse_norm_sum
    · intro D hD'
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hD'
      exact (hD x (hFsub hx)).1
    · intro D hD'
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hD'
      exact (hD x (hFsub hx)).2
  have htup : ((Packet.Fibre.divisorTuples k Y).card : ℝ) = τY^k := by
    rw [Packet.Fibre.card_divisorTuples]; push_cast; rfl
  have hτpow : τY^(k+1) ≤ Cd * Z^(ε/32) := hdiv Z hZ1 Y hY hNY
  calc ∑ x ∈ F, gWeight x ≤ ∑ x ∈ F, τY * (1 / (x.D.absNorm : ℝ)) := Finset.sum_le_sum hw
    _ = τY * ∑ x ∈ F, 1 / (x.D.absNorm : ℝ) := by rw [Finset.mul_sum]
    _ ≤ τY * (τY^k * (256 * ((CanonicalQuadraticSieve.columnDyadicLength (Z^B) : ℝ) + 1))) := by
        apply mul_le_mul_of_nonneg_left _ hτ0
        rw [← htup]
        exact hsum.trans (mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _))
    _ = τY^(k+1) * (256 * ((CanonicalQuadraticSieve.columnDyadicLength (Z^B) : ℝ) + 1)) := by
        ring
    _ ≤ (Cd * Z^(ε/32)) * (Cl * Z^(ε/32)) :=
        mul_le_mul hτpow (hlen Z hZ1) (by positivity) (by positivity)
    _ = (Cd * Cl) * Z^(ε/16) := by
        rw [show (Cd * Z^(ε/32)) * (Cl * Z^(ε/32)) = (Cd * Cl) * (Z^(ε/32) * Z^(ε/32)) by ring,
          ← Real.rpow_add hZ0]
        ring_nf
    _ ≤ Z^(ε/16) * Z^(ε/16) := mul_le_mul_of_nonneg_right hZC (by positivity)
    _ = Z^(ε/8) := by rw [← Real.rpow_add hZ0]; ring_nf

/-! ### The genuine common factors divide the squared twist -/

theorem cfg_sq_eq (C D : Id) (hC : Supported C) :
    (Ideal.span {commonFrequencyGenerator C D})^2 =
      ∏ P : CommonIndex C D, Ideal.span {commonPrime C D P}^(2 * min (leftExponent C D P)
        (rightExponent C D P)) := by
  unfold commonFrequencyGenerator
  rw [CenteredMomentSecondCanonicalLedger.span_finset_product, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro P _
  rw [← Ideal.span_singleton_pow, ← pow_mul, mul_comm]

theorem cfg_dvd_twist (C D : Id) (U : Finset (CommonIndex C D)) :
    Ideal.span {commonFrequencyGenerator C D} ∣ Ideal.span {Packet.secondTwist C D U} :=
  Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr (dvd_mul_right _ _)

theorem left_dvd_twist_sq (C D : Id) (hC : Supported C)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (h2 : ∀ P, leftExponent C D P ≤ 2) :
    C ∣ (Ideal.span {Packet.secondTwist C D U})^2 := by
  refine dvd_trans ?_ (pow_dvd_pow_of_dvd (cfg_dvd_twist C D U) 2)
  rw [cfg_sq_eq C D hC]
  conv_lhs => rw [← left_ideal_product C D hC hCD]
  apply Finset.prod_dvd_prod_of_dvd
  intro P _
  apply pow_dvd_pow
  have h1 := leftExponent_pos C D P
  have h3 := rightExponent_pos C D P
  have := h2 P
  have : 1 ≤ min (leftExponent C D P) (rightExponent C D P) := le_min h1 h3
  omega

theorem right_dvd_twist_sq (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (h2 : ∀ P, rightExponent C D P ≤ 2) :
    D ∣ (Ideal.span {Packet.secondTwist C D U})^2 := by
  refine dvd_trans ?_ (pow_dvd_pow_of_dvd (cfg_dvd_twist C D U) 2)
  rw [cfg_sq_eq C D hC]
  conv_lhs => rw [← right_ideal_product C D hC hD hCD]
  apply Finset.prod_dvd_prod_of_dvd
  intro P _
  apply pow_dvd_pow
  have h1 := leftExponent_pos C D P
  have h3 := rightExponent_pos C D P
  have := h2 P
  have : 1 ≤ min (leftExponent C D P) (rightExponent C D P) := le_min h1 h3
  omega

/-! ### Normalizer, `ρ`, dyads, active columns -/

theorem normalizer_le_left (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) : normalizer C D U ≤ (C.absNorm : ℝ) := by
  refine (normalizer_le_cfg C D hC U).trans ?_
  have hd := (commonFrequencyGenerator_dvd C D hC hD hCD).1
  have h := Concrete.absNorm_le_of_dvd (I := Ideal.span {commonFrequencyGenerator C D})
    (J := Ideal.span {primaryGenerator C}) ?_
    (Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr hd)
  · rwa [primary_span_supported C hC] at h
  · rw [primary_span_supported C hC]; exact hC.1

theorem normalizer_le_right (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) : normalizer C D U ≤ (D.absNorm : ℝ) := by
  refine (normalizer_le_cfg C D hC U).trans ?_
  have hd := (commonFrequencyGenerator_dvd C D hC hD hCD).2
  have h := Concrete.absNorm_le_of_dvd (I := Ideal.span {commonFrequencyGenerator C D})
    (J := Ideal.span {primaryGenerator D}) ?_
    (Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr hd)
  · rwa [primary_span_supported D hD] at h
  · rw [primary_span_supported D hD]; exact hD.1

theorem norm_rhoC (G : Id) : ‖rhoC G‖ = rho G := by
  unfold rhoC rho
  rw [norm_pow]
  norm_num
  rfl

theorem dyad_of_range (C D : Id) (A : O) (hA : A ≠ 0) (K R H : ℝ) (n : Fin 4 → ℤ)
    (hn : n 1 ∈ indices (sourceLower C D A K 1) (sourceUpper C D A K R H 1)) :
    normValue A * dyadicScale (n 1) ≤ 4 * max (normValue A) (4 * R) := by
  have hNA : 0 < normValue A := by
    unfold normValue
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hA))
  have hl : sourceLower C D A K 1 = 1 := rfl
  have hu : sourceUpper C D A K R H 1 = max 1 (4*R/normValue A) := rfl
  rw [hl, hu] at hn
  have h := ((mem_indices_iff_scale 1 _ one_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) _).mp hn).2
  calc normValue A * dyadicScale (n 1) ≤ normValue A * (4 * max 1 (4*R/normValue A)) :=
        mul_le_mul_of_nonneg_left h hNA.le
    _ = 4 * max (normValue A * 1) (normValue A * (4*R/normValue A)) := by
        rw [← mul_max_of_nonneg _ _ hNA.le]; ring
    _ = 4 * max (normValue A) (4 * R) := by
        congr 2
        · ring
        · field_simp

theorem S0_subset {ι : Type*} [Fintype ι] {a b : ℝ} (s : Source ι a b) (ha : 0 < a) :
    S0 s ha ⊆ sourceColumns s := by
  intro I hI
  unfold S0 at hI
  rw [mem_activeSource] at hI
  exact hI.1

theorem S0_zero {ι : Type*} [Fintype ι] {a b : ℝ} (s : Source ι a b) (ha : 0 < a) :
    ∀ I ∈ sourceColumns s, I ∉ S0 s ha → sourceCoefficient s ha 1 I = 0 := by
  intro I hI hn
  by_contra h
  apply hn
  unfold S0
  rw [mem_activeSource]
  exact ⟨hI, h⟩

end
end Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
