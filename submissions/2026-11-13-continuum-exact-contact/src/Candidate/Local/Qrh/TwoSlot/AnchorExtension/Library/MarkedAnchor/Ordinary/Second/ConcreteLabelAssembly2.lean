/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Label assembly, part 2: one dyadic class of one residual split.

* `weighted_column_bound`: if each weighted grouped source energy is at most `Λ` times the
  weighted frame energy of an injectively assigned frame label, a height-uniform bound `B` of
  the frame group (Seam B) gives the height-uniform bound `Λ·B` of the weighted source sum
  (the hypotheses `hleft`/`hright` of `Concrete.grouped_label_blocks`).
* `frame_ratio`: the frame product `gWeight·gEnergy` of a concrete label is
  `ρ(G)·‖pref‖·N(G)·(Z^k/X²)·rawEnergy` (the second artificial divisor cancels).
* `outerScalar_le`: within a dyadic class, `outerScalar ≤ c₀ X · (Z^k/X²)` when
  `Z^k = K` and `X ≤ c₀ N(C₂) d₂`, `X ≤ c₀ N(D₂) d₃` (column-norm bounds).
* `seam_column`: Seam B at one scale on an admissible group with branch data gives the
  frame bound at exponent `A - c + q_C + ε` (as `ConcreteWindow.summed_sides_window`).
* `class_label_bound`: for one class (common kernel ratio, window centres, row scale `H`)
  and label weights `wt`, the grouped label-block sum of the split is at most
  `Cg · windowBudget J t (Λ B_C) · windowBudget J t (Λ B_D)`.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ConcreteWindow
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalLedger

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
open QRH.SilDensitySplit.CubeFree.Packet.Grouped QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSecondWindowBudget
local notation "O" => HeckeFamily.O

variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

/-- **Weighted transfer of a height-uniform frame bound to the grouped source energies.** -/
theorem weighted_column_bound {K : Type*} (η : Character) (rs : GSrc θ mesh Z) (Ks : Finset K)
    (wt : K → ℝ) (src : K → ℝ → ℝ) (X : K → GLabel θ mesh Z) (hX : Set.InjOn X Ks)
    (Λ B : ℝ) (hΛ : 0 ≤ Λ) (J : ℕ)
    (hratio : ∀ k ∈ Ks, ∀ v : ℝ, wt k * src k v ≤ Λ * (gWeight (X k) * gEnergy η rs (X k) v))
    (hseam : ∀ v : ℝ, ∑ x ∈ Ks.image X, gWeight x * gEnergy η rs x v ≤ B * (1 + ‖v‖)^(2*J)) :
    ∀ v : ℝ, ∑ k ∈ Ks, wt k * src k v ≤ (Λ * B) * (1 + ‖v‖)^(2*J) := by
  intro v
  calc ∑ k ∈ Ks, wt k * src k v ≤ ∑ k ∈ Ks, Λ * (gWeight (X k) * gEnergy η rs (X k) v) :=
        Finset.sum_le_sum fun k hk => hratio k hk v
    _ = Λ * ∑ x ∈ Ks.image X, gWeight x * gEnergy η rs x v := by
        rw [Finset.sum_image hX, Finset.mul_sum]
    _ ≤ Λ * (B * (1 + ‖v‖)^(2*J)) := mul_le_mul_of_nonneg_left (hseam v) hΛ
    _ = (Λ * B) * (1 + ‖v‖)^(2*J) := by ring

/-- `weighted_column_bound` without injectivity: every frame label is hit by at most `M`
indices (e.g. `M ≤ 4^{ω(G)} ≤ Z^δ` for the choices of `D₂` and `U` with the same twist). -/
theorem weighted_column_bound_mult {K : Type*} (η : Character) (rs : GSrc θ mesh Z)
    (Ks : Finset K) (wt : K → ℝ) (src : K → ℝ → ℝ) (X : K → GLabel θ mesh Z)
    (M : ℕ) (hM : ∀ y ∈ Ks.image X, (Ks.filter (fun k => X k = y)).card ≤ M)
    (Λ B : ℝ) (hΛ : 0 ≤ Λ) (hB : 0 ≤ B) (J : ℕ)
    (hratio : ∀ k ∈ Ks, ∀ v : ℝ, wt k * src k v ≤ Λ * (gWeight (X k) * gEnergy η rs (X k) v))
    (hseam : ∀ v : ℝ, ∑ x ∈ Ks.image X, gWeight x * gEnergy η rs x v ≤ B * (1 + ‖v‖)^(2*J)) :
    ∀ v : ℝ, ∑ k ∈ Ks, wt k * src k v ≤ (Λ * M * B) * (1 + ‖v‖)^(2*J) := by
  intro v
  have hnn : ∀ y, 0 ≤ gWeight y * gEnergy η rs y v := fun y =>
    mul_nonneg (gWeight_nonneg y) ((gFrame L θ mesh η Z).energy_nonneg rs y v)
  calc ∑ k ∈ Ks, wt k * src k v ≤ ∑ k ∈ Ks, Λ * (gWeight (X k) * gEnergy η rs (X k) v) :=
        Finset.sum_le_sum fun k hk => hratio k hk v
    _ = Λ * ∑ y ∈ Ks.image X, ((Ks.filter (fun k => X k = y)).card : ℝ) *
          (gWeight y * gEnergy η rs y v) := by
        rw [← Finset.mul_sum, Finset.sum_image' (fun k => gWeight (X k) * gEnergy η rs (X k) v)]
        intro y hy
        rw [Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.mp hk).2]),
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ Λ * ∑ y ∈ Ks.image X, (M : ℝ) * (gWeight y * gEnergy η rs y v) := by
        apply mul_le_mul_of_nonneg_left _ hΛ
        exact Finset.sum_le_sum fun y hy =>
          mul_le_mul_of_nonneg_right (by exact_mod_cast hM y hy) (hnn y)
    _ ≤ Λ * (M * (B * (1 + ‖v‖)^(2*J))) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hseam v) (Nat.cast_nonneg _)) hΛ
    _ = (Λ * M * B) * (1 + ‖v‖)^(2*J) := by ring

/-- The frame product of a fitting label. -/
theorem frame_ratio (η : Character) (rs : GSrc θ mesh Z) (x : GLabel θ mesh Z) (h : Fits η rs x)
    (v : ℝ) :
    gWeight x * gEnergy η rs x v =
      rho x.common * ‖x.prefactor‖ * (x.G.absNorm : ℝ) *
        ((x.d.1.absNorm : ℝ) * (x.d.2.absNorm : ℝ)) * rs.norm * rawEnergy η rs x h v := by
  have hD : (x.D.absNorm : ℝ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr h.D_sq.ne_zero
  unfold gWeight gEnergy
  rw [dif_pos h]
  field_simp

/-- The pointwise ratio for a concrete label: a weight below `Λ ρ(G) ‖pref‖ N(G) (Z^k/X²)` and a
source energy below the literal frame energy. -/
theorem pointwise_ratio (η : Character) (rs : GSrc θ mesh Z) (x : GLabel θ mesh Z)
    (h : Fits η rs x) (w src Λ : ℝ) (v : ℝ) (hw0 : 0 ≤ w)
    (hw : w ≤ Λ * (rho x.common * ‖x.prefactor‖ * (x.G.absNorm : ℝ) *
      ((x.d.1.absNorm : ℝ) * (x.d.2.absNorm : ℝ)) * rs.norm))
    (hsrc0 : 0 ≤ src) (hsrc : src ≤ rawEnergy η rs x h v) :
    w * src ≤ Λ * (gWeight x * gEnergy η rs x v) := by
  rw [frame_ratio η rs x h v]
  have hr := rawEnergy_nonneg η rs x h v
  calc w * src ≤ (Λ * (rho x.common * ‖x.prefactor‖ * (x.G.absNorm : ℝ) *
        ((x.d.1.absNorm : ℝ) * (x.d.2.absNorm : ℝ)) * rs.norm)) *
        rawEnergy η rs x h v := mul_le_mul hw hsrc hsrc0 (hw0.trans hw)
    _ = _ := by ring

/-- **The outer scalar within a dyadic class.** -/
theorem outerScalar_le (C D : Ideal O) (hC : C ≠ 0) (hD : D ≠ 0) (K : ℝ) (hK : 0 ≤ K)
    (n : Fin 4 → ℤ) (Xv c₀ : ℝ) (hX : 0 < Xv) (hc₀ : 0 < c₀)
    (h1 : Xv ≤ c₀ * ((C.absNorm : ℝ) * CenteredMomentSectorLocalization.dyadicScale (n 2)))
    (h2 : Xv ≤ c₀ * ((D.absNorm : ℝ) * CenteredMomentSectorLocalization.dyadicScale (n 3))) :
    CenteredMomentSecondPhysicalBlock.outerScalar C D K n ≤ (c₀ * Xv) * (K / Xv^2) := by
  unfold CenteredMomentSecondPhysicalBlock.outerScalar
  have hCn : 0 < (C.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hDn : 0 < (D.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hd2 := CenteredMomentSectorLocalization.dyadicScale_pos (n 2)
  have hd3 := CenteredMomentSectorLocalization.dyadicScale_pos (n 3)
  set P := Real.sqrt (C.absNorm : ℝ) * Real.sqrt (D.absNorm : ℝ) *
    Real.sqrt (CenteredMomentSectorLocalization.dyadicScale (n 2)) *
    Real.sqrt (CenteredMomentSectorLocalization.dyadicScale (n 3)) with hP
  have hPsq : P^2 = ((C.absNorm : ℝ) * CenteredMomentSectorLocalization.dyadicScale (n 2)) *
      ((D.absNorm : ℝ) * CenteredMomentSectorLocalization.dyadicScale (n 3)) := by
    rw [hP, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hCn.le, Real.sq_sqrt hDn.le,
      Real.sq_sqrt hd2.le, Real.sq_sqrt hd3.le]
    ring
  have hP0 : 0 < P := by rw [hP]; positivity
  have a1 : Xv / c₀ ≤ (C.absNorm : ℝ) * CenteredMomentSectorLocalization.dyadicScale (n 2) := by
    rw [div_le_iff₀ hc₀]; linarith
  have a2 : Xv / c₀ ≤ (D.absNorm : ℝ) * CenteredMomentSectorLocalization.dyadicScale (n 3) := by
    rw [div_le_iff₀ hc₀]; linarith
  have hsq : (Xv / c₀)^2 ≤ P^2 := by
    rw [hPsq, sq]
    exact mul_le_mul a1 a2 (by positivity) (by positivity)
  have hXP : Xv / c₀ ≤ P := (sq_le_sq₀ (by positivity) hP0.le).mp hsq
  rw [div_le_iff₀ hP0]
  calc K = (c₀ * Xv) * (K / Xv^2) * (Xv / c₀) := by field_simp
    _ ≤ (c₀ * Xv) * (K / Xv^2) * P :=
        mul_le_mul_of_nonneg_left hXP (by positivity)

/-- **Seam B on one column** (the step of `ConcreteWindow.summed_sides_window`): the pointwise
grouped bounds for the step price and the native price, an admissible group and its branch
data give the frame bound at exponent `A - c + q_C + ε`. -/
theorem seam_column (D : StepData) (G : StepGates D) {F : SideFrame} {ε mesh : ℝ} (hε : 0 < ε)
    (hm0 : 0 ≤ mesh) (hmL : mesh ≤ G.meshL ε) (Z : ℝ) (hZ1 : 1 ≤ Z)
    (ampL ampS CL CS : ℝ) (dL dS : ℕ) (hCL : 0 ≤ CL) (hCS : 0 ≤ CS) (hampL : 0 ≤ ampL)
    (hampS : 0 ≤ ampS) (r : F.Src) (labels : Finset F.Label) (A c qC H : ℝ)
    (hL : ∀ w₀ : ℝ, ∀ v : ℝ, ∑ x ∈ labels, F.weight x * F.energy r x v ≤
      CL * ampL * (1 + ‖v‖)^(2*dL) * Z^(F.logScale r + D.price.f w₀ (F.P r) (F.s r) H + ε/2))
    (hS : ∀ v : ℝ, ∑ x ∈ labels, F.weight x * F.energy r x v ≤
      CS * ampS * (1 + ‖v‖)^(2*dS) *
        Z^(F.logScale r + (nativePrice (3/4) (by norm_num)).f 0 (F.P r) (F.s r) H + ε/2))
    (hb : BranchData D G F ε mesh r A c qC H) :
    ∀ v : ℝ, ∑ x ∈ labels, F.weight x * F.energy r x v ≤
      (max CL CS * max ampL ampS * Z^(A - c + qC + ε)) * (1 + ‖v‖)^(2*max dL dS) := by
  intro v
  have hX1 : (1:ℝ) ≤ 1 + ‖v‖ := by linarith [norm_nonneg v]
  rcases Concrete.column_exponent' G hε hm0 hmL hb with ⟨w₀, hex⟩ | hex
  · exact (hL w₀ v).trans (Concrete.raise_bound' hX1 hZ1 hCL (le_max_left _ _) hampL
      (le_max_left _ _) (le_max_left _ _) hex)
  · exact (hS v).trans (Concrete.raise_bound' hX1 hZ1 hCS (le_max_right _ _) hampS
      (le_max_right _ _) (le_max_right _ _) hex)

/-- The second-step normalizer is at most the norm of the common frequency generator; hence the
label prefactor `normalizer / N(cfg)` has absolute value at most one. -/
theorem normalizer_le_cfg (C D : Ideal O) (hC : CanonicalQuadraticSieve.Supported C)
    (U : Finset (CenteredMomentCanonicalFirst.CommonIndex C D)) :
    CenteredMomentSecondCanonicalScalar.normalizer C D U ≤
      ((Ideal.span {CenteredMomentSecondCanonical.commonFrequencyGenerator C D}).absNorm : ℝ) := by
  unfold CenteredMomentSecondCanonicalScalar.normalizer CenteredMomentPartition.partitionNormalizer
    CenteredMomentSecondCanonical.commonFrequencyGenerator
  rw [CenteredMomentSecondCanonicalLedger.span_finset_product, map_prod, Nat.cast_prod]
  apply Finset.prod_le_prod₀ (fun i _ => by positivity)
  intro P _
  rw [← Ideal.span_singleton_pow, map_pow, Nat.cast_pow]
  have h1 : (1:ℝ) ≤ (Ideal.absNorm (Ideal.span {CenteredMomentSecondCanonical.commonPrime C D P}) : ℝ) := by
    rw [CenteredMomentSecondCanonical.commonPrime_span C D hC P]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (CenteredMomentSecondCanonical.commonPrime_supported_ideal C D hC P).1)
  exact pow_le_pow_right₀ h1 (Nat.sub_le _ _)

theorem prefactor_norm_le (C D : Ideal O) (hC : CanonicalQuadraticSieve.Supported C)
    (U : Finset (CenteredMomentCanonicalFirst.CommonIndex C D)) :
    ‖((CenteredMomentSecondCanonicalScalar.normalizer C D U /
      ((Ideal.span {CenteredMomentSecondCanonical.commonFrequencyGenerator C D}).absNorm : ℝ) : ℝ) : ℂ)‖
      ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h0 := (CenteredMomentSecondCanonicalScalar.normalizer_pos C D hC U).le
  have h1 := normalizer_le_cfg C D hC U
  rw [abs_of_nonneg (div_nonneg h0 (Nat.cast_nonneg _))]
  rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ)
    (Ideal.span {CenteredMomentSecondCanonical.commonFrequencyGenerator C D}).absNorm) with h | h
  · rw [← h, div_zero]; norm_num
  · rw [div_le_one h]; exact h1

end
end Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
