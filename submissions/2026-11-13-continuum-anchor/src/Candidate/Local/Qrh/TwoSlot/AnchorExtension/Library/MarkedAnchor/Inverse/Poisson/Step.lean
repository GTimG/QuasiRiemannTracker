/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.StepBounds
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.Entry
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.ProfileSep

/-!
# Inverse.Poisson.Step — the second Poisson step (assembly)

`poissonStepStatement : PoissonStepStatement`.

Per label: `Entry` (selected energy ≤ grouped physical rows), `f_decomp` (diagonal + in-ball +
tail), the diagonal by `diagCoeff_norm_le`, the tail by `tail_f_le` (rapid decay at
`T₀ = Z^κ / bl²`, because a row outside the child ball has `Y ‖k‖²/kernelDen ≥ Z^κ/bl²`), and
all labels' in-ball rows at once by `inball_le`. The polylogarithms and the divisor bound are
absorbed in `Z^ε`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap ENNReal ContDiff
open MeasureTheory OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open OAI.FirstPassCubeLabels (primeProductNorm)
open OAI.RayFourExpansion (RayCharacter gCoeff crossCoeff)
open FourierBridge (logPhase)
open IdealMobiusDivisorSum (idealDivisors)

local notation "O" => ActualEisensteinCubic.O

set_option maxHeartbeats 3200000 in
/-- The Poisson step at one scale, with all constants supplied. -/
theorem poisson_at (Kslots : ℕ) (W : ℝ → ℂ) (ao bo : ℝ) (hao : 0 < ao) (hab : ao ≤ bo)
    (hsupp : Function.support W ⊆ Set.Icc ao bo) (Φ : ℝ → ℂ) (hΦ0 : ∀ x, 2 * bo < x → Φ x = 0)
    (b' : 𝓢(ℝ, ℂ))
    (hb' : ∀ r x h : ℝ, 1 ≤ r → r ≤ 2 → 0 < x →
      W (r * x) * logPhase h (Real.log (r * x)) =
        ∫ t : ℝ, logPhase (t + h) (Real.log r) * childLogTest Φ (t + h) x * b' t)
    (d : ℕ) (Cb : ℝ) (hCb : 0 ≤ Cb) (bf : ℝ → 𝓢(ℝ, ℂ))
    (hbf : ∀ R : ℝ, 0 < R → KernelSep SecondPassArithmetic.rowMajorant W R (bf R) ∧
      ∀ t : ℝ, (1 + ‖t‖) ^ (2 * d + 2) * ‖bf R t‖ ≤ Cb)
    (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ) (At : ℕ) (hAt : 14 ≤ κ * At) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hlat : ∀ K T : ℝ, 0 < K → 0 ≤ T →
      (∑' h : {h : O // T ≤ K * ‖eisEmbedding h‖ ^ 2},
        ‖paperRadialFourier SecondPassArithmetic.rowMajorant (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
        Cw / ((min 1 K) ^ 2 * (1 + T) ^ At))
    (δ Cd : ℝ) (hδ : 0 ≤ δ) (hδε : 3 * (δ * (4 + κ)) ≤ ε / 2) (hCd0 : 0 ≤ Cd)
    (hCd : ∀ I : Ideal O, I ≠ ⊥ → ((idealDivisors I).card : ℝ) ≤ Cd * (Ideal.absNorm I : ℝ) ^ δ)
    (η : ℝ) (hη : 0 < η) (hηε : 2 * η * ((2 * Kslots + 2 : ℕ) : ℝ) ≤ ε / 2)
    (Z : ℝ) (hZ : 1 ≤ Z) :
    PoissonStepAt Kslots W bo ![Φ] d d ε κ
      (cIn Kslots d b' Cb Cd η (max bo 1) + cDt Cw (max bo 1) At + 1) Z := by
  intro ι σ _ p hp _ hinj hcop hg hc hpr pool Ψ m slots lists a labels D Dmax N' V K'
    hΨ hslots ha hlab hD hDmax hN' hV hK' hNV hK4 B hB hchild s₀
  obtain ⟨Hc, hHc⟩ : ∃ Hc : ℝ, Hc = 2 * (N' + V) - K' + κ := ⟨_, rfl⟩
  rw [← hHc] at hchild
  have hZ0 : 0 < Z := by linarith
  have hbl1 : 1 ≤ max bo 1 := le_max_right _ _
  have hbobl : bo ≤ max bo 1 := le_max_left _ _
  have hX1 : 1 ≤ Z ^ N' := Real.one_le_rpow hZ hN'
  have hX0 : 0 < Z ^ N' := by linarith
  have hY1 : 1 ≤ Z ^ K' := Real.one_le_rpow hZ hK'
  have hY0 : 0 < Z ^ K' := by linarith
  have hcZ0 : 0 ≤ Z ^ (-(N' + V)) := (Real.rpow_pos_of_pos hZ0 _).le
  have hΛ1 : 1 ≤ max bo 1 * Z ^ N' := one_le_mul_of_one_le_of_one_le hbl1 hX1
  have hWb : ∀ x, W x ≠ 0 → x ≤ max bo 1 := fun x hx => ((hsupp hx).2).trans hbobl
  have hgen : ∀ f ∈ labels, CompletedGauss.primaryGenerator f ≠ 0 := fun f hf => (hlab f hf).1
  have hball0 : (0 : O) ∉ nonzeroChildFrequencyBall 1 (Z ^ Hc) :=
    fun h => ball_ne_zero _ _ h rfl
  have hD0 : ∀ f ∈ labels, 0 ≤ D f := fun f hf => (hD f hf).1
  -- the constants
  set Ct := Cw * 128 ^ 2 * 2 * max bo 1 ^ (7 + 2 * At) with hCt
  have hCt0 : 0 ≤ Ct := mul_nonneg (mul_nonneg (mul_nonneg hCw (by norm_num)) (by norm_num))
    (pow_nonneg (by linarith) _)
  set SH := ∑ U ∈ pool.powerset, ‖entryH p slots lists a W s₀ (Z ^ N') U‖ ^ 2 with hSH
  have hSH0 : 0 ≤ SH := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hG := gSum_nonneg
  -- per label
  have hper : ∀ f ∈ labels,
      D f * (Z ^ (-(N' + V)) *
        (∑ g ∈ pool.powerset, ∑ a' ∈ (pool \ g).powerset, ∑ b' ∈ (pool \ g).powerset,
          if Disjoint a' b' then groupedTerm p hp hcop hg Ψ m (CompletedGauss.primaryGenerator f)
            (fun U => primeMarkInj slots lists a U * childLogTest W s₀ (primeProductNorm p U / Z ^ N'))
            SecondPassArithmetic.rowMajorant (Z ^ K') g a' b' else 0).re) ≤
      D f * Z ^ (-(N' + V)) * (∑ g ∈ pool.powerset, ∑ E ∈ g.powerset,
        Z ^ K' / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
          ∑ k ∈ (nonzeroChildFrequencyBall 1 (Z ^ Hc)).filter
            (fun k => physRow p (CompletedGauss.primaryGenerator f) g E k ∈
              nonzeroChildFrequencyBall 1 (Z ^ Hc)),
            ‖inner p hp hcop hg pool Ψ m (CompletedGauss.primaryGenerator f)
              (entryH p slots lists a W s₀ (Z ^ N')) SecondPassArithmetic.rowMajorant (Z ^ K')
              g E k‖) +
      D f * Z ^ (-(N' + V)) * (Z ^ K' * gSum ^ 2 * (‖paperRadialFourier SecondPassArithmetic.rowMajorant 0‖ + Ct) * SH) := by
    intro f hf
    have hf0 := hgen f hf
    have hdec := f_decomp p hp hcop hg hinj hc hpr pool Ψ m (CompletedGauss.primaryGenerator f) hf0
      (entryH p slots lists a W s₀ (Z ^ N')) SecondPassArithmetic.rowMajorant (Z ^ K') hY0
      (nonzeroChildFrequencyBall 1 (Z ^ Hc)) hball0
    simp only [mul_add, Finset.sum_add_distrib] at hdec
    -- the in-ball part
    have hin : ∑ g ∈ pool.powerset, ∑ E ∈ g.powerset.attach,
        Z ^ K' / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.1)‖ ^ 2 *
          ∑ k ∈ kIn p hp (CompletedGauss.primaryGenerator f) hf0 g E.1 (Finset.mem_powerset.mp E.2)
            (nonzeroChildFrequencyBall 1 (Z ^ Hc)),
            ‖inner p hp hcop hg pool Ψ m (CompletedGauss.primaryGenerator f)
              (entryH p slots lists a W s₀ (Z ^ N')) SecondPassArithmetic.rowMajorant (Z ^ K')
              g E.1 k‖ =
        ∑ g ∈ pool.powerset, ∑ E ∈ g.powerset,
        Z ^ K' / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
          ∑ k ∈ (nonzeroChildFrequencyBall 1 (Z ^ Hc)).filter
            (fun k => physRow p (CompletedGauss.primaryGenerator f) g E k ∈
              nonzeroChildFrequencyBall 1 (Z ^ Hc)),
            ‖inner p hp hcop hg pool Ψ m (CompletedGauss.primaryGenerator f)
              (entryH p slots lists a W s₀ (Z ^ N')) SecondPassArithmetic.rowMajorant (Z ^ K')
              g E k‖ :=
      Finset.sum_congr rfl fun g _ => inball_attach_eq p hp (CompletedGauss.primaryGenerator f)
        hf0 g (Z ^ Hc)
        (fun E k => ‖inner p hp hcop hg pool Ψ m (CompletedGauss.primaryGenerator f)
              (entryH p slots lists a W s₀ (Z ^ N')) SecondPassArithmetic.rowMajorant (Z ^ K')
              g E k‖)
        (fun E => Z ^ K' / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2)
    -- the diagonal
    have hdiag : ∑ g ∈ pool.powerset, Z ^ K' * ‖paperRadialFourier SecondPassArithmetic.rowMajorant 0‖ *
        ‖diagCoeff p hp hcop hg Ψ m (CompletedGauss.primaryGenerator f)
          (entryH p slots lists a W s₀ (Z ^ N')) g‖ ≤ Z ^ K' * ‖paperRadialFourier SecondPassArithmetic.rowMajorant 0‖ * gSum ^ 2 * SH := by
      calc _ ≤ ∑ g ∈ pool.powerset, Z ^ K' * ‖paperRadialFourier SecondPassArithmetic.rowMajorant 0‖ *
            (gSum ^ 2 * ‖entryH p slots lists a W s₀ (Z ^ N') g‖ ^ 2) :=
            Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_left
              (diagCoeff_norm_le p hp hcop hg hinj hc hpr Ψ hΨ m _ _ g)
              (mul_nonneg hY0.le (norm_nonneg _))
        _ = _ := by rw [hSH, Finset.mul_sum]; apply Finset.sum_congr rfl; intro g _; ring
    -- the tail
    have hs : ∀ g ∈ pool.powerset, ∀ E (hE : E ∈ g.powerset), ∀ a' ∈ (pool \ g).powerset,
        ∀ b' ∈ (pool \ g).powerset, Disjoint a' b' →
        bigGBound p hp hcop hg Ψ m (CompletedGauss.primaryGenerator f)
          (entryH p slots lists a W s₀ (Z ^ N')) g a' b' ≠ 0 →
        ∀ k ∈ {k : O | k ≠ 0 ∧ k ∉ kIn p hp (CompletedGauss.primaryGenerator f) hf0 g E
          (Finset.mem_powerset.mp hE) (nonzeroChildFrequencyBall 1 (Z ^ Hc))},
          Z ^ κ / max bo 1 ^ 2 ≤ Z ^ K' / kernelDen p E a' b' * ‖eisEmbedding k‖ ^ 2 := by
      intro g _ E hE a' ha' b' hb' hd hB0 k hk
      simp only [Set.mem_setOf_eq] at hk
      obtain ⟨hk0, hkin⟩ := hk
      have hEg := Finset.mem_powerset.mp hE
      have hbB := bigGBound_le p hp hcop hg hinj hc hpr Ψ hΨ m (CompletedGauss.primaryGenerator f)
        (entryH p slots lists a W s₀ (Z ^ N')) g a' b'
      have hb0 := bigGBound_nonneg p hp hcop hg Ψ m (CompletedGauss.primaryGenerator f)
        (entryH p slots lists a W s₀ (Z ^ N')) g a' b'
      have hHa : entryH p slots lists a W s₀ (Z ^ N') (g ∪ a') ≠ 0 := by
        intro h; apply hB0
        exact le_antisymm (by simpa [h] using hbB) hb0
      have hHb : entryH p slots lists a W s₀ (Z ^ N') (g ∪ b') ≠ 0 := by
        intro h; apply hB0
        exact le_antisymm (by simpa [h] using hbB) hb0
      have hga : Disjoint g a' := Finset.disjoint_of_subset_right (Finset.mem_powerset.mp ha')
        Finset.disjoint_sdiff
      have hgb : Disjoint g b' := Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hb')
        Finset.disjoint_sdiff
      have hla := entryH_live p slots lists a W s₀ (Z ^ N') (max bo 1) hX0 hWb _ hHa
      have hlb := entryH_live p slots lists a W s₀ (Z ^ N') (max bo 1) hX0 hWb _ hHb
      rw [FirstPassCubeLabels.primeProductNorm_union p g a' hga] at hla
      rw [FirstPassCubeLabels.primeProductNorm_union p g b' hgb] at hlb
      -- the physical row is outside the child ball
      have hy0 : physRow p (CompletedGauss.primaryGenerator f) g E k ≠ 0 := by
        unfold physRow
        exact mul_ne_zero (physRow_coeff_ne_zero p hp _ hf0 g E hEg) hk0
      have hyn : Z ^ Hc <
          ‖eisEmbedding (physRow p (CompletedGauss.primaryGenerator f) g E k)‖ ^ 2 := by
        by_contra hle
        push_neg at hle
        apply hkin
        rw [mem_kIn, mem_nonzeroChildFrequencyBall 1 one_ne_zero]
        simp only [one_mul]
        exact ⟨by have := one_le_eis_sq hy0; linarith, hle⟩
      have hrow := physRow_norm_sq p (CompletedGauss.primaryGenerator f) g E hEg k
      have hgc := gen_cofactor_norm p g E hEg
      have hfN : ‖eisEmbedding (CompletedGauss.primaryGenerator f)‖ ^ 2 ≤ Z ^ V := by
        rw [CompletedGauss.primaryGenerator_norm_sq f hf0]; exact (hlab f hf).2
      have hF0 : 0 ≤ ‖eisEmbedding (CompletedGauss.primaryGenerator f)‖ ^ 2 := by positivity
      have hkey : Z ^ K' * Z ^ Hc = Z ^ κ * (Z ^ V) ^ 2 * (Z ^ N') ^ 2 := by
        rw [hHc, ← Real.rpow_natCast (Z ^ V), ← Real.rpow_mul hZ0.le, ← Real.rpow_natCast (Z ^ N'),
          ← Real.rpow_mul hZ0.le, ← Real.rpow_add hZ0, ← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
        congr 1; push_cast; ring
      have hNa0' := FirstPassCubeLabels.primeProductNorm_pos p hp a'
      have hNb0' := FirstPassCubeLabels.primeProductNorm_pos p hp b'
      have hkd : kernelDen p E a' b' =
          ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
            (primeProductNorm p a' * primeProductNorm p b') := by
        unfold kernelDen
        rw [norm_eis_active p hp a' b' hd, mul_pow, Real.sq_sqrt hNa0'.le, Real.sq_sqrt hNb0'.le]
      rw [hkd]
      set e2 := ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 with he2
      set c2 := ‖eisEmbedding (cofactor p g E)‖ ^ 2 with hc2
      set k2 := ‖eisEmbedding k‖ ^ 2 with hk2
      set F2 := ‖eisEmbedding (CompletedGauss.primaryGenerator f)‖ ^ 2 with hF2
      set Ng := primeProductNorm p g with hNg
      set Na := primeProductNorm p a' with hNa
      set Nb := primeProductNorm p b' with hNb
      have he1 : 1 ≤ e2 := one_le_gen_norm_sq p hp E
      have hNg0 : 0 < Ng := FirstPassCubeLabels.primeProductNorm_pos p hp g
      have hNa0 : 0 < Na := FirstPassCubeLabels.primeProductNorm_pos p hp a'
      have hNb0 : 0 < Nb := FirstPassCubeLabels.primeProductNorm_pos p hp b'
      have hk20 : 0 ≤ k2 := by rw [hk2]; positivity
      -- `Z^Hc e2 ≤ (Z^V)² Ng² k2`
      have h1 : Z ^ Hc * e2 ≤ (Z ^ V) ^ 2 * Ng ^ 2 * k2 := by
        have hy2 : ‖eisEmbedding (physRow p (CompletedGauss.primaryGenerator f) g E k)‖ ^ 2 * e2 =
            F2 ^ 2 * Ng ^ 2 * k2 := by
          rw [hrow, ← hgc]; ring
        have hF : F2 ^ 2 ≤ (Z ^ V) ^ 2 := pow_le_pow_left₀ hF0 hfN 2
        calc Z ^ Hc * e2
            ≤ ‖eisEmbedding (physRow p (CompletedGauss.primaryGenerator f) g E k)‖ ^ 2 * e2 :=
              mul_le_mul_of_nonneg_right hyn.le (by linarith)
          _ = F2 ^ 2 * Ng ^ 2 * k2 := hy2
          _ ≤ (Z ^ V) ^ 2 * Ng ^ 2 * k2 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hF (by positivity)) hk20
      have hV2 : 0 < (Z ^ V) ^ 2 := pow_pos (Real.rpow_pos_of_pos hZ0 V) 2
      have h3 : (Z ^ V) ^ 2 * (Z ^ κ * (Z ^ N') ^ 2 * e2) ≤ (Z ^ V) ^ 2 * (Z ^ K' * Ng ^ 2 * k2) := by
        have := mul_le_mul_of_nonneg_left h1 hY0.le
        have e : Z ^ K' * (Z ^ Hc * e2) =
            (Z ^ K' * Z ^ Hc) * e2 := by ring
        rw [e, hkey] at this
        linarith
      have h4 := le_of_mul_le_mul_left h3 hV2
      have h2 : Ng ^ 2 * (Na * Nb) ≤ (max bo 1 * Z ^ N') ^ 2 := by
        calc Ng ^ 2 * (Na * Nb) = (Ng * Na) * (Ng * Nb) := by ring
          _ ≤ (max bo 1 * Z ^ N') * (max bo 1 * Z ^ N') :=
              mul_le_mul hla hlb (mul_pos hNg0 hNb0).le (by linarith)
          _ = _ := by ring
      have hκ0 : 0 ≤ Z ^ κ := (Real.rpow_pos_of_pos hZ0 _).le
      have h5 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hκ0 (by linarith : (0:ℝ) ≤ e2))
      have h6 := mul_le_mul_of_nonneg_left h4 (sq_nonneg (max bo 1))
      have hbl0 : 0 < max bo 1 ^ 2 := pow_pos (by linarith) 2
      rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos (by linarith) (mul_pos hNa0 hNb0)),
        div_mul_eq_mul_div, div_le_iff₀ hbl0]
      have hNg2 : 0 < Ng ^ 2 := pow_pos hNg0 2
      apply le_of_mul_le_mul_left _ hNg2
      nlinarith [h5, h6]
    have htail := tail_f_le p hp hcop hg hinj hc hpr pool Ψ hΨ m slots lists a W s₀ (Z ^ N') hX0
      (max bo 1) hΛ1 hWb SecondPassArithmetic.rowMajorant (Z ^ K') hY1
      (CompletedGauss.primaryGenerator f) hf0
      (nonzeroChildFrequencyBall 1 (Z ^ Hc)) (Z ^ κ / max bo 1 ^ 2)
      (div_nonneg (Real.rpow_pos_of_pos hZ0 _).le (by positivity)) Cw hCw At
      (fun K hK => hlat K _ hK (div_nonneg (Real.rpow_pos_of_pos hZ0 _).le (by positivity))) hs
    have htc := tail_const_le Cw (max bo 1) Z N' κ At hCw hbl1 hZ hN' (by linarith) hAt
    have htail' : ∑ g ∈ pool.powerset, ∑ E ∈ g.powerset.attach,
        Z ^ K' / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.1)‖ ^ 2 *
          ∑' k : {k : O | k ≠ 0 ∧ k ∉ kIn p hp (CompletedGauss.primaryGenerator f) hf0 g E.1
            (Finset.mem_powerset.mp E.2) (nonzeroChildFrequencyBall 1 (Z ^ Hc))},
            ‖inner p hp hcop hg pool Ψ m (CompletedGauss.primaryGenerator f)
              (entryH p slots lists a W s₀ (Z ^ N')) SecondPassArithmetic.rowMajorant (Z ^ K')
              g E.1 k‖ ≤ Z ^ K' * gSum ^ 2 * Ct * SH := by
      refine htail.trans ?_
      have hY0' : 0 ≤ Z ^ K' * gSum ^ 2 * SH := mul_nonneg (mul_nonneg hY0.le (sq_nonneg _)) hSH0
      calc Cw * (1 + (max bo 1 * Z ^ N') ^ 4) / (1 + Z ^ κ / max bo 1 ^ 2) ^ At * gSum ^ 2 *
            Z ^ K' * (max bo 1 * Z ^ N') * (128 * (max bo 1 * Z ^ N')) *
            (128 * (max bo 1 * Z ^ N') * SH)
          = (Cw * (1 + (max bo 1 * Z ^ N') ^ 4) / (1 + Z ^ κ / max bo 1 ^ 2) ^ At *
              (128 ^ 2 * (max bo 1 * Z ^ N') ^ 3)) * (Z ^ K' * gSum ^ 2 * SH) := by ring
        _ ≤ Ct * (Z ^ K' * gSum ^ 2 * SH) := mul_le_mul_of_nonneg_right htc hY0'
        _ = _ := by ring
    -- combine
    have hre := Complex.re_le_norm (∑ g ∈ pool.powerset, ∑ a' ∈ (pool \ g).powerset,
        ∑ b' ∈ (pool \ g).powerset,
          if Disjoint a' b' then groupedTerm p hp hcop hg Ψ m (CompletedGauss.primaryGenerator f)
            (fun U => primeMarkInj slots lists a U * childLogTest W s₀ (primeProductNorm p U / Z ^ N'))
            SecondPassArithmetic.rowMajorant (Z ^ K') g a' b' else 0)
    have htot := hre.trans hdec
    rw [hin] at htot
    have hfin : (∑ g ∈ pool.powerset, ∑ a' ∈ (pool \ g).powerset, ∑ b' ∈ (pool \ g).powerset,
          if Disjoint a' b' then groupedTerm p hp hcop hg Ψ m (CompletedGauss.primaryGenerator f)
            (fun U => primeMarkInj slots lists a U * childLogTest W s₀ (primeProductNorm p U / Z ^ N'))
            SecondPassArithmetic.rowMajorant (Z ^ K') g a' b' else 0).re ≤
        (∑ g ∈ pool.powerset, ∑ E ∈ g.powerset,
          Z ^ K' / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
            ∑ k ∈ (nonzeroChildFrequencyBall 1 (Z ^ Hc)).filter
              (fun k => physRow p (CompletedGauss.primaryGenerator f) g E k ∈
                nonzeroChildFrequencyBall 1 (Z ^ Hc)),
              ‖inner p hp hcop hg pool Ψ m (CompletedGauss.primaryGenerator f)
                (entryH p slots lists a W s₀ (Z ^ N')) SecondPassArithmetic.rowMajorant (Z ^ K')
                g E k‖) +
        Z ^ K' * gSum ^ 2 * (‖paperRadialFourier SecondPassArithmetic.rowMajorant 0‖ + Ct) * SH := by
      refine htot.trans ?_
      linarith [hdiag, htail']
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfin hcZ0) (hD0 f hf)
    linarith
  -- all labels
  have hsum := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib] at hsum
  have hE1 := selectedEnergy_le_grouped p hp hinj hcop hg hc hpr pool Ψ m slots lists a labels D W
    Z N' V K' s₀ hZ0 hD0
  -- in-ball
  have hHc4 : Hc ≤ 4 + κ := by rw [hHc]; linarith
  set fib := (Cd * (Z ^ Hc) ^ δ) ^ 3 with hfibdef
  have hfib0 : 0 ≤ fib := by
    have : 0 ≤ (Z ^ Hc) ^ δ := Real.rpow_nonneg (Real.rpow_pos_of_pos hZ0 _).le _
    exact pow_nonneg (mul_nonneg hCd0 this) 3
  have hfib : ∀ y : O, y ≠ 0 → ‖eisEmbedding y‖ ^ 2 ≤ Z ^ Hc →
      ((idealDivisors (Ideal.span {y})).card : ℝ) ^ 3 ≤ fib := by
    intro y hy0 hyZ
    have h1 := hCd (Ideal.span {y}) (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hy0)
    have h2 : (Ideal.absNorm (Ideal.span {y}) : ℝ) ≤ Z ^ Hc := by
      rw [← eisEmbedding_norm_sq_eq_absNorm_span]; exact hyZ
    have h3 : (Ideal.absNorm (Ideal.span {y}) : ℝ) ^ δ ≤ (Z ^ Hc) ^ δ :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) h2 hδ
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (h1.trans (mul_le_mul_of_nonneg_left h3 hCd0)) 3
  have hin := inball_le p hp hcop hg hinj hc hpr pool Ψ hΨ m slots lists a ha Kslots hslots labels
    hgen D Dmax hD hDmax W Φ bo (max bo 1) hbobl hWb b' hb' hΦ0 SecondPassArithmetic.rowMajorant
    d Cb hCb bf hbf Z (Z ^ N') (Z ^ K') (Z ^ (-(N' + V))) Hc B s₀ hX0 hY0 hcZ0 hΛ1 hB hchild
    fib hfib0 hfib
  -- the diagonal/tail sum over labels
  have hdt : ∑ f ∈ labels, D f * Z ^ (-(N' + V)) * (Z ^ K' * gSum ^ 2 * (‖paperRadialFourier SecondPassArithmetic.rowMajorant 0‖ + Ct) * SH) ≤
      (labels.card : ℝ) * Dmax * Z ^ (-(N' + V)) * (Z ^ K' * gSum ^ 2 * (‖paperRadialFourier SecondPassArithmetic.rowMajorant 0‖ + Ct) * SH) := by
    have hQ0 : 0 ≤ Z ^ (-(N' + V)) * (Z ^ K' * gSum ^ 2 * (‖paperRadialFourier SecondPassArithmetic.rowMajorant 0‖ + Ct) * SH) :=
      mul_nonneg hcZ0 (mul_nonneg (mul_nonneg (mul_nonneg hY0.le (sq_nonneg _))
        (add_nonneg (norm_nonneg _) hCt0)) hSH0)
    calc _ ≤ ∑ f ∈ labels, Dmax * Z ^ (-(N' + V)) * (Z ^ K' * gSum ^ 2 * (‖paperRadialFourier SecondPassArithmetic.rowMajorant 0‖ + Ct) * SH) := by
          apply Finset.sum_le_sum; intro f hf
          rw [mul_assoc, mul_assoc Dmax]
          exact mul_le_mul_of_nonneg_right (hD f hf).2 hQ0
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- the column mass
  have hSHc : SH = Z ^ N' * columnMass p pool slots lists a W Z N' := by
    rw [hSH]
    unfold columnMass
    rw [← mul_assoc, Real.rpow_neg hZ0.le, mul_inv_cancel₀ hX0.ne', one_mul]
    apply Finset.sum_congr rfl; intro U _
    rw [entryH_norm, mul_pow]
  -- numerics: in-ball
  set bl := max bo 1 with hbl
  set ℓ := 1 + Real.logb 2 (bl * Z ^ N') with hℓ
  have hlog0 : 0 ≤ Real.logb 2 (bl * Z ^ N') := Real.logb_nonneg (by norm_num) hΛ1
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; linarith
  have hLp : 1 + Real.logb 2 (2 * (bl * Z ^ N') ^ 2) = 2 * ℓ := by
    rw [logb_two_mul_sq _ (by linarith), hℓ]; ring
  have hI1 : (((Nat.floor (Real.logb 2 (bl * Z ^ N')) + 1 : ℕ)) : ℝ) ≤ ℓ := by
    push_cast; rw [hℓ]; linarith [Nat.floor_le hlog0]
  have hI10 : (0 : ℝ) ≤ (((Nat.floor (Real.logb 2 (bl * Z ^ N')) + 1 : ℕ)) : ℝ) := Nat.cast_nonneg _
  have hB1 : 0 ≤ ∫ τ : ℝ, ‖b' τ‖ := integral_nonneg fun τ => norm_nonneg _
  have hMb : 0 ≤ ∫ τ : ℝ, ‖b' τ‖ * (1 + ‖τ‖) ^ (2 * d) := integral_nonneg fun τ => by positivity
  have hpow : (2 : ℝ) ^ slots.card ≤ 2 ^ Kslots := pow_le_pow_right₀ (by norm_num) hslots
  have hkOne : kOne slots ((1 + Real.logb 2 (2 * (bl * Z ^ N') ^ 2)) ^ Kslots) b' ≤
      gSum * 2 ^ Kslots * (∫ τ : ℝ, ‖b' τ‖) / 2 * 4 ^ Kslots * ℓ ^ (2 * Kslots) := by
    unfold kOne
    have e : (∑ θ : RayCharacter, ‖gCoeff θ‖) = gSum := rfl
    rw [hLp, Finset.card_powerset, e]
    push_cast
    have hℓK : 0 ≤ (2 * ℓ) ^ Kslots := pow_nonneg (by linarith) _
    have h := mul_le_mul_of_nonneg_right hpow (mul_nonneg (mul_nonneg hℓK hℓK) hB1)
    have h' := mul_le_mul_of_nonneg_left h hG
    have h4 : (4 : ℝ) ^ Kslots = 2 ^ Kslots * 2 ^ Kslots := by rw [← mul_pow]; norm_num
    calc gSum * (2 ^ slots.card * (2 * ℓ) ^ Kslots) * (2 * ℓ) ^ Kslots * (∫ τ : ℝ, ‖b' τ‖) / 2
        = gSum * (2 ^ slots.card * ((2 * ℓ) ^ Kslots * (2 * ℓ) ^ Kslots *
            ∫ τ : ℝ, ‖b' τ‖)) / 2 := by ring
      _ ≤ gSum * (2 ^ Kslots * ((2 * ℓ) ^ Kslots * (2 * ℓ) ^ Kslots *
            ∫ τ : ℝ, ‖b' τ‖)) / 2 := div_le_div_of_nonneg_right h' (by norm_num)
      _ = _ := by rw [mul_pow, h4]; ring
  have hkOne0 : 0 ≤ kOne slots ((1 + Real.logb 2 (2 * (bl * Z ^ N') ^ 2)) ^ Kslots) b' := by
    unfold kOne
    have e : (∑ θ : RayCharacter, ‖gCoeff θ‖) = gSum := rfl
    rw [hLp, e]
    have hℓK : 0 ≤ (2 * ℓ) ^ Kslots := pow_nonneg (by linarith) _
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hG (mul_nonneg (Nat.cast_nonneg _) hℓK))
      hℓK) hB1) (by norm_num)
  have hharm : ∑ t' ∈ pool.powerset.filter (fun t' => primeProductNorm p t' ≤ 2 * bo * Z ^ N'),
      (primeProductNorm p t')⁻¹ ≤ 768 * ℓ := by
    have hsub : pool.powerset.filter (fun t' => primeProductNorm p t' ≤ 2 * bo * Z ^ N') ⊆
        pool.powerset.filter (fun t' => primeProductNorm p t' ≤ 2 * bl * Z ^ N') := by
      intro U hU
      rw [Finset.mem_filter] at hU ⊢
      refine ⟨hU.1, hU.2.trans ?_⟩
      have := mul_le_mul_of_nonneg_right hbobl hX0.le
      nlinarith
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun U _ _ =>
      inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp U).le).trans ?_
    refine (column_harmonic_le p hp hinj pool (2 * bl * Z ^ N') (by linarith)).trans ?_
    rw [mul_assoc, logb_two_mul' _ (by linarith)]
    rw [hℓ]; nlinarith
  have hP2 : ∑ t' ∈ pool.powerset.filter (fun t' => primeProductNorm p t' ≤ 2 * bo * Z ^ N'),
      kOne slots ((1 + Real.logb 2 (2 * (bl * Z ^ N') ^ 2)) ^ Kslots) b' / primeProductNorm p t' ≤
      gSum * 2 ^ Kslots * (∫ τ : ℝ, ‖b' τ‖) / 2 * 4 ^ Kslots * ℓ ^ (2 * Kslots) * (768 * ℓ) := by
    have hA0 : 0 ≤ gSum * 2 ^ Kslots * (∫ τ : ℝ, ‖b' τ‖) / 2 * 4 ^ Kslots * ℓ ^ (2 * Kslots) :=
      mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg hG (pow_nonneg (by norm_num) _))
        hB1) (by norm_num)) (pow_nonneg (by norm_num) _)) (pow_nonneg (by linarith) _)
    rw [show (∑ t' ∈ pool.powerset.filter (fun t' => primeProductNorm p t' ≤ 2 * bo * Z ^ N'),
        kOne slots ((1 + Real.logb 2 (2 * (bl * Z ^ N') ^ 2)) ^ Kslots) b' / primeProductNorm p t') =
        kOne slots ((1 + Real.logb 2 (2 * (bl * Z ^ N') ^ 2)) ^ Kslots) b' *
          ∑ t' ∈ pool.powerset.filter (fun t' => primeProductNorm p t' ≤ 2 * bo * Z ^ N'),
            (primeProductNorm p t')⁻¹ by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun U _ => div_eq_mul_inv _ _]
    exact mul_le_mul hkOne hharm (Finset.sum_nonneg fun U _ =>
      inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp U).le) hA0
  have hP20 : 0 ≤ ∑ t' ∈ pool.powerset.filter (fun t' => primeProductNorm p t' ≤ 2 * bo * Z ^ N'),
      kOne slots ((1 + Real.logb 2 (2 * (bl * Z ^ N') ^ 2)) ^ Kslots) b' / primeProductNorm p t' :=
    Finset.sum_nonneg fun U _ => div_nonneg hkOne0
      (FirstPassCubeLabels.primeProductNorm_pos p hp U).le
  have hP3 : ∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset, ‖gCoeff c.1‖ ≤
      2 ^ Kslots * gSum := by
    rw [Finset.sum_product]
    simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    have e : (∑ θ : RayCharacter, ‖gCoeff θ‖) = gSum := rfl
    rw [e]
    push_cast
    exact mul_le_mul_of_nonneg_right hpow gSum_nonneg
  have hP30 : 0 ≤ ∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset, ‖gCoeff c.1‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hℓn := ell_pow_le bl Z N' η (2 * Kslots + 2) hbl1 hZ hN' (by linarith) hη
  rw [← hℓ] at hℓn
  have hZε2 : Z ^ (2 * η * ((2 * Kslots + 2 : ℕ) : ℝ)) ≤ Z ^ (ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hZ hηε
  have hfibb : fib ≤ Cd ^ 3 * Z ^ (ε / 2) := by
    rw [hfibdef, mul_pow, ← Real.rpow_mul hZ0.le, ← Real.rpow_natCast (Z ^ (Hc * δ)) 3,
      ← Real.rpow_mul hZ0.le]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hCd0 3)
    apply Real.rpow_le_rpow_of_exponent_le hZ
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hHc4 hδ]
  have hcl0 : 0 ≤ ((1 + 1 / (η * Real.log 2)) * bl ^ η) ^ (2 * Kslots + 2) := by
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : 0 ≤ bl ^ η := Real.rpow_nonneg (by linarith) _
    have h2 : 0 ≤ 1 + 1 / (η * Real.log 2) :=
      add_nonneg zero_le_one (div_nonneg zero_le_one (mul_pos hη hl2).le)
    exact pow_nonneg (mul_nonneg h2 h1) _
  have hP2I : (∑ t' ∈ pool.powerset.filter (fun t' => primeProductNorm p t' ≤ 2 * bo * Z ^ N'),
      kOne slots ((1 + Real.logb 2 (2 * (bl * Z ^ N') ^ 2)) ^ Kslots) b' / primeProductNorm p t') *
      (((Nat.floor (Real.logb 2 (bl * Z ^ N')) + 1 : ℕ)) : ℝ) ≤
      (gSum * 2 ^ Kslots * (∫ τ : ℝ, ‖b' τ‖) / 2 * 4 ^ Kslots * 768 *
        ((1 + 1 / (η * Real.log 2)) * bl ^ η) ^ (2 * Kslots + 2)) * Z ^ (ε / 2) := by
    have hA0 : 0 ≤ gSum * 2 ^ Kslots * (∫ τ : ℝ, ‖b' τ‖) / 2 * 4 ^ Kslots * 768 :=
      mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg hG (pow_nonneg (by norm_num) _))
        hB1) (by norm_num)) (pow_nonneg (by norm_num) _)) (by norm_num)
    have hA1 : 0 ≤ gSum * 2 ^ Kslots * (∫ τ : ℝ, ‖b' τ‖) / 2 * 4 ^ Kslots * ℓ ^ (2 * Kslots) *
        (768 * ℓ) := by
      have := mul_nonneg hA0 (mul_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ ℓ) (2 * Kslots))
        (by linarith : (0:ℝ) ≤ ℓ))
      linarith [this]
    calc _ ≤ (gSum * 2 ^ Kslots * (∫ τ : ℝ, ‖b' τ‖) / 2 * 4 ^ Kslots * ℓ ^ (2 * Kslots) *
            (768 * ℓ)) * ℓ := mul_le_mul hP2 hI1 hI10 hA1
      _ = (gSum * 2 ^ Kslots * (∫ τ : ℝ, ‖b' τ‖) / 2 * 4 ^ Kslots * 768) *
            ℓ ^ (2 * Kslots + 2) := by ring
      _ ≤ (gSum * 2 ^ Kslots * (∫ τ : ℝ, ‖b' τ‖) / 2 * 4 ^ Kslots * 768) *
            (((1 + 1 / (η * Real.log 2)) * bl ^ η) ^ (2 * Kslots + 2) * Z ^ (ε / 2)) :=
          mul_le_mul_of_nonneg_left (hℓn.trans (mul_le_mul_of_nonneg_left hZε2 hcl0)) hA0
      _ = _ := by ring
  -- the exponents
  have hcY : Z ^ (-(N' + V)) * Z ^ K' = Z ^ (K' - N' - V) := by
    rw [← Real.rpow_add hZ0]; congr 1; ring
  have hcYX : Z ^ (-(N' + V)) * Z ^ K' * Z ^ N' = Z ^ (K' - V) := by
    rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0]; congr 1; ring
  have hεsplit : Z ^ (K' - N' - V + ε) = Z ^ (K' - N' - V) * (Z ^ (ε / 2) * Z ^ (ε / 2)) := by
    rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0]; congr 1; ring
  have hε1 : 1 ≤ Z ^ ε := Real.one_le_rpow hZ hε.le
  have hε2 : Z ^ (K' - V) ≤ Z ^ (K' + ε) * Z ^ (-V) := by
    rw [← Real.rpow_add hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hcIn0 := cIn_nonneg Kslots d b' Cb Cd η bl hCb hCd0 hη (by linarith)
  have hcDt0 := cDt_nonneg Cw bl At hCw (by linarith)
  have hs0 : 0 ≤ (1 + ‖s₀‖) ^ (2 * d) := by positivity
  have hcM0 : 0 ≤ columnMass p pool slots lists a W Z N' := by
    unfold columnMass
    exact mul_nonneg (Real.rpow_pos_of_pos hZ0 _).le
      (Finset.sum_nonneg fun _ _ => by positivity)
  -- in-ball total
  have hIN : ∑ f ∈ labels, D f * Z ^ (-(N' + V)) * (∑ g ∈ pool.powerset, ∑ E ∈ g.powerset,
        Z ^ K' / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
          ∑ k ∈ (nonzeroChildFrequencyBall 1 (Z ^ Hc)).filter
            (fun k => physRow p (CompletedGauss.primaryGenerator f) g E k ∈
              nonzeroChildFrequencyBall 1 (Z ^ Hc)),
            ‖inner p hp hcop hg pool Ψ m (CompletedGauss.primaryGenerator f)
              (entryH p slots lists a W s₀ (Z ^ N')) SecondPassArithmetic.rowMajorant (Z ^ K')
              g E k‖) ≤
      cIn Kslots d b' Cb Cd η bl * Z ^ (K' - N' - V + ε) * Dmax * (1 + ‖s₀‖) ^ (2 * d) * B := by
    refine hin.trans ?_
    rw [hεsplit]
    unfold cIn
    have hK0 : 0 ≤ Cb * crossMass * 2 * (∫ τ : ℝ, ‖b' τ‖ * (1 + ‖τ‖) ^ (2 * d)) * c2Int :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCb crossMass_nonneg) (by norm_num)) hMb)
        c2Int_nonneg
    have hQ0 : 0 ≤ Dmax * Z ^ (K' - N' - V) * B * (1 + ‖s₀‖) ^ (2 * d) :=
      mul_nonneg (mul_nonneg (mul_nonneg hDmax (Real.rpow_pos_of_pos hZ0 _).le) hB) hs0
    have hZe : 0 ≤ Z ^ (ε / 2) := (Real.rpow_pos_of_pos hZ0 _).le
    have hA2 : 0 ≤ gSum * 2 ^ Kslots * (∫ τ : ℝ, ‖b' τ‖) / 2 * 4 ^ Kslots * 768 *
        ((1 + 1 / (η * Real.log 2)) * bl ^ η) ^ (2 * Kslots + 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg hG
        (pow_nonneg (by norm_num) _)) hB1) (by norm_num)) (pow_nonneg (by norm_num) _))
        (by norm_num)) hcl0
    have hA3 : 0 ≤ (2 : ℝ) ^ Kslots * gSum := mul_nonneg (pow_nonneg (by norm_num) _) hG
    have e1 : (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) = crossMass := rfl
    have e2 : (∫ t : ℝ, (1 + ‖t‖) ^ (-(2 : ℝ))) = c2Int := rfl
    rw [e1, e2]
    calc _ = (Cb * crossMass * 2 * (∫ τ : ℝ, ‖b' τ‖ * (1 + ‖τ‖) ^ (2 * d)) * c2Int) *
          ((∑ t' ∈ pool.powerset.filter (fun t' => primeProductNorm p t' ≤ 2 * bo * Z ^ N'),
            kOne slots ((1 + Real.logb 2 (2 * (bl * Z ^ N') ^ 2)) ^ Kslots) b' /
              primeProductNorm p t') *
            (((Nat.floor (Real.logb 2 (bl * Z ^ N')) + 1 : ℕ)) : ℝ)) *
          (∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset, ‖gCoeff c.1‖) * fib *
          (Dmax * (Z ^ (-(N' + V)) * Z ^ K') * B * (1 + ‖s₀‖) ^ (2 * d)) := by ring
      _ ≤ (Cb * crossMass * 2 * (∫ τ : ℝ, ‖b' τ‖ * (1 + ‖τ‖) ^ (2 * d)) * c2Int) *
          ((gSum * 2 ^ Kslots * (∫ τ : ℝ, ‖b' τ‖) / 2 * 4 ^ Kslots * 768 *
            ((1 + 1 / (η * Real.log 2)) * bl ^ η) ^ (2 * Kslots + 2)) * Z ^ (ε / 2)) *
          (2 ^ Kslots * gSum) * (Cd ^ 3 * Z ^ (ε / 2)) *
          (Dmax * Z ^ (K' - N' - V) * B * (1 + ‖s₀‖) ^ (2 * d)) := by
          rw [hcY]
          apply mul_le_mul_of_nonneg_right _ hQ0
          apply mul_le_mul _ hfibb hfib0
            (mul_nonneg (mul_nonneg hK0 (mul_nonneg hA2 hZe)) hA3)
          apply mul_le_mul _ hP3 hP30 (mul_nonneg hK0 (mul_nonneg hA2 hZe))
          exact mul_le_mul_of_nonneg_left hP2I hK0
      _ = _ := by ring
  -- diagonal/tail total
  have hDT : (labels.card : ℝ) * Dmax * Z ^ (-(N' + V)) * (Z ^ K' * gSum ^ 2 * (‖paperRadialFourier SecondPassArithmetic.rowMajorant 0‖ + Ct) * SH) ≤
      cDt Cw bl At * Z ^ (K' + ε) * Dmax * (Z ^ (-V) * (labels.card : ℝ)) *
        columnMass p pool slots lists a W Z N' := by
    rw [hSHc]
    unfold cDt
    rw [← hCt]
    have hL0 : 0 ≤ (labels.card : ℝ) * Dmax * (gSum ^ 2 * (‖paperRadialFourier SecondPassArithmetic.rowMajorant 0‖ + Ct)) *
        columnMass p pool slots lists a W Z N' :=
      mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hDmax)
        (mul_nonneg (sq_nonneg _) (add_nonneg (norm_nonneg _) hCt0))) hcM0
    calc (labels.card : ℝ) * Dmax * Z ^ (-(N' + V)) *
          (Z ^ K' * gSum ^ 2 * (‖paperRadialFourier SecondPassArithmetic.rowMajorant 0‖ + Ct) * (Z ^ N' * columnMass p pool slots lists a W Z N'))
        = (Z ^ (-(N' + V)) * Z ^ K' * Z ^ N') * ((labels.card : ℝ) * Dmax * (gSum ^ 2 * (‖paperRadialFourier SecondPassArithmetic.rowMajorant 0‖ + Ct)) *
          columnMass p pool slots lists a W Z N') := by ring
      _ ≤ (Z ^ (K' + ε) * Z ^ (-V)) * ((labels.card : ℝ) * Dmax * (gSum ^ 2 * (‖paperRadialFourier SecondPassArithmetic.rowMajorant 0‖ + Ct)) *
          columnMass p pool slots lists a W Z N') := by
          rw [hcYX]; exact mul_le_mul_of_nonneg_right hε2 hL0
      _ = _ := by ring
  -- final
  have hZK : 0 ≤ Z ^ (K' - N' - V + ε) := (Real.rpow_pos_of_pos hZ0 _).le
  have hZK2 : 0 ≤ Z ^ (K' + ε) := (Real.rpow_pos_of_pos hZ0 _).le
  have hZV : 0 ≤ Z ^ (-V) := (Real.rpow_pos_of_pos hZ0 _).le
  calc selectedEnergy p hp hcop hg pool Ψ m slots lists a labels D W Z N' V K' s₀
      ≤ _ := hE1
    _ ≤ _ := hsum
    _ ≤ cIn Kslots d b' Cb Cd η bl * Z ^ (K' - N' - V + ε) * Dmax * (1 + ‖s₀‖) ^ (2 * d) * B +
        cDt Cw bl At * Z ^ (K' + ε) * Dmax * (Z ^ (-V) * (labels.card : ℝ)) *
          columnMass p pool slots lists a W Z N' := add_le_add hIN (hdt.trans hDT)
    _ ≤ _ := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_right _ hB
          apply mul_le_mul_of_nonneg_right _ hs0
          apply mul_le_mul_of_nonneg_right _ hDmax
          exact mul_le_mul_of_nonneg_right (by linarith) hZK
        · apply mul_le_mul_of_nonneg_right _ hcM0
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hZV (Nat.cast_nonneg _))
          apply mul_le_mul_of_nonneg_right _ hDmax
          exact mul_le_mul_of_nonneg_right (by linarith) hZK2


/-- **The second Poisson step**: `PoissonStepStatement`, with the child
profile family `![Φ]` (`Φ` a smooth bump `= 1` on `[ao/2, bo]`, support `⊆ [ao/4, 2 bo]`) and
output degree `= dchild`. -/
theorem poissonStepStatement : PoissonStepStatement := by
  intro Kslots W ao bo hao hab hsupp hWs
  obtain ⟨Φ, hΦs, hΦsupp, hΦ1, -, -⟩ := exists_profile_bump (ao / 2) bo (by linarith) (by linarith)
  have hΦsupp' : Function.support Φ ⊆ Set.Icc (ao / 4) (2 * bo) := by
    have e : ao / 2 / 2 = ao / 4 := by ring
    rw [e] at hΦsupp; exact hΦsupp
  have hΦ0 : ∀ x, 2 * bo < x → Φ x = 0 := by
    intro x hx
    by_contra h
    exact absurd (hΦsupp' h).2 (not_le.mpr hx)
  obtain ⟨b', hb'⟩ := profile_separation W hWs ao bo hao hsupp Φ hΦ1 hΦsupp'
  refine ⟨1, ![Φ], ao / 4, 2 * bo, by linarith, by linarith, ?_, ?_⟩
  · intro j
    fin_cases j
    exact ⟨hΦs, hΦsupp'⟩
  intro d
  refine ⟨d, ?_⟩
  intro ε κ hε hκ
  -- the window of the kernel separation
  have hWex : ∀ z : ℝ, W (Real.exp z) ≠ 0 → |z| ≤ max |Real.log ao| |Real.log bo| := by
    intro z hz
    have hm := hsupp hz
    have h1 : Real.log ao ≤ z := by
      have := Real.log_le_log hao hm.1; rwa [Real.log_exp] at this
    have h2 : z ≤ Real.log bo := by
      have := Real.log_le_log (Real.exp_pos z) hm.2; rwa [Real.log_exp] at this
    rw [abs_le]
    constructor
    · have := neg_abs_le (Real.log ao); have := le_max_left |Real.log ao| |Real.log bo|; linarith
    · have := le_abs_self (Real.log bo); have := le_max_right |Real.log ao| |Real.log bo|; linarith
  obtain ⟨Cb, hCb, hrad⟩ := radial_kernel_separation_pointwise SecondPassArithmetic.rowMajorant
    (![fun z => star (W (Real.exp z)), fun z => W (Real.exp z)] : Fin 2 → ℝ → ℂ)
    (fun _ => (-1 : ℝ)) (fun _ => max |Real.log ao| |Real.log bo|)
    (fun _ => le_max_of_le_left (abs_nonneg _))
    (by
      intro j z hz
      fin_cases j
      · exact hWex z (fun h => hz (by simp [h]))
      · exact hWex z (fun h => hz (by simp [h])))
    0 (2 * d + 2)
  choose! bf hbf using hrad
  have hbf' : ∀ R : ℝ, 0 < R → KernelSep SecondPassArithmetic.rowMajorant W R (bf R) ∧
      ∀ t : ℝ, (1 + ‖t‖) ^ (2 * d + 2) * ‖bf R t‖ ≤ Cb := by
    intro R hR
    refine ⟨(hbf R hR).1, fun t => ?_⟩
    have := (hbf R hR).2 t
    rw [pow_zero, one_mul] at this
    exact this
  -- the rapid lattice tail
  obtain ⟨sL, CL, hCL, hlatL⟩ :=
    EisensteinSchwartzPoisson.paperRadialFourier_lattice_tail (Nat.ceil (14 / κ))
  have hAt : 14 ≤ κ * ((Nat.ceil (14 / κ) : ℕ) : ℝ) := by
    have := Nat.le_ceil (14 / κ)
    rw [div_le_iff₀ hκ] at this; linarith
  have hCw : 0 ≤ CL * (sL.sup (schwartzSeminormFamily ℝ ℝ ℂ)) SecondPassArithmetic.rowMajorant :=
    mul_nonneg hCL.le (apply_nonneg _ _)
  -- the divisor bound
  have h4κ : (0 : ℝ) < 4 + κ := by linarith
  obtain ⟨Cd, hCd0, hCd⟩ :=
    IdealDivisorBound.ideal_divisor_small_power (ε / (6 * (4 + κ))) (by positivity)
  have hδε : 3 * (ε / (6 * (4 + κ)) * (4 + κ)) ≤ ε / 2 :=
    le_of_eq (by first | (field_simp; ring) | field_simp)
  have hn0 : (0 : ℝ) < ((2 * Kslots + 2 : ℕ) : ℝ) := by positivity
  have hη : 0 < ε / (4 * ((2 * Kslots + 2 : ℕ) : ℝ)) := div_pos hε (by positivity)
  have hηε : 2 * (ε / (4 * ((2 * Kslots + 2 : ℕ) : ℝ))) * ((2 * Kslots + 2 : ℕ) : ℝ) ≤ ε / 2 :=
    le_of_eq (by first | (field_simp; ring) | field_simp)
  have hbl0 : (0 : ℝ) ≤ max bo 1 := le_trans zero_le_one (le_max_right _ _)
  refine ⟨cIn Kslots d b' Cb Cd (ε / (4 * ((2 * Kslots + 2 : ℕ) : ℝ))) (max bo 1) +
      cDt (CL * (sL.sup (schwartzSeminormFamily ℝ ℝ ℂ)) SecondPassArithmetic.rowMajorant)
        (max bo 1) (Nat.ceil (14 / κ)) + 1, 1, ?_, le_rfl, ?_⟩
  · have := cIn_nonneg Kslots d b' Cb Cd _ (max bo 1) hCb hCd0.le hη hbl0
    have := cDt_nonneg (CL * (sL.sup (schwartzSeminormFamily ℝ ℝ ℂ)) SecondPassArithmetic.rowMajorant)
      (max bo 1) (Nat.ceil (14 / κ)) hCw hbl0
    linarith
  · intro Z hZ
    exact poisson_at Kslots W ao bo hao hab hsupp Φ hΦ0 b' hb' d Cb hCb bf hbf' ε κ hε hκ
      (Nat.ceil (14 / κ)) hAt _ hCw (fun K T hK hT => hlatL _ K T hK hT)
      (ε / (6 * (4 + κ))) Cd (by positivity) hδε hCd0.le hCd _ hη hηε Z hZ

end
end Qrh.MarkedAnchor.Inverse.Poisson

#print axioms Qrh.MarkedAnchor.Inverse.Poisson.poissonStepStatement
