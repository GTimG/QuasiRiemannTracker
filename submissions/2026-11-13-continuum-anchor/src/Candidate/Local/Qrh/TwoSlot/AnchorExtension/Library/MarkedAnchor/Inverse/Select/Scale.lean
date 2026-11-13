/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Select.AtScale

/-!
# Inverse.Select.Scale — the selection reduction at one scale (`selection_at_scale`)

See `Select/AtScale` for the plan. Here the pieces are assembled for one canonical datum, one
`HighLive` state and one scale `Z`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths OAI.SevenEighths.InverseMoment

local notation "O" => OAI.ActualEisensteinCubic.O

/-- Exponent bookkeeping of one Poisson call (pure arithmetic). -/
theorem selection_exponents (Pmax Smax u κ mesh κP N V Q z u' N' K' Hc' : ℝ) (hP : 0 ≤ Pmax)
    (hu : 0 ≤ u) (hκ : 0 < κ) (hdiag : Pmax+Smax+4*u+10*κ < 1) (hrad : 6*u+2*κ < 1)
    (hmeshκ : 5*mesh ≤ κ) (hκP : 0 ≤ κP) (hκP1 : κP ≤ 1)
    (hzS : z ≤ Smax+κ) (hNz : N - z ≤ Pmax+κ) (hFQ : N+V+Q ≤ Pmax+Smax+κ)
    (hQ : 0 ≤ Q) (hu'0 : 0 ≤ u') (hu'u : u' ≤ u) (hu'lo : u - 5*mesh ≤ u') (hu'z : u' ≤ z)
    (hN' : N' = N - u') (hK' : K' = 2*(N+V)-1+κ+4*u') (hHc' : Hc' = 2*(N'+V) - K' + κP) :
    Hc' = 1 - 6*u' - κ + κP ∧ 1-6*u-κ ≤ Hc' ∧ Hc' ≤ 2 ∧ K' ≤ N+V ∧
    N' - (z - u') ≤ (Pmax+2*κ)/(1-6*u-κ) * Hc' ∧
    z - u' ≤ (Smax-u+3*κ)/(1-6*u-κ) * Hc' ∧
    K' - N' - V + Hc' = N + V - u' + κP := by
  have hHlo : 0 < 1-6*u-κ := by linarith
  have hHc : Hc' = 1 - 6*u' - κ + κP := by rw [hHc', hN', hK']; ring
  have hHlo_le : 1-6*u-κ ≤ Hc' := by rw [hHc]; linarith
  refine ⟨hHc, hHlo_le, by rw [hHc]; linarith, by rw [hK']; linarith, ?_, ?_,
    by rw [hHc', hN', hK']; ring⟩
  · have h1 : Pmax + 2*κ ≤ (Pmax+2*κ)/(1-6*u-κ) * Hc' := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hHlo]
      have hP2 : 0 ≤ Pmax + 2*κ := by linarith
      nlinarith
    have : N' - (z - u') = N - z := by rw [hN']; ring
    rw [this]; linarith
  · have hSu : 0 ≤ Smax - u + 3*κ := by linarith
    have h1 : Smax - u + 3*κ ≤ (Smax-u+3*κ)/(1-6*u-κ) * Hc' := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hHlo]
      nlinarith
    linarith

/-- **The selection reduction at one scale.** -/
theorem selection_at_scale
    {ι σ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq σ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ActualEisensteinCubic.lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1)
    (Pmax Smax u κ mesh κP εP εR η : ℝ) (hP : 0 ≤ Pmax) (hu : 0 ≤ u)
    (hκ : 0 < κ) (hdiag : Pmax+Smax+4*u+10*κ < 1) (hrad : 6*u+2*κ < 1)
    (hmesh : 0 < mesh) (hmeshκ : 5*mesh ≤ κ) (hκP : 0 ≤ κP) (hκP1 : κP ≤ 1)
    (hεP : 0 ≤ εP) (hεR : 0 ≤ εR) (hη : 0 ≤ η)
    (K : ℕ) (Wc : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo) (hlh : lo ≤ hi)
    (hsW : Function.support Wc ⊆ Set.Icc lo hi)
    (Φ : ℝ → ℂ) (hΦn : ∀ y, ‖Φ y‖ ≤ 1) (boΦ : ℝ) (hbo : 0 < boΦ)
    (hΦs : Function.support Φ ⊆ Set.Icc (lo/2) boΦ)
    (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ r x h : ℝ, 1 ≤ 2^K * r → r ≤ 1 → 0 < x →
      Wc (r * x) * FourierBridge.logPhase h (Real.log (r * x)) =
        ∫ t : ℝ, FourierBridge.logPhase (t + h) (Real.log r) * childLogTest Φ (t + h) x * b t)
    {J : ℕ} (Φs : Fin J → ℝ → ℂ) (dchild degree : ℕ) (CP CR Cd : ℝ)
    (hCP : 0 ≤ CP) (hCR : 0 ≤ CR) (hCd : 1 ≤ Cd)
    (Z : ℝ) (hZ : 1 < Z) (hZm : (2:ℝ) ≤ Z^mesh) (hZhi : 2^K * hi ≤ Z^mesh) (hZbo : boΦ ≤ Z)
    (hPoisson : Poisson.PoissonStepAt K Φ boΦ Φs dchild degree εP κP CP Z)
    (hdiv : ∀ I : Ideal O, I ≠ ⊥ → (Ideal.absNorm I : ℝ) ≤ Z^4 →
      ((IdealMobiusDivisorSum.idealDivisors I).card : ℝ) ≤ Cd * Z^η)
    (slots : Finset σ) (hslots : slots.card ≤ K) (lists : σ → Finset ι) (H : σ → ℝ)
    (a : σ → ι → ℂ)
    (ha : ∀ i ∈ slots, ∀ P ∈ lists i, ‖a i P‖ ≤ 1)
    (hHr : ∀ i ∈ slots, 2 ≤ H i ∧ H i ≤ 2 * Z^mesh)
    (hPr : ∀ i ∈ slots, ∀ P ∈ lists i, H i / 2 ≤ FirstPassCubeLabels.primeProductNorm p {P} ∧
      FirstPassCubeLabels.primeProductNorm p {P} ≤ H i)
    (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (m : O)
    (hRestore : ∀ R' ⊆ slots, ∀ Xmax Hc' : ℝ, 0 < Xmax → Xmax ≤ Z^2 → 1-6*u-κ ≤ Hc' → Hc' ≤ 2 →
      Real.logb Z Xmax - Real.logb Z (∏ i ∈ slots \ R', H i) ≤
        ((Pmax+2*κ)/(1-6*u-κ)) * Hc' →
      Real.logb Z (∏ i ∈ slots \ R', H i) ≤ ((Smax-u+3*κ)/(1-6*u-κ)) * Hc' →
      ChildBoundInj p hg Finset.univ Ψ m (slots \ R') lists a Φs dchild Z Xmax
        (2*boΦ*Xmax) Hc' (CR * Z^(Hc'*(1+u/(1-6*u-κ)) + εR)))
    (N V M Q : ℝ) (hN : 0 ≤ N) (hV : 0 ≤ V) (hM : 0 ≤ M) (hQ : 0 ≤ Q)
    (ss : Finset σ) (hss : ss ⊆ slots)
    (hGood : HighLive Pmax Smax κ u N V M Q (Real.logb Z (∏ i ∈ ss, H i)))
    (labels : Finset (Ideal O)) (hlab : ∀ I ∈ labels, I ≠ ⊥ ∧ CompletedGauss.primaryGenerator I ≠ 0 ∧
      (Ideal.absNorm I : ℝ) ≤ Z^V)
    (s : ℝ) :
    columnEnergyInj p hp hcop hg Finset.univ Ψ m ss lists a
        labels (nonzeroChildFrequencyBall 1 (Z^M)) (secondLabelWeight K) (childLogTest Wc s)
        (Z^N) Z (N+V) ≤
      selConst (∫ t, ‖b t‖ * (1 + ‖t‖)^degree) CP CR Cd boΦ K *
        Z^(N+V+selExcess (u/(1-6*u-κ)) mesh κP εP εR η K) * (1 + ‖s‖)^(2*degree) := by
  have hZ0 : 0 < Z := by linarith
  have hZ1 : 1 ≤ Z := hZ.le
  set x := u/(1-6*u-κ) with hx
  have hHlo : 0 < 1-6*u-κ := by linarith
  have hx0 : 0 ≤ x := div_nonneg hu hHlo.le
  have hxH : x * (1-6*u-κ) = u := by rw [hx, div_mul_cancel₀ _ hHlo.ne']
  set Ib := ∫ t, ‖b t‖ * (1 + ‖t‖)^degree with hIbdef
  have hCd0 : 0 ≤ Cd := by linarith
  set e := selExcess x mesh κP εP εR η K with he
  have hRHS0 : 0 ≤ selConst Ib CP CR Cd boΦ K * Z^(N+V+e) * (1 + ‖s‖)^(2*degree) := by
    unfold selConst; positivity
  obtain ⟨⟨hz0, hzS, hNz, hFQ, hM0⟩, huz⟩ := hGood
  set z := Real.logb Z (∏ i ∈ ss, H i) with hzdef
  have hHss : ∀ i ∈ ss, 2 ≤ H i ∧ H i ≤ 2 * Z^mesh := fun i hi => hHr i (hss hi)
  have hPss : ∀ i ∈ ss, ∀ P ∈ lists i, H i / 2 ≤ FirstPassCubeLabels.primeProductNorm p {P} ∧
      FirstPassCubeLabels.primeProductNorm p {P} ≤ H i := fun i hi => hPr i (hss hi)
  have hprod_pos : ∀ R ⊆ ss, 0 < ∏ i ∈ R, H i := fun R hR =>
    Finset.prod_pos (fun i hi => by linarith [(hHss i (hR hi)).1])
  have hcard_ss : ss.card ≤ K := (Finset.card_le_card hss).trans hslots
  -- rows vanish unless `z ≤ N + mesh`
  by_cases hvan : 2^ss.card * hi * Z^N < ∏ i ∈ ss, H i
  · rw [energy_eq_zero p hp hcop hg _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun f k => rows_vanish p hp hcop hg Finset.univ Ψ m ss lists a H hPss Wc lo hi hsW
        s (Z^N) (Real.rpow_pos_of_pos hZ0 _) hvan f k)]
    exact hRHS0
  push_neg at hvan
  have hhi0 : 0 ≤ hi := by linarith
  have hzN : z ≤ N + mesh := by
    have h1 : ∏ i ∈ ss, H i ≤ Z^(N+mesh) := by
      calc ∏ i ∈ ss, H i ≤ 2^ss.card * hi * Z^N := hvan
        _ ≤ 2^K * hi * Z^N := by
            have : (2:ℝ)^ss.card ≤ 2^K := pow_le_pow_right₀ (by norm_num) hcard_ss
            have := Real.rpow_nonneg hZ0.le N
            gcongr
        _ ≤ Z^mesh * Z^N := by
            have := Real.rpow_nonneg hZ0.le N
            gcongr
        _ = Z^(N+mesh) := by rw [← Real.rpow_add hZ0]; ring_nf
    exact (Real.logb_le_iff_le_rpow hZ (hprod_pos ss le_rfl)).mpr h1
  -- whole-slot selection
  set w : σ → ℝ := fun i => Real.logb Z (H i) with hwdef
  have hw0 : ∀ i ∈ ss, 0 ≤ w i := fun i hi =>
    Real.logb_nonneg hZ (by linarith [(hHss i hi).1])
  have hwm : ∀ i ∈ ss, w i ≤ 2*mesh := by
    intro i hi
    apply (Real.logb_le_iff_le_rpow hZ (by linarith [(hHss i hi).1])).mpr
    calc H i ≤ 2 * Z^mesh := (hHss i hi).2
      _ ≤ Z^mesh * Z^mesh := by
          have := Real.rpow_nonneg hZ0.le mesh
          gcongr
      _ = Z^(2*mesh) := by rw [← Real.rpow_add hZ0]; ring_nf
  have hzsum : z = ∑ i ∈ ss, w i :=
    logb_prod_eq_sum ss H (fun i hi => by linarith [(hHss i hi).1]) Z
  set u₁ := max 0 (u - 3*mesh) with hu₁
  have hu₁u : u₁ ≤ u := max_le hu (by linarith)
  obtain ⟨R, hRss, hR1, hR2⟩ := live_selection w (2*mesh) (by linarith) ss hw0 hwm u₁
    (le_max_left _ _) (by rw [← hzsum]; linarith)
  set T := ∏ i ∈ R, H i with hTdef
  have hT : 0 < T := hprod_pos R hRss
  set u' := Real.logb Z T with hu'def
  have hu'sum : u' = ∑ i ∈ R, w i :=
    logb_prod_eq_sum R H (fun i hi => by linarith [(hHss i (hRss hi)).1]) Z
  have hZu' : Z^u' = T := Real.rpow_logb hZ0 hZ.ne' hT
  have hu'0 : 0 ≤ u' := by
    rw [hu'sum]; exact Finset.sum_nonneg (fun i hi => hw0 i (hRss hi))
  have hu'u : u' ≤ u := by rw [hu'sum]; linarith
  have hu'lo : u - 5*mesh ≤ u' := by
    rw [hu'sum]; have := le_max_right 0 (u - 3*mesh); linarith
  have hu'z : u' ≤ z := by
    rw [hu'sum, hzsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hRss (fun i hi _ => hw0 i hi)
  have hNu' : 0 ≤ N - u' := by
    have : u₁ ≤ N := max_le hN (by linarith)
    rw [hu'sum]; linarith
  obtain ⟨N', hN'def⟩ : ∃ N', N' = N - u' := ⟨_, rfl⟩
  obtain ⟨K', hK'def⟩ : ∃ K', K' = 2*(N+V)-1+κ+4*u' := ⟨_, rfl⟩
  obtain ⟨Hc', hHc'def⟩ : ∃ Hc', Hc' = 2*(N'+V) - K' + κP := ⟨_, rfl⟩
  obtain ⟨hHc, hHlo_le, hHc2, hK'F, hgeoP, hgeoS, hexpo⟩ :=
    selection_exponents Pmax Smax u κ mesh κP N V Q z u' N' K' Hc' hP hu hκ hdiag hrad hmeshκ
      hκP hκP1 hzS hNz hFQ hQ hu'0 hu'u hu'lo hu'z hN'def hK'def hHc'def
  have hN'0 : 0 ≤ N' := by rw [hN'def]; exact hNu'
  have hF1 : N + V < 1 := by linarith
  have hK'0 : 0 ≤ K' := by rw [hK'def]; linarith
  -- enlarge the Gauss ball to `M₀ = 2F-1+κ`
  have hDw0 : ∀ f ∈ labels, 0 ≤ secondLabelWeight K f := fun f _ => by
    unfold secondLabelWeight; positivity
  have hball : nonzeroChildFrequencyBall 1 (Z^M) ⊆
      nonzeroChildFrequencyBall 1 (Z^(2*(N+V)-1+κ)) :=
    ball_mono _ _ (Real.rpow_le_rpow_of_exponent_le hZ1 hM0)
  have hmono := energy_rows_mono p hp hcop hg Finset.univ Ψ m ss lists a labels _ _ hball
    (secondLabelWeight K) hDw0 (childLogTest Wc s) (Z^N) Z (N+V)
  refine hmono.trans ?_
  -- residual coefficients for the Poisson step
  obtain ⟨a', ha'def⟩ : ∃ a' : σ → ι → ℂ,
      a' = fun i P => if i ∈ slots ∧ P ∈ lists i then a i P else 0 := ⟨_, rfl⟩
  have ha'eq : ∀ i ∈ slots, ∀ P ∈ lists i, a' i P = a i P := fun i hi P hP => by
    rw [ha'def]; simp only [hi, hP, and_self, ite_true]
  have ha'n : ∀ i j, ‖a' i j‖ ≤ 1 := by
    intro i j
    rw [ha'def]
    dsimp only
    split_ifs with h
    · exact ha i h.1 j h.2
    · simp
  have hRsub : ss \ R ⊆ slots := Finset.sdiff_subset.trans hss
  -- the constants of one Poisson call
  obtain ⟨Dmax, hDmax⟩ : ∃ D : ℝ, D = (Cd * Z^η)^(9+4*K) := ⟨_, rfl⟩
  obtain ⟨Bc, hBc⟩ : ∃ B : ℝ, B = CR * Z^(Hc'*(1+x)+εR) := ⟨_, rfl⟩
  obtain ⟨colM, hcolM⟩ : ∃ c : ℝ, c = Poisson.columnMass p Finset.univ (ss \ R) lists a' Φ Z N' :=
    ⟨_, rfl⟩
  obtain ⟨Lc, hLc⟩ : ∃ c : ℝ, c = Z^(-V) * (labels.card : ℝ) := ⟨_, rfl⟩
  have hcolM0 : 0 ≤ colM := by
    rw [hcolM]; unfold Poisson.columnMass
    exact mul_nonneg (Real.rpow_nonneg hZ0.le _) (Finset.sum_nonneg (fun _ _ => by positivity))
  have hLc0 : 0 ≤ Lc := by rw [hLc]; positivity
  have hDmax0 : 0 ≤ Dmax := by rw [hDmax]; positivity
  have hBc0 : 0 ≤ Bc := by rw [hBc]; positivity
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = Z^(-u') * (CP * Z^(K'-N'-V+εP) * Dmax * Bc +
      CP * Z^(K'+εP) * Dmax * Lc * colM) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    have := Real.rpow_nonneg hZ0.le (-u')
    have := Real.rpow_nonneg hZ0.le (K'-N'-V+εP)
    have := Real.rpow_nonneg hZ0.le (K'+εP)
    positivity
  -- the restored child bound on the residual slots `ss \ R`
  have hR'sub : R ∪ (slots \ ss) ⊆ slots :=
    Finset.union_subset (hRss.trans hss) Finset.sdiff_subset
  have hres : slots \ (R ∪ (slots \ ss)) = ss \ R := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_union, not_or, not_and, not_not]
    constructor
    · rintro ⟨hi, hnR, hss'⟩
      exact ⟨hss' hi, hnR⟩
    · rintro ⟨hi, hnR⟩
      exact ⟨hss hi, hnR, fun _ => hi⟩
  have hlogN' : Real.logb Z (Z^N') = N' := Real.logb_rpow hZ0 hZ.ne'
  have hlogres : Real.logb Z (∏ i ∈ ss \ R, H i) = z - u' := by
    have hsplit : (∏ i ∈ ss \ R, H i) * T = ∏ i ∈ ss, H i := Finset.prod_sdiff hRss
    have hpos : 0 < ∏ i ∈ ss \ R, H i := hprod_pos _ Finset.sdiff_subset
    rw [hzdef, hu'def, ← hsplit, Real.logb_mul hpos.ne' hT.ne']
    ring
  have hXmax2 : Z^N' ≤ Z^2 := by
    have h1 : Z^N' ≤ Z^(2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by rw [hN'def]; linarith)
    have h2 : Z^(2:ℝ) = Z^2 := by norm_cast
    rwa [h2] at h1
  have hCB := hRestore (R ∪ (slots \ ss)) hR'sub (Z^N') Hc' (Real.rpow_pos_of_pos hZ0 _)
    hXmax2 hHlo_le hHc2 (by rw [hres, hlogN', hlogres]; exact hgeoP) (by rw [hres, hlogres]; exact hgeoS)
  rw [hres, ← hBc] at hCB
  have hCB' : ChildBoundInj p hg Finset.univ Ψ m (ss \ R) lists a' Φs dchild Z (Z^N')
      (2*boΦ*Z^N') (2*(N'+V)-K'+κP) Bc := by
    have h := childBound_congr p hg Finset.univ Ψ m (ss \ R) lists a a'
      (fun i hi P hP => ha'eq i (hRsub hi) P hP) Φs dchild Z (Z^N') (2*boΦ*Z^N') Hc' Bc hCB
    rwa [hHc'def] at h
  -- one Poisson call per height
  have hlabD : ∀ f ∈ labels, 0 ≤ secondLabelWeight K f ∧ secondLabelWeight K f ≤ Dmax := by
    intro f hf
    refine ⟨hDw0 f hf, ?_⟩
    rw [hDmax]
    unfold secondLabelWeight
    have hZV : Z^V ≤ Z^(4:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
    have h4 : Z^(4:ℝ) = Z^4 := by norm_cast
    have hd := hdiv f (hlab f hf).1 (by rw [← h4]; linarith [(hlab f hf).2.2])
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hd _
  have hstep := fun h : ℝ => hPoisson p hp hinj hcop hg hc hpr Finset.univ Ψ m (ss \ R) lists a'
    labels (secondLabelWeight K) Dmax N' V K' hΨ
    ((Finset.card_le_card hRsub).trans hslots) ha'n
    (fun f hf => (hlab f hf).2) hlabD hDmax0 hN'0 hV hK'0 (by rw [hN'def]; linarith)
    (by linarith) Bc hBc0 hCB' h
  have hXT : Z^N / T = Z^N' := by rw [← hZu', ← Real.rpow_sub hZ0, hN'def]
  have hA : ∀ h : ℝ, columnEnergyInj p hp hcop hg
      Finset.univ Ψ m (ss \ R) lists a labels (nonzeroChildFrequencyBall 1 (Z^K'))
      (secondLabelWeight K) (childLogTest Φ h) (Z^N / T) Z (N+V) ≤ A * (1 + ‖h‖)^(2*degree) := by
    intro h
    rw [hXT, energy_renormalize p hp hcop hg _ _ _ _ _ _ _ _ _ _ _ Z (N+V) (N'+V) hZ0,
      ← energy_congr p hp hcop hg Finset.univ Ψ m (ss \ R) lists a a'
        (fun i hi P hP => ha'eq i (hRsub hi) P hP)]
    have hP' := hstep h
    unfold Poisson.selectedEnergy at hP'
    rw [← hcolM, ← hLc] at hP'
    have hexp : (N'+V) - (N+V) = -u' := by rw [hN'def]; ring
    rw [hexp]
    have hpow1 : 1 ≤ (1 + ‖h‖)^(2*degree) := one_le_pow₀ (by linarith [norm_nonneg h])
    have hX2 : 0 ≤ CP * Z^(K'+εP) * Dmax * Lc * colM := by
      have := Real.rpow_nonneg hZ0.le (K'+εP)
      positivity
    have hZu0 : 0 ≤ Z^(-u') := Real.rpow_nonneg hZ0.le _
    have h2 := le_mul_of_one_le_right hX2 hpow1
    have h3 : CP * Z^(K'-N'-V+εP) * Dmax * (1 + ‖h‖)^(2*degree) * Bc =
        (CP * Z^(K'-N'-V+εP) * Dmax * Bc) * (1 + ‖h‖)^(2*degree) := by ring
    calc Z^(-u') * columnEnergyInj p hp hcop hg Finset.univ
          Ψ m (ss \ R) lists a' labels (nonzeroChildFrequencyBall 1 (Z^K')) (secondLabelWeight K)
          (childLogTest Φ h) (Z^N') Z (N'+V)
        ≤ Z^(-u') * (CP * Z^(K'-N'-V+εP) * Dmax * (1 + ‖h‖)^(2*degree) * Bc +
            CP * Z^(K'+εP) * Dmax * Lc * colM) :=
          mul_le_mul_of_nonneg_left hP' hZu0
      _ ≤ Z^(-u') * ((CP * Z^(K'-N'-V+εP) * Dmax * Bc) * (1 + ‖h‖)^(2*degree) +
            (CP * Z^(K'+εP) * Dmax * Lc * colM) * (1 + ‖h‖)^(2*degree)) := by
          apply mul_le_mul_of_nonneg_left _ hZu0
          linarith
      _ = A * (1 + ‖h‖)^(2*degree) := by rw [hAdef]; ring
  -- separation and central Cauchy (`selected_energy_bound`)
  have hcardR : R.card ≤ K := (Finset.card_le_card hRss).trans hcard_ss
  have hPR : ∀ i ∈ R, ∀ P ∈ lists i, H i / 2 ≤ FirstPassCubeLabels.primeProductNorm p {P} ∧
      FirstPassCubeLabels.primeProductNorm p {P} ≤ H i := fun i hi => hPss i (hRss hi)
  have hNd : ∀ d ∈ injPi R lists,
      1 ≤ 2^K * (FirstPassCubeLabels.primeProductNorm p (tupleImage R d) / T) ∧
      FirstPassCubeLabels.primeProductNorm p (tupleImage R d) / T ≤ 1 := by
    intro d hd
    obtain ⟨hlo', hup'⟩ := tuple_norm_bounds p R lists H hPR d hd
    have h2R : (0:ℝ) < 2^R.card := by positivity
    have h2K : (2:ℝ)^R.card ≤ 2^K := pow_le_pow_right₀ (by norm_num) hcardR
    refine ⟨?_, (div_le_one hT).mpr hup'⟩
    rw [div_le_iff₀ h2R] at hlo'
    rw [← mul_div_assoc, le_div_iff₀ hT]
    have hNd0 : 0 ≤ FirstPassCubeLabels.primeProductNorm p (tupleImage R d) := by
      unfold FirstPassCubeLabels.primeProductNorm; positivity
    have := mul_le_mul_of_nonneg_left h2K hNd0
    linarith
  have hmap : ∀ d ∈ injPi R lists, ∀ k ∈ nonzeroChildFrequencyBall 1 (Z^(2*(N+V)-1+κ)),
      k * (∏ i ∈ tupleImage R d, p i)^4 ∈ nonzeroChildFrequencyBall 1 (Z^K') := by
    intro d hd k hk
    rw [mem_nonzeroChildFrequencyBall 1 one_ne_zero, one_mul] at hk ⊢
    have hNdT := (tuple_norm_bounds p R lists H hPR d hd).2
    have hNd0 : 0 < FirstPassCubeLabels.primeProductNorm p (tupleImage R d) :=
      FirstPassCubeLabels.primeProductNorm_pos p hp _
    have heq : ‖ConcreteTraceCRT.eisEmbedding (k * (∏ i ∈ tupleImage R d, p i)^4)‖^2 =
        ‖ConcreteTraceCRT.eisEmbedding k‖^2 *
          (FirstPassCubeLabels.primeProductNorm p (tupleImage R d))^4 := by
      rw [eis_norm_sq_mul, eis_norm_sq_pow]; rfl
    rw [heq]
    refine ⟨mul_pos hk.1 (pow_pos hNd0 4), ?_⟩
    have hT4 : T^4 = Z^(4*u') := by
      rw [← hZu', ← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]; ring_nf
    calc ‖ConcreteTraceCRT.eisEmbedding k‖^2 *
          (FirstPassCubeLabels.primeProductNorm p (tupleImage R d))^4
        ≤ Z^(2*(N+V)-1+κ) * T^4 := by gcongr; exact hk.2
      _ = Z^K' := by rw [hT4, ← Real.rpow_add hZ0, hK'def]
  obtain ⟨mult, hmultdef⟩ : ∃ n : ℕ, n = K^K * ⌊Cd * Z^η⌋₊ := ⟨_, rfl⟩
  have hmult : ∀ k' ∈ nonzeroChildFrequencyBall 1 (Z^K'), ((injPi R lists ×ˢ
      nonzeroChildFrequencyBall 1 (Z^(2*(N+V)-1+κ))).filter
      (fun x => x.2 * (∏ i ∈ tupleImage R x.1, p i)^4 = k')).card ≤ mult := by
    intro k' hk'
    rw [mem_nonzeroChildFrequencyBall 1 one_ne_zero, one_mul] at hk'
    have hk'0 : k' ≠ 0 := by
      intro h; rw [h, map_zero, norm_zero] at hk'; norm_num at hk'
    rw [hmultdef]
    refine (tuple_fiber_card_le p hp hinj R lists _ k' hk'0).trans
      (Nat.mul_le_mul (pow_self_le_pow_self hcardR) ?_)
    apply Nat.le_floor
    apply hdiv
    · rw [Ne, Ideal.span_singleton_eq_bot]; exact hk'0
    · rw [← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
      refine hk'.2.trans ?_
      calc Z^K' ≤ Z^(4:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
        _ = Z^4 := by norm_cast
  have hE := selected_energy_bound p hp hcop hg hpr hc Finset.univ Ψ hΨ m ss R hRss lists a
    (fun i _ => Finset.subset_univ _) Wc Φ b K hsep T (Z^N) hT
    (Real.rpow_pos_of_pos hZ0 _) hNd labels (secondLabelWeight K) hDw0 _ _ hmap mult hmult Z
    (N+V) A degree hA0 hA s
  refine hE.trans ?_
  -- numerics
  obtain ⟨mass, hmassdef⟩ : ∃ c : ℝ,
      c = ∑ d ∈ injPi R lists, ‖∏ i ∈ R.attach, a i.1 (d i.1 i.2)‖^2 := ⟨_, rfl⟩
  rw [← hmassdef]
  have hmass : mass ≤ 128^K * T := by
    have h1 := mass_le p hp hinj R lists a H (fun i hi => ha i (hss (hRss hi)))
      (fun i hi => by linarith [(hHss i (hRss hi)).1]) (fun i hi P hP => (hPR i hi P hP).2)
    rw [hmassdef]
    calc _ ≤ 128^R.card * T := h1
      _ ≤ 128^K * T := by
          have : (128:ℝ)^R.card ≤ 128^K := pow_le_pow_right₀ (by norm_num) hcardR
          exact mul_le_mul_of_nonneg_right this hT.le
  have hmult' : (mult : ℝ) ≤ (K:ℝ)^K * (Cd * Z^η) := by
    rw [hmultdef]
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by positivity)
  have hLc' : Lc ≤ 128 := by
    rw [hLc]
    have hZV1 : 1 ≤ Z^V := Real.one_le_rpow hZ1 hV
    have hcnt := DescentFiberCost.finite_ideal_count_real labels (Z^V) hZV1
      (fun I hI => (hlab I hI).1) (fun I hI => (hlab I hI).2.2)
    rw [Real.rpow_neg hZ0.le]
    have hZVp : 0 < Z^V := by positivity
    calc (Z^V)⁻¹ * (labels.card : ℝ) ≤ (Z^V)⁻¹ * (128 * Z^V) :=
          mul_le_mul_of_nonneg_left hcnt (by positivity)
      _ = 128 := by field_simp
  have hcolM' : colM ≤ 128 * (1 + boΦ) * (Cd * Z^η)^(2*K) := by
    rw [hcolM]
    refine colMass_le p hp hinj (ss \ R) lists a' K ((Finset.card_le_card hRsub).trans hslots)
      (fun i _ P _ => ha'n i P) Φ hΦn (lo/2) boΦ hbo.le hΦs Z N' Cd η hZ1 hN'0 hCd hη ?_ hdiv
    have hZN' : Z^N' ≤ Z^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ1 (by rw [hN'def]; linarith)
    have hZN0 := Real.rpow_nonneg hZ0.le N'
    calc boΦ * Z^N' ≤ Z * Z^(1:ℝ) := mul_le_mul hZbo hZN' hZN0 (by linarith)
      _ ≤ Z^4 := by
          rw [Real.rpow_one]
          have h3 : 1 ≤ Z^2 := one_le_pow₀ hZ1
          calc Z * Z ≤ Z * Z * Z^2 := le_mul_of_one_le_right (by positivity) h3
            _ = Z^4 := by ring
  have hTinv : T * Z^(-u') = 1 := by
    rw [Real.rpow_neg hZ0.le, hZu', mul_inv_cancel₀ hT.ne']
  -- the two exponents
  have hxHc : x * Hc' ≤ u + x * (30*mesh + κP) := by
    rw [hHc]
    have h6 : 6*(u-u') ≤ 30*mesh := by linarith
    have h7 := mul_le_mul_of_nonneg_left h6 hx0
    have e1 : x*(1-6*u'-κ+κP) = x*(1-6*u-κ) + x*(6*(u-u')) + x*κP := by ring
    have e2 : x*(30*mesh+κP) = x*(30*mesh) + x*κP := by ring
    linarith
  have he_def : e = 5*mesh + x*(30*mesh+κP) + κP + εP + εR + (10+6*(K:ℝ))*η := by
    rw [he]; unfold selExcess; push_cast; ring
  have hB1 : (Z^η)^(10+4*K) * (Z^(K'-N'-V+εP) * Z^(Hc'*(1+x)+εR)) ≤ Z^(N+V+e) := by
    rw [← Real.rpow_add hZ0]
    apply rpow_pow_mul_le Z η _ _ (10+4*K) hZ1
    have e2 : Hc' * (1 + x) = Hc' + x * Hc' := by ring
    rw [he_def]
    push_cast
    have hK0 : (0:ℝ) ≤ K := Nat.cast_nonneg K
    have hηK : (10+4*(K:ℝ))*η ≤ (10+6*(K:ℝ))*η :=
      mul_le_mul_of_nonneg_right (by linarith) hη
    linarith
  have hB2 : (Z^η)^(10+6*K) * Z^(K'+εP) ≤ Z^(N+V+e) := by
    apply rpow_pow_mul_le Z η (K'+εP) _ (10+6*K) hZ1
    rw [he_def]
    push_cast
    have : 0 ≤ x*(30*mesh+κP) := by positivity
    linarith
  have hfinal : mass * (Cd * Z^η) * A ≤ 128^K * CP * Cd^(10+4*K) *
      (CR + 128^2*(1+boΦ)*Cd^(2*K)) * Z^(N+V+e) := by
    have hCdZ : 0 ≤ Cd * Z^η := by positivity
    have hZa1 := Real.rpow_nonneg hZ0.le (K'-N'-V+εP)
    have hZa3 := Real.rpow_nonneg hZ0.le (K'+εP)
    have hP2 : 0 ≤ CP * Z^(K'+εP) * Dmax := by positivity
    have h128T : 0 ≤ (128:ℝ)^K * T := by positivity
    calc mass * (Cd * Z^η) * A ≤ (128^K * T) * (Cd * Z^η) * A :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmass hCdZ) hA0
      _ = 128^K * (Cd * Z^η) * (T * Z^(-u')) *
            (CP * Z^(K'-N'-V+εP) * Dmax * Bc + CP * Z^(K'+εP) * Dmax * Lc * colM) := by
          rw [hAdef]; ring
      _ = 128^K * (Cd * Z^η) *
            (CP * Z^(K'-N'-V+εP) * Dmax * Bc + CP * Z^(K'+εP) * Dmax * Lc * colM) := by
          rw [hTinv, mul_one]
      _ ≤ 128^K * (Cd * Z^η) * (CP * Z^(K'-N'-V+εP) * Dmax * Bc + CP * Z^(K'+εP) * Dmax * 128 *
            (128 * (1 + boΦ) * (Cd * Z^η)^(2*K))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine add_le_add le_rfl ?_
          calc CP * Z^(K'+εP) * Dmax * Lc * colM = (CP * Z^(K'+εP) * Dmax) * (Lc * colM) := by
                ring
            _ ≤ (CP * Z^(K'+εP) * Dmax) * (128 * (128 * (1 + boΦ) * (Cd * Z^η)^(2*K))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul hLc' hcolM' hcolM0 (by norm_num)) hP2
            _ = _ := by ring
      _ = 128^K * CP * CR * Cd^(10+4*K) * ((Z^η)^(10+4*K) *
              (Z^(K'-N'-V+εP) * Z^(Hc'*(1+x)+εR))) +
            128^K * CP * 128^2 * (1 + boΦ) * Cd^(10+6*K) * ((Z^η)^(10+6*K) * Z^(K'+εP)) := by
          rw [hDmax, hBc]; ring
      _ ≤ 128^K * CP * CR * Cd^(10+4*K) * Z^(N+V+e) +
            128^K * CP * 128^2 * (1 + boΦ) * Cd^(10+6*K) * Z^(N+V+e) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hB1 (by positivity)
          · exact mul_le_mul_of_nonneg_left hB2 (by positivity)
      _ = 128^K * CP * Cd^(10+4*K) * (CR + 128^2*(1+boΦ)*Cd^(2*K)) * Z^(N+V+e) := by ring
  have hs0 : 0 ≤ (1 + ‖s‖)^(2*degree) := by positivity
  have hIb0 : 0 ≤ Ib^2 := sq_nonneg _
  have hmass0 : 0 ≤ mass := by rw [hmassdef]; positivity
  have hKK : (0:ℝ) ≤ (K:ℝ)^K := by positivity
  have hmassm : mass * mult * A ≤ (K:ℝ)^K * (mass * (Cd * Z^η) * A) := by
    calc mass * mult * A ≤ mass * ((K:ℝ)^K * (Cd * Z^η)) * A :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmult' hmass0) hA0
      _ = (K:ℝ)^K * (mass * (Cd * Z^η) * A) := by ring
  calc Ib^2 * (mass * mult * A * (1 + ‖s‖)^(2*degree))
      ≤ Ib^2 * (((K:ℝ)^K * (128^K * CP * Cd^(10+4*K) * (CR + 128^2*(1+boΦ)*Cd^(2*K)) *
          Z^(N+V+e))) * (1 + ‖s‖)^(2*degree)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (hmassm.trans (mul_le_mul_of_nonneg_left hfinal hKK)) hs0) hIb0
    _ = selConst Ib CP CR Cd boΦ K * Z^(N+V+e) * (1 + ‖s‖)^(2*degree) := by
        unfold selConst; ring

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.selection_at_scale
