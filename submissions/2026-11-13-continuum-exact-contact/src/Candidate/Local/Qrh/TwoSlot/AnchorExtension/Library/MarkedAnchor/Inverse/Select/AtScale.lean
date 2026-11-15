/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Select.Counting
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Select.Choice
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.Statement
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Oracle

/-!
# Inverse.Select.AtScale — selection, second Poisson step and restoration at one scale `Z`

`selection_at_scale`: for one canonical datum at one scale `Z`, a `HighLive` state
`(N, V, M, Q, z)` (`z` the actual width of the slot subcollection `ss`), given
* the second Poisson step at this scale (`Poisson.PoissonStepAt`),
* the restored child bound for every residual subcollection (the datum-level content of
  `RestoreChildBound`),
* the divisor bound `#divisors(I) ≤ Cd Z^η` for `N I ≤ Z^4`,

the canonical energy is `≤ Cfin Z^(N+V+e) (1+|s|)^(2 degree)` with the explicit constant
`selConst` and the explicit excess `selExcess = 5 mesh + x(30 mesh + κP) + κP + εP + εR
+ (10+6K) η`, `x = u/(1-6u-κ)`.

Steps: rows vanish unless `z ≤ N + mesh` (`rows_vanish`); Gauss ball enlarged to
`M₀ = 2F-1+κ`; whole-slot selection `R ⊆ ss` of width `u' ∈ [u₁ - 2 mesh, u₁]`,
`u₁ = max 0 (u - 3 mesh)` (`live_selection`); separation and central Cauchy (`selected_energy_bound`) with the common
inner row at column scale `Z^(N-u')`, rows `Z^(M₀+4u')`; one Poisson call per height; child from
the restoration at `Hc' = 1-6u'-κ+κP ∈ [1-6u-κ, 2]`; diagonal by the ideal and divisor counts.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths OAI.SevenEighths.InverseMoment

local notation "O" => OAI.ActualEisensteinCubic.O

/-- The explicit constant of the selection at one scale. -/
def selConst (Ib CP CR Cd boΦ : ℝ) (K : ℕ) : ℝ :=
  Ib^2 * 128^K * (K:ℝ)^K * Cd^(10+4*K) * CP * (CR + 128^2*(1+boΦ)*Cd^(2*K))

/-- The explicit exponent excess of the selection at one scale. -/
def selExcess (x mesh κP εP εR η : ℝ) (K : ℕ) : ℝ :=
  5*mesh + x*(30*mesh+κP) + κP + εP + εR + (10+6*K)*η

theorem logb_prod_eq_sum {σ : Type} (s : Finset σ) (H : σ → ℝ) (hH : ∀ i ∈ s, H i ≠ 0) (Z : ℝ) :
    Real.logb Z (∏ i ∈ s, H i) = ∑ i ∈ s, Real.logb Z (H i) := by
  unfold Real.logb
  rw [Real.log_prod hH, Finset.sum_div]

section
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]

/-- `∏_R H / 2^|R| ≤ N(img d) ≤ ∏_R H` for one prime per slot with ratio `[H/2, H]`. -/
theorem tuple_norm_bounds (p : ι → O) (R : Finset σ) (lists : σ → Finset ι) (H : σ → ℝ)
    (hPr : ∀ i ∈ R, ∀ P ∈ lists i, H i / 2 ≤ FirstPassCubeLabels.primeProductNorm p {P} ∧
      FirstPassCubeLabels.primeProductNorm p {P} ≤ H i)
    (d : ∀ i ∈ R, ι) (hd : d ∈ injPi R lists) :
    (∏ i ∈ R, H i) / 2^R.card ≤ FirstPassCubeLabels.primeProductNorm p (tupleImage R d) ∧
      FirstPassCubeLabels.primeProductNorm p (tupleImage R d) ≤ ∏ i ∈ R, H i := by
  rw [tupleImage_norm p R lists d hd]
  have hmem : ∀ i : R, d i.1 i.2 ∈ lists i.1 :=
    fun i => Finset.mem_pi.mp (injPi_subset _ _ hd) i.1 i.2
  have hlow : ∀ i ∈ R.attach, H i.1 / 2 ≤ FirstPassCubeLabels.primeProductNorm p {d i.1 i.2} :=
    fun i _ => (hPr i.1 i.2 _ (hmem i)).1
  have hup : ∀ i ∈ R.attach, FirstPassCubeLabels.primeProductNorm p {d i.1 i.2} ≤ H i.1 :=
    fun i _ => (hPr i.1 i.2 _ (hmem i)).2
  have hH0 : ∀ i ∈ R.attach, 0 ≤ H i.1 / 2 := by
    intro i hi
    have h1 := hlow i hi
    have h2 := hup i hi
    have h3 : 0 ≤ FirstPassCubeLabels.primeProductNorm p {d i.1 i.2} := by
      unfold FirstPassCubeLabels.primeProductNorm; positivity
    linarith
  constructor
  · calc (∏ i ∈ R, H i) / 2^R.card = ∏ i ∈ R.attach, H i.1 / 2 := by
          rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_attach,
            Finset.prod_attach R H]
      _ ≤ _ := Finset.prod_le_prod₀ hH0 hlow
  · calc ∏ i ∈ R.attach, FirstPassCubeLabels.primeProductNorm p {d i.1 i.2}
        ≤ ∏ i ∈ R.attach, H i.1 :=
          Finset.prod_le_prod₀ (fun i _ => by unfold FirstPassCubeLabels.primeProductNorm; positivity)
            hup
      _ = ∏ i ∈ R, H i := Finset.prod_attach R H

variable (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

/-- The rows vanish when the marked width exceeds the column scale. -/
theorem rows_vanish (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (ss : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (H : σ → ℝ)
    (hPr : ∀ i ∈ ss, ∀ P ∈ lists i, H i / 2 ≤ FirstPassCubeLabels.primeProductNorm p {P} ∧
      FirstPassCubeLabels.primeProductNorm p {P} ≤ H i)
    (Wc : ℝ → ℂ) (lo hi : ℝ) (hsW : Function.support Wc ⊆ Set.Icc lo hi) (s X : ℝ) (hX : 0 < X)
    (hbig : 2^ss.card * hi * X < ∏ i ∈ ss, H i) (f k : O) :
    canonRowInj p hp hcop hg pool Ψ m f k ss lists a (childLogTest Wc s) X = 0 := by
  rw [row_eq_column_sum]
  apply Finset.sum_eq_zero
  intro U _
  by_cases hpm : primeMarkInj ss lists a U = 0
  · unfold SecondPassArithmetic.secondChildColumn
    rw [hpm]; ring
  · have hex : ∃ d ∈ injPi ss lists, tupleImage ss d ⊆ U := by
      by_contra hno
      push_neg at hno
      apply hpm
      rw [markInj_tuple_indicator]
      apply Finset.sum_eq_zero
      intro d hd
      rw [if_neg (hno d hd), mul_zero]
    obtain ⟨d, hd, hdU⟩ := hex
    have hNd := (tuple_norm_bounds p ss lists H hPr d hd).1
    have hNU : FirstPassCubeLabels.primeProductNorm p (tupleImage ss d) ≤
        FirstPassCubeLabels.primeProductNorm p U := by
      have key := FirstPassCubeLabels.primeProductNorm_union p (tupleImage ss d)
        (U \ tupleImage ss d) Finset.disjoint_sdiff
      rw [Finset.union_sdiff_of_subset hdU] at key
      rw [key]
      have h1 : 1 ≤ FirstPassCubeLabels.primeProductNorm p (U \ tupleImage ss d) :=
        one_le_eis_norm_sq _ (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
      have h0 : 0 ≤ FirstPassCubeLabels.primeProductNorm p (tupleImage ss d) := by
        unfold FirstPassCubeLabels.primeProductNorm; positivity
      nlinarith
    have hW : Wc (FirstPassCubeLabels.primeProductNorm p U / X) = 0 := by
      by_contra hne
      have hmem := hsW hne
      have h2 : FirstPassCubeLabels.primeProductNorm p U ≤ hi * X := by
        have := hmem.2
        rwa [div_le_iff₀ hX] at this
      have h2p : (0:ℝ) < 2^ss.card := by positivity
      have : (∏ i ∈ ss, H i) ≤ 2^ss.card * hi * X := by
        rw [div_le_iff₀ h2p] at hNd
        nlinarith
      linarith
    rw [childLogTest, hW, zero_mul, zero_mul]

/-- Coefficients agreeing on the lists of the slots give the same energy. -/
theorem energy_congr (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (S : Finset σ)
    (lists : σ → Finset ι) (a a' : σ → ι → ℂ) (h : ∀ i ∈ S, ∀ P ∈ lists i, a' i P = a i P)
    (labels : Finset (Ideal O)) (ks : Finset O) (Dw : Ideal O → ℝ) (Wf : ℝ → ℂ) (X Z F : ℝ) :
    columnEnergyInj p hp hcop hg pool Ψ m S lists a' labels
        ks Dw Wf X Z F =
      columnEnergyInj p hp hcop hg pool Ψ m S lists a labels
        ks Dw Wf X Z F := by
  unfold columnEnergyInj canonRowInj
  rw [markInj_congr S lists a a' h]

end

/-- Coefficients agreeing on the lists of the slots give the same child bound. -/
theorem childBound_congr {ι σ : Type} {instι : DecidableEq ι} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, ActualEisensteinCubic.lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (S : Finset σ) (lists : σ → Finset ι)
    (a a' : σ → ι → ℂ) (h : ∀ i ∈ S, ∀ P ∈ lists i, a' i P = a i P) {J : ℕ}
    (Φs : Fin J → ℝ → ℂ) (deg : ℕ) (Z Xmax Gmax Hc B : ℝ)
    (hCB : @ChildBoundInj ι σ instι p _ hg pool Ψ m S lists a J Φs deg Z Xmax Gmax Hc B) :
    @ChildBoundInj ι σ instι p _ hg pool Ψ m S lists a' J Φs deg Z Xmax Gmax Hc B := by
  intro t ht hNt Js hJs ψ hψ j s Xc hXc hXc' hd neg
  have hb := hCB t ht hNt Js hJs ψ hψ j s Xc hXc hXc' hd neg
  have hsub : S \ Js ⊆ S := Finset.sdiff_subset
  unfold mobiusChildSumInj mobiusChildRowInj at hb ⊢
  refine le_of_eq_of_le ?_ hb
  apply Finset.sum_congr rfl
  intro y _
  congr 2
  apply Finset.sum_congr rfl
  intro A _
  congr 3
  rw [markInj_congr (S \ Js) lists a a' (fun i hi P hP => h i (Finset.mem_sdiff.mp hi).1 P hP)]

section Counts
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hp hinj in
theorem list_count_le (L : Finset ι) (Y : ℝ) (hY : 1 ≤ Y)
    (hL : ∀ P ∈ L, FirstPassCubeLabels.primeProductNorm p {P} ≤ Y) : (L.card : ℝ) ≤ 128 * Y := by
  have hsub : L.image (fun P => ({P} : Finset ι)) ⊆
      L.powerset.filter (fun U => FirstPassCubeLabels.primeProductNorm p U ≤ Y) := by
    intro U hU
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hU
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hP), hL P hP⟩
  have hc : (L.image (fun P => ({P} : Finset ι))).card = L.card :=
    Finset.card_image_of_injective L Finset.singleton_injective
  have h := Finset.card_le_card hsub
  rw [hc] at h
  exact (Nat.cast_le.mpr h).trans (powerset_norm_count p hp hinj L Y hY)

include hp hinj in
/-- Central mass of the tuple selection: `∑_d |∏ a(d_i)|² ≤ 128^|R| ∏_R H`. -/
theorem mass_le (R : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (H : σ → ℝ)
    (ha : ∀ i ∈ R, ∀ P ∈ lists i, ‖a i P‖ ≤ 1) (hH : ∀ i ∈ R, 1 ≤ H i)
    (hPr : ∀ i ∈ R, ∀ P ∈ lists i, FirstPassCubeLabels.primeProductNorm p {P} ≤ H i) :
    (∑ d ∈ injPi R lists, ‖∏ i ∈ R.attach, a i.1 (d i.1 i.2)‖^2) ≤ 128^R.card * ∏ i ∈ R, H i := by
  have h1 : ∀ d ∈ injPi R lists, ‖∏ i ∈ R.attach, a i.1 (d i.1 i.2)‖^2 ≤ 1 := by
    intro d hd
    rw [norm_prod]
    have hle : ∏ i ∈ R.attach, ‖a i.1 (d i.1 i.2)‖ ≤ 1 := by
      calc ∏ i ∈ R.attach, ‖a i.1 (d i.1 i.2)‖ ≤ ∏ _i ∈ R.attach, (1:ℝ) :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
              (fun i _ => ha i.1 i.2 _ (Finset.mem_pi.mp (injPi_subset _ _ hd) i.1 i.2))
        _ = 1 := Finset.prod_const_one
    have h0 : 0 ≤ ∏ i ∈ R.attach, ‖a i.1 (d i.1 i.2)‖ :=
      Finset.prod_nonneg (fun _ _ => norm_nonneg _)
    nlinarith
  calc _ ≤ ∑ _d ∈ injPi R lists, (1:ℝ) := Finset.sum_le_sum h1
    _ ≤ ∑ _d ∈ R.pi lists, (1:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (injPi_subset R lists) (fun _ _ _ => zero_le_one)
    _ = ∏ i ∈ R, ((lists i).card : ℝ) := by
        rw [Finset.sum_const, Finset.card_pi, nsmul_eq_mul, mul_one]
        push_cast; rfl
    _ ≤ ∏ i ∈ R, (128 * H i) :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity)
          (fun i hi => list_count_le p hp hinj _ _ (hH i hi) (hPr i hi))
    _ = 128^R.card * ∏ i ∈ R, H i := by rw [Finset.prod_mul_distrib, Finset.prod_const]

include hp hinj in
/-- The paid diagonal column mass is subpower. -/
theorem colMass_le [Fintype ι] (S : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (K : ℕ)
    (hSK : S.card ≤ K) (ha : ∀ i ∈ S, ∀ P ∈ lists i, ‖a i P‖ ≤ 1) (Φ : ℝ → ℂ)
    (hΦn : ∀ y, ‖Φ y‖ ≤ 1) (lo' boΦ : ℝ) (hbo : 0 ≤ boΦ)
    (hΦs : Function.support Φ ⊆ Set.Icc lo' boΦ) (Z N' Cd η : ℝ) (hZ : 1 ≤ Z) (hN' : 0 ≤ N')
    (hCd : 1 ≤ Cd) (hη : 0 ≤ η) (hZ4 : boΦ * Z^N' ≤ Z^4)
    (hdiv : ∀ I : Ideal O, I ≠ ⊥ → (Ideal.absNorm I : ℝ) ≤ Z^4 →
      ((IdealMobiusDivisorSum.idealDivisors I).card : ℝ) ≤ Cd * Z^η) :
    Poisson.columnMass p Finset.univ S lists a Φ Z N' ≤ 128 * (1 + boΦ) * (Cd * Z^η)^(2*K) := by
  unfold Poisson.columnMass
  have hZ0 : 0 < Z := by linarith
  have hZN : 0 < Z^N' := Real.rpow_pos_of_pos hZ0 _
  have hZN1 : 1 ≤ Z^N' := Real.one_le_rpow hZ hN'
  set Y := boΦ * Z^N' with hY
  set c := (Cd * Z^η)^(2*K) with hcdef
  have hc1 : 1 ≤ Cd * Z^η := one_le_mul_of_one_le_of_one_le hCd (Real.one_le_rpow hZ hη)
  have hc0 : 0 ≤ c := by positivity
  have hterm : ∀ U ∈ (Finset.univ : Finset ι).powerset,
      ‖primeMarkInj S lists a U‖^2 * ‖Φ (FirstPassCubeLabels.primeProductNorm p U / Z^N')‖^2 ≤
        if FirstPassCubeLabels.primeProductNorm p U ≤ Y then c else 0 := by
    intro U _
    by_cases hΦ0 : Φ (FirstPassCubeLabels.primeProductNorm p U / Z^N') = 0
    · rw [hΦ0, norm_zero]
      split_ifs <;> simp [hc0]
    · have hmem := hΦs hΦ0
      have hNU : FirstPassCubeLabels.primeProductNorm p U ≤ Y := by
        have h2 := hmem.2
        rw [div_le_iff₀ hZN] at h2
        exact h2
      rw [if_pos hNU]
      have hcard : (U.card : ℝ) ≤ Cd * Z^η := by
        refine (card_le_idealDivisors p hp hinj U).trans (hdiv _ (span_prod_ne_bot p hp U) ?_)
        rw [← primeProductNorm_eq_absNorm]
        linarith
      have hpm := primeMarkInj_norm_le S lists a ha U
      have h1 : ‖primeMarkInj S lists a U‖ ≤ (Cd * Z^η)^K :=
        hpm.trans ((pow_le_pow_left₀ (Nat.cast_nonneg _) hcard _).trans
          (pow_le_pow_right₀ hc1 hSK))
      have h2 : ‖Φ (FirstPassCubeLabels.primeProductNorm p U / Z^N')‖^2 ≤ 1 := by
        have := hΦn (FirstPassCubeLabels.primeProductNorm p U / Z^N')
        have := norm_nonneg (Φ (FirstPassCubeLabels.primeProductNorm p U / Z^N'))
        nlinarith
      calc ‖primeMarkInj S lists a U‖^2 *
            ‖Φ (FirstPassCubeLabels.primeProductNorm p U / Z^N')‖^2
          ≤ ((Cd * Z^η)^K)^2 * 1 := by gcongr
        _ = c := by rw [mul_one, ← pow_mul, mul_comm K 2]
  have hcount : (((Finset.univ : Finset ι).powerset.filter
      (fun U => FirstPassCubeLabels.primeProductNorm p U ≤ Y)).card : ℝ) ≤ 128 * max 1 Y := by
    refine le_trans ?_ (powerset_norm_count p hp hinj Finset.univ (max 1 Y) (le_max_left _ _))
    exact_mod_cast Finset.card_le_card (fun U hU => by
      simp only [Finset.mem_filter] at hU ⊢
      exact ⟨hU.1, hU.2.trans (le_max_right _ _)⟩)
  have hmax : max 1 Y ≤ (1 + boΦ) * Z^N' := max_le (by nlinarith) (by rw [hY]; nlinarith)
  have hinv : Z^(-N') * Z^N' = 1 := by
    rw [Real.rpow_neg hZ0.le, inv_mul_cancel₀ hZN.ne']
  calc Z^(-N') * ∑ U ∈ (Finset.univ : Finset ι).powerset,
        ‖primeMarkInj S lists a U‖^2 * ‖Φ (FirstPassCubeLabels.primeProductNorm p U / Z^N')‖^2
      ≤ Z^(-N') * ∑ U ∈ (Finset.univ : Finset ι).powerset,
          (if FirstPassCubeLabels.primeProductNorm p U ≤ Y then c else 0) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (Real.rpow_nonneg hZ0.le _)
    _ = Z^(-N') * (c * (((Finset.univ : Finset ι).powerset.filter
          (fun U => FirstPassCubeLabels.primeProductNorm p U ≤ Y)).card : ℝ)) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ Z^(-N') * (c * (128 * ((1 + boΦ) * Z^N'))) := by
        gcongr
        exact hcount.trans (by gcongr)
    _ = 128 * (1 + boΦ) * c * (Z^(-N') * Z^N') := by ring
    _ = 128 * (1 + boΦ) * c := by rw [hinv, mul_one]

end Counts

theorem rpow_pow_mul_le (Z η a e : ℝ) (n : ℕ) (hZ : 1 ≤ Z) (h : n * η + a ≤ e) :
    (Z^η)^n * Z^a ≤ Z^e := by
  have hZ0 : 0 < Z := by linarith
  rw [← Real.rpow_natCast (Z^η) n, ← Real.rpow_mul hZ0.le, ← Real.rpow_add hZ0]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith [mul_comm η (n:ℝ)])

end
end Qrh.MarkedAnchor.Inverse
