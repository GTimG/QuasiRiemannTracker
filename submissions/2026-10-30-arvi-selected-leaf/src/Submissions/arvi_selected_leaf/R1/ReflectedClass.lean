/-
The reflected class bound in closed form.

The reflected engine on one root class (`reflected_root`) with every separated energy bounded by PR 93's
selected norm (`direct_class` on the dual annulus polynomial, the short polynomial and the slots), at a source
bound `Xe` for dual lengths up to `Z^{max(0, M - along + ξ)}`, and the remainder term bounded by the short class
bound (`short_class`).
-/
import Submissions.arvi_selected_leaf.R1.ClassBound

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf.R1
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
open OAI OAI.SevenEighths CanonicalRowCompletion HeckeFamily HeckeDyadic ConcreteTraceCRT
open QuadraticInitialBound
open CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentSourceMass CenteredMomentOriginalRadialComparison CenteredMomentScaleSupremum
open CenteredMomentSectorLocalization
open Qrh.JointDetector Qrh.JointDetector.FineDetectorWords
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

/-- A uniform bound for the two annulus test profiles. -/
theorem annulus_test_bound : ∃ La : ℝ, 1 ≤ La ∧
    ∀ (j : Fin 2) (x : ℝ), ‖scaleTest (fun y : ℝ => (annulus y : ℂ)) j x‖ ≤ La := by
  have hcont : ∀ j, Continuous (scaleTest (fun y : ℝ => (annulus y : ℂ)) j) := fun j =>
    scaleTest_continuous _ CenteredMomentOneReflectionScaleEnergy.annulus_complex_smooth j
  have hsupp : ∀ j, Function.support (scaleTest (fun y : ℝ => (annulus y : ℂ)) j) ⊆ Set.Icc (1/4) 1 :=
    fun j => scaleTest_support _ _ _ CenteredMomentOneReflectionScaleEnergy.annulus_complex_support j
  have hcs : ∀ j, HasCompactSupport (scaleTest (fun y : ℝ => (annulus y : ℂ)) j) := fun j =>
    HasCompactSupport.intro isCompact_Icc (fun x hx => by
      by_contra h
      exact hx (hsupp j h))
  have hb : ∀ j : Fin 2, ∃ Cj : ℝ, ∀ x, ‖scaleTest (fun y : ℝ => (annulus y : ℂ)) j x‖ ≤ Cj :=
    fun j => (hcont j).bounded_above_of_compact_support (hcs j)
  choose Cj hCj using hb
  refine ⟨max 1 (max (Cj 0) (Cj 1)), le_max_left _ _, ?_⟩
  intro j x
  fin_cases j
  · exact (hCj 0 x).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hCj 1 x).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- The reflected class bound at one base `Z` (the content of `reflected_class`). -/
def ReflectedClassAt (n : ℕ) (S : Finset (ℕ×ℕ)) (C D La epsilon Cscale xi L Z : ℝ) : Prop :=
      ∀ (cores : Finset O) (Y δ Kn Xmax Xe : ℝ), 0 ≤ Y → 0 ≤ δ → δ ≤ 1 →
        SelectedAllSourceNormBound cores Y δ Kn Xmax →
      ∀ (ε : ℝ) (hε : 0 < ε) (η : Character) (m g : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m)
        (hm2 : (2:O) ∣ m) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ), (∀ z : O, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) → 0 < K →
        (∀ z, keep z → Φ (‖eisEmbedding z‖^2/K) ≠ 0 → ∃ u ∈ cores, z = u * g^6) →
        (∀ u ∈ cores, u * g^6 ≠ 0) →
      ∀ (Wlong Wshort : 𝓢(ℝ,ℂ)), Function.support (Wlong:ℝ→ℂ) ⊆ Set.Icc (1/4) (9/4) →
        Function.support (Wshort:ℝ→ℂ) ⊆ Set.Icc (1/4) (9/4) →
      ∀ (L₂ : ℝ), (∀ (k : Fin 2) (x : ℝ), ‖scaleTest Wshort k x‖ ≤ L₂) →
      ∀ (ι : Type) [Fintype ι] (pool : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
        (t along bshort M Rcap : ℝ) (B ms : ι → ℝ),
        (∀ i, (slotPoly η m g (pool i) (β i) t (P i)).NormLe (B i) ∧ 1 ≤ B i) →
        (∀ i, (slotPoly η m g (pool i) (β i) t (P i)).mass ≤ ms i) →
        (∀ z, keep z → (radRow η m z hm hmLam hm2).residue ≠ 1) →
        M ≤ L + along →
        (∀ z, keep z → ((radRow η m z hm hmLam hm2).modulus.absNorm : ℝ) ≤ Cscale * Z^M) →
        1 ≤ Rcap → (∀ z, keep z → ((radRow η m z hm hmLam hm2).modulus.absNorm : ℝ) ≤ Rcap) →
        max 1 (Z^(max 0 (M - along + xi))) * (max 1 (9/4 * Z^bshort) * ∏ i, B i) ≤ Xe →
        Xe ≤ Xmax →
        radialEnergy (fun z => polynomial (radRow η m z hm hmLam hm2) false Wlong (Z^along) 0 t *
            polynomial (radRow η m z hm hmLam hm2) false Wshort (Z^bshort) 0 t *
            ∏ i, normalizedSlot η m 1 z (pool i) (β i) t (P i)) keep Φ K ≤
          C * Rcap^epsilon * (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2 * (1+‖t‖)^(2*n) *
            (1 + 2*(max 0 (M - along + xi) * Real.log Z)) *
            (diagonalControl Φ * (2 * Kn * (Xe + Y)) *
              ((idealDivisorConstant ε hε * Xe^ε)^(2 + Fintype.card ι) *
                (128 * 1 * La^2 * (128 * (9/4) * L₂^2 * ∏ i, ms i)))) +
          D * Rcap^(2*epsilon) * (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2 * (1+‖t‖)^(2*n) *
            Z^(-2*(0:ℝ)) *
            (diagonalControl Φ * (2 * Kn * (Xe + Y)) *
              ((idealDivisorConstant ε hε * Xe^ε)^(1 + Fintype.card ι) *
                (128 * (9/4) * L₂^2 * ∏ i, ms i)))

/-- **The reflected class bound.** -/
theorem reflected_class (epsilon Cscale xi L : ℝ) (hepsilon : 0 < epsilon) (hscale : 0 < Cscale)
    (hxi : 0 < xi) :
    ∃ n : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ C D La : ℝ, 0 < C ∧ 0 < D ∧ 1 ≤ La ∧ (0,0) ∈ S ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ReflectedClassAt n S C D La epsilon Cscale xi L Z := by
  obtain ⟨n, S, C, D, hC, hD, hS, h⟩ := reflected_root (1/4) (9/4) epsilon Cscale xi 0 L
    (by norm_num) (by norm_num) hepsilon hscale hxi 2 0 le_rfl
  obtain ⟨La, hLa1, hLa⟩ := annulus_test_bound
  refine ⟨n, S, C, D, La, hC, hD, hLa1, hS, ?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1, ?_⟩
  unfold ReflectedClassAt
  intro cores Y δ Kn Xmax Xe hY hδ0 hδ1 hnorm ε hε η m g hm hmLam hm2 keep Φ K hΦ hK hcover hnz
    Wlong Wshort hsL hsS L₂ hL₂ ι _ pool β P t along bshort M Rcap B ms hB hms hχ hML hmod hRcap
    hcap hXe hXmax
  have hZ1 : 1 < Z := hZ.1
  have hZ0 : 0 < Z := by linarith
  have hlog : 0 < Real.log Z := Real.log_pos hZ1
  have hB0 : 0 ≤ ∏ i, B i := Finset.prod_nonneg (fun i _ => zero_le_one.trans (hB i).2)
  have hshortX : max 1 (9/4 * Z^bshort) * ∏ i, B i ≤ Xe := by
    refine le_trans ?_ hXe
    have h1 : 1 ≤ max 1 (Z^(max 0 (M - along + xi))) := le_max_left _ _
    have h2 : 0 ≤ max 1 (9/4 * Z^bshort) * ∏ i, B i := mul_nonneg (zero_le_one.trans (le_max_left _ _)) hB0
    nlinarith
  set E := diagonalControl Φ * (2 * Kn * (Xe + Y)) *
    ((idealDivisorConstant ε hε * Xe^ε)^(2 + Fintype.card ι) *
      (128 * 1 * La^2 * (128 * (9/4) * L₂^2 * ∏ i, ms i))) with hEdef
  have hX1 : 1 ≤ Xe := by
    refine le_trans ?_ hshortX
    have h3 : 1 ≤ ∏ i, B i := by
      have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ => (1:ℝ)) (g := B)
        (fun i _ => zero_le_one) (fun i _ => (hB i).2)
      simpa using this
    nlinarith [le_max_left 1 (9/4 * Z^bshort)]
  have hms0 : 0 ≤ ∏ i, ms i := Finset.prod_nonneg (fun i _ => (OrdPoly.mass_nonneg _).trans (hms i))
  have hL₂0 : 0 ≤ L₂ := (norm_nonneg _).trans (hL₂ 0 0)
  have hE0 : 0 ≤ E := by
    have := diagonalControl_nonneg Φ
    have := hnorm.1
    have := idealDivisorConstant_pos ε hε
    have : 0 ≤ Xe^ε := Real.rpow_nonneg (zero_le_one.trans hX1) ε
    have : 0 ≤ Xe + Y := by linarith
    positivity
  have hchildren : ∀ v : ℝ, ∀ j k : Fin 2, ∀ x ∈ Set.Icc 0 (max 0 (M - along + xi) * Real.log Z),
      radialEnergy (fun z => polynomial (radRow η m z hm hmLam hm2) false
          (scaleTest (fun y : ℝ => (annulus y : ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v) *
        polynomial (radRow η m z hm hmLam hm2) false (scaleTest Wshort k) (Z^bshort) 0 t *
        ∏ i, normalizedSlot η m 1 z (pool i) (β i) t (P i)) keep Φ K ≤ E*(1+‖v‖)^(2*0) := by
    intro v j k x hx
    rw [mul_zero, pow_zero, mul_one]
    have hex : Real.exp x ≤ Z^(max 0 (M - along + xi)) := by
      rw [Real.rpow_def_of_pos hZ0]
      apply Real.exp_le_exp.mpr
      have := hx.2
      nlinarith
    have hXd : max 1 (1 * Real.exp x) * (max 1 (9/4 * Z^bshort) * ∏ i, B i) ≤ Xe := by
      refine le_trans ?_ hXe
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (zero_le_one.trans (le_max_left _ _)) hB0)
      rw [one_mul]
      exact max_le_max le_rfl hex
    have hsa : Function.support (scaleTest (fun y : ℝ => (annulus y : ℂ)) j) ⊆ Set.Iic 1 :=
      (scaleTest_support _ _ _ CenteredMomentOneReflectionScaleEnergy.annulus_complex_support j).trans
        Set.Icc_subset_Iic_self
    have hss : Function.support (scaleTest (Wshort : ℝ → ℂ) k) ⊆ Set.Iic (9/4) :=
      (scaleTest_support _ _ _ hsS k).trans Set.Icc_subset_Iic_self
    exact direct_class cores Y δ Kn Xmax Xe hY hδ0 hδ1 hnorm ε hε η m g hm hmLam hm2 keep Φ K hΦ
      hcover hnz _ _ (Real.exp x) (Z^bshort) (-2*Real.pi*v) t 1 (9/4) La L₂ (Real.exp_pos x)
      (Real.rpow_pos_of_pos hZ0 _) zero_le_one (by norm_num) hsa hss (hLa j) (hL₂ k) pool β P t B ms
      hB hms hXd hXmax
  have hh := hZ.2 η m hm hmLam hm2 keep Φ K Wlong Wshort hsL hsS ι pool β P t along bshort M E Rcap
    hK hΦ hχ hML hmod hE0 hRcap hcap hchildren
  have hss0 : Function.support (Wshort : ℝ → ℂ) ⊆ Set.Iic (9/4) := hsS.trans Set.Icc_subset_Iic_self
  have hshort := short_class cores Y δ Kn Xmax Xe hY hδ0 hδ1 hnorm ε hε η m g hm hmLam hm2 keep Φ K hΦ
    hcover hnz Wshort (Z^bshort) t (9/4) L₂ (Real.rpow_pos_of_pos hZ0 _) (by norm_num) hss0
    (fun x => by simpa [scaleTest] using hL₂ 0 x) pool β P t B ms hB hms hshortX hXmax
  refine hh.trans ?_
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left hshort
  have := Real.rpow_nonneg (zero_le_one.trans hRcap) (2*epsilon)
  have := Real.rpow_nonneg hZ0.le (-2*(0:ℝ))
  positivity

end
end QRH.ArviSelectedLeaf.R1
