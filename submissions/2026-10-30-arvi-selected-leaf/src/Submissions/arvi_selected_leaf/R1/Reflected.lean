/-
The reflected energy of one root class.

The baseline's reflected radial energy engine (`actual_original_radial_comparison`) applied to the rows of one
sixth-root class, with the radical row characters `radRow η m z` (conductor `≲ N(u) N(g)`, which is smaller
than the row norm by `N(g)⁵`), the long plain profile carried by the height profile `normPowerProfile`, and the
packed normalized slots as the row factor. The form is homogeneous in the long profile (as in
`natural_reference_reflection_homogeneous`).
-/
import Submissions.arvi_selected_leaf.R1.DualPoly
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceHomogeneous

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf.R1
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
open OAI OAI.SevenEighths CanonicalRowCompletion HeckeFamily HeckeDyadic ConcreteTraceCRT
open QuadraticInitialBound
open CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentOriginalRadialComparison CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentFiniteProfileExceptional CenteredMomentLattice
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

/-- A uniform bound for a product of normalized slots. -/
theorem slots_norm_bound {ι : Type*} [Fintype ι] (η : Character) (m A : O)
    (pool : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (t : ℝ) (P : ι → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : O, ‖∏ i, normalizedSlot η m A z (pool i) (β i) t (P i)‖ ≤ B := by
  refine ⟨∏ i, (‖(Real.sqrt (P i) : ℂ)⁻¹‖ * ∑ I ∈ pool i, ‖β i I‖),
    Finset.prod_nonneg (fun i _ => by positivity), ?_⟩
  intro z
  rw [norm_prod]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
  unfold normalizedSlot
  rw [norm_mul, rowSlot_eq_weight]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (CenteredMomentAbsoluteEnergy.rowWeight_norm_le_one_all η m A z t I)

/-- **The reflected energy of a root class** (homogeneous in the long profile). -/
theorem reflected_root (a b epsilon Cscale xi saving L : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hepsilon : 0 < epsilon) (hscale : 0 < Cscale) (hxi : 0 < xi) (B J : ℕ) (hB : 2 ≤ B) :
    ∃ n : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ (0,0) ∈ S ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (η : Character) (m : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2:O) ∣ m)
        (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (Wlong Wshort : 𝓢(ℝ,ℂ)),
        Function.support (Wlong:ℝ→ℂ) ⊆ Set.Icc a b → Function.support (Wshort:ℝ→ℂ) ⊆ Set.Icc a b →
      ∀ (ι : Type) [Fintype ι] (pool : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
        (t along bshort M E Rcap : ℝ),
        0 < K → (∀ z, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) →
        (∀ z, keep z → (radRow η m z hm hmLam hm2).residue ≠ 1) →
        M ≤ L + along →
        (∀ z, keep z → ((radRow η m z hm hmLam hm2).modulus.absNorm : ℝ) ≤ Cscale * Z^M) →
        0 ≤ E → 1 ≤ Rcap →
        (∀ z, keep z → ((radRow η m z hm hmLam hm2).modulus.absNorm : ℝ) ≤ Rcap) →
        (∀ v : ℝ, ∀ j k : Fin 2, ∀ x ∈ Set.Icc 0 (max 0 (M - along + xi) * Real.log Z),
          radialEnergy (fun z => polynomial (radRow η m z hm hmLam hm2) false
              (scaleTest (fun y : ℝ => (annulus y : ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v) *
            polynomial (radRow η m z hm hmLam hm2) false (scaleTest Wshort k) (Z^bshort) 0 t *
            ∏ i, normalizedSlot η m 1 z (pool i) (β i) t (P i)) keep Φ K ≤ E*(1+‖v‖)^(2*J)) →
        radialEnergy (fun z => polynomial (radRow η m z hm hmLam hm2) false Wlong (Z^along) 0 t *
            polynomial (radRow η m z hm hmLam hm2) false Wshort (Z^bshort) 0 t *
            ∏ i, normalizedSlot η m 1 z (pool i) (β i) t (P i)) keep Φ K ≤
          C * Rcap^epsilon * (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2 * (1+‖t‖)^(2*n) *
            (1 + 2*(max 0 (M - along + xi) * Real.log Z)) * E +
          D * Rcap^(2*epsilon) * (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2 * (1+‖t‖)^(2*n) *
            Z^(-2*saving) *
            radialEnergy (fun z => polynomial (radRow η m z hm hmLam hm2) false Wshort (Z^bshort) 0 t *
              ∏ i, normalizedSlot η m 1 z (pool i) (β i) t (P i)) keep Φ K := by
  obtain ⟨H, C, D, hC, hD, h⟩ := CenteredMomentUniformRadialComparison.actual_original_radial_comparison
    epsilon Cscale xi saving L hepsilon hscale hxi B J hB
  obtain ⟨n, T, Ct, hCt, hprofile⟩ := normPowerProfile_source_control a b ha H
  let S := T ∪ {(0,0)}
  have hS : (0,0) ∈ S := by simp [S]
  refine ⟨n, S, C*Ct^2, D*Ct^2, by positivity, by positivity, hS, ?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro η m hm hmLam hm2 keep Φ K Wlong Wshort hsLong hsShort ι _ pool β P t along bshort M E Rcap
    hK hΦ hχ hML hmod hE hRcap hcap hchildren
  by_cases hzero : sourceControl S Wlong = 0
  · have hw := sourceControl_zero S hS Wlong hzero
    subst Wlong
    simp [polynomial, summand, radialEnergy]
  have hpos : 0 < sourceControl S Wlong :=
    lt_of_le_of_ne (sourceControl_nonneg S Wlong) (Ne.symm hzero)
  let G := normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t
  let Src := Ct * (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong) * (1+‖t‖)^n
  have hSrc : 0 < Src := mul_pos (mul_pos hCt hpos) (by positivity)
  have hcontrol : sourceControl T Wlong ≤ sourceControl S Wlong :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left : T ⊆ T ∪ {(0,0)})) Wlong
  have hnorm : H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G ≤ Src :=
    (hprofile Wlong hsLong t).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcontrol hCt.le) (by positivity))
  obtain ⟨Pbound, _, hbound⟩ := slots_norm_bound η m 1 pool β t P
  have hh := hZ.2 (fun _ => G) (fun z => radRow η m z hm hmLam hm2)
    (fun z => ∏ i, normalizedSlot η m 1 z (pool i) (β i) t (P i))
    (fun _ => t) keep Φ K Pbound Wshort a b M along bshort E Src Rcap
    hK hΦ hbound hχ hb hsShort (Wshort.smooth ⊤) hML hmod hE hSrc (fun _ _ => hnorm) hRcap hcap
    hchildren
  have hG : (G : ℝ → ℂ) = normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t := rfl
  simp only [hG, CenteredMomentNaturalMaskedFloor.twist_polynomial _ Wlong a b ha hsLong t] at hh
  apply hh.trans_eq
  dsimp only [Src]
  rw [show (1+‖t‖)^(2*n) = ((1+‖t‖)^n)^2 by rw [Nat.mul_comm 2 n, pow_mul]]
  ring

end
end QRH.ArviSelectedLeaf.R1
