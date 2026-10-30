/-
The dyadic polynomials of the radical row character at a sixth root, as ordinary polynomials in the core,
and the separated energies of one root class.

At `z = u·g⁶` the radical row character `radRow η m z` has coefficients `rootCommon η m g 0 I · idealRowHom u I`
(`radRow_coeff_root`), so every dyadic polynomial `polynomial (radRow η m z) false W D 0 ω` is the value at the
core `u` of one ordinary polynomial `dyadPoly η m g W D ω b`, common to all cores of the root. The separated
energies of the reflected engine (a dual polynomial, the short plain polynomial and the slots) are then bounded
by PR 93's selected all-source norm (`separated_root_energy`).
-/
import Submissions.arvi_selected_leaf.R1.RootEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicBridge

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf.R1
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths CanonicalRowCompletion HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentSourceMass CenteredMomentOriginalRadialComparison
open Qrh.JointDetector Qrh.JointDetector.FineDetectorWords
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

/-- The dyadic polynomial at the root `g`: length `D`, frequency `ω`, support radius `b`. -/
def dyadPoly (η : Character) (m g : O) (W : ℝ → ℂ) (D ω b : ℝ) : OrdPoly :=
  ⟨idealBall (b*D), fun I => (D : ℂ)^(-(1/2 : ℂ)) *
    (rootCommon η m g 0 I.val * W ((Ideal.absNorm I.val : ℝ)/D) *
      (((Ideal.absNorm I.val : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift 0 ω))⟩

/-- **The dyadic polynomial of the radical row character at a sixth root.** -/
theorem dyadPoly_eval (η : Character) (m u g : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2:O) ∣ m)
    (hw : u * g^6 ≠ 0) (W : ℝ → ℂ) (D ω b : ℝ) (hD : 0 < D) (hs : Function.support W ⊆ Set.Iic b) :
    (dyadPoly η m g W D ω b).eval u =
      polynomial (radRow η m (u * g^6) hm hmLam hm2) false W D 0 ω := by
  have hcover : ∀ J : Ideal O, J ≠ 0 → W ((J.absNorm : ℝ)/D) ≠ 0 → J ∈ idealBall (b*D) := by
    intro J hJ hW
    rw [mem_idealBall]
    refine ⟨hJ, ?_⟩
    have h1 := hs hW
    simp only [Set.mem_Iic] at h1
    rwa [div_le_iff₀ hD] at h1
  rw [HeckeDetectorDyadicBridge.polynomial_eq_finite _ false W D 0 ω (idealBall (b*D)) hcover]
  simp only [OrdPoly.eval, dyadPoly]
  rw [ordinaryPolynomial, Finset.sum_coe_sort (idealBall (b*D)) (fun I => (D : ℂ)^(-(1/2 : ℂ)) *
    (rootCommon η m g 0 I * W ((Ideal.absNorm I : ℝ)/D) *
      (((Ideal.absNorm I : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift 0 ω)) * idealRowHom u I), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  simp only [HeckeDyadic.coefficient, Bool.false_eq_true, ↓reduceIte]
  rw [radRow_coeff_root η m u g hm hmLam hm2 hw I]
  ring

theorem dyadPoly_normLe (η : Character) (m g : O) (W : ℝ → ℂ) (D ω b : ℝ) :
    (dyadPoly η m g W D ω b).NormLe (max 1 (b*D)) := by
  intro I hI
  have h := (mem_idealBall (b*D) I).mp hI
  exact ⟨h.1, h.2.trans (le_max_right _ _)⟩

/-- At most `128 H` nonzero ideals have norm at most `H`. -/
theorem ideal_card_le (s : Finset (Ideal O)) (H : ℝ) (hH : 0 ≤ H) (hpos : ∀ I ∈ s, I ≠ ⊥)
    (hN : ∀ I ∈ s, (Ideal.absNorm I : ℝ) ≤ H) : (s.card : ℝ) ≤ 128 * H := by
  rcases le_or_gt 1 H with h1 | h1
  · exact DescentFiberCost.finite_ideal_count_real s H h1 hpos hN
  · have hempty : s = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro I hI
      have h1' : (1:ℝ) ≤ Ideal.absNorm I := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hpos I hI))
      linarith [hN I hI]
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

/-- Mass of a dyadic polynomial: at most `128·b·L²`. -/
theorem dyadPoly_mass_le (η : Character) (m g : O) (W : ℝ → ℂ) (D ω b L : ℝ) (hD : 0 < D)
    (hb : 0 ≤ b) (hW : ∀ x, ‖W x‖ ≤ L) :
    (dyadPoly η m g W D ω b).mass ≤ 128 * b * L^2 := by
  have hL : 0 ≤ L := (norm_nonneg _).trans (hW 0)
  have hDn : ‖(D : ℂ)^(-(1/2 : ℂ))‖ = D^(-(1/2:ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hD]
    norm_num
  have hDsq : (D^(-(1/2:ℝ)))^2 = 1/D := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le]
    norm_num
    rw [Real.rpow_neg_one]
  have hterm : ∀ I : (idealBall (b*D) : Finset (Ideal O)),
      ‖(D : ℂ)^(-(1/2 : ℂ)) * (rootCommon η m g 0 I.val * W ((Ideal.absNorm I.val : ℝ)/D) *
        (((Ideal.absNorm I.val : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift 0 ω))‖^2 ≤ L^2 / D := by
    intro I
    have hI := (mem_idealBall _ _).mp I.property
    have hN : 0 < (Ideal.absNorm I.val : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
    have hND : 0 < (Ideal.absNorm I.val : ℝ)/D := div_pos hN hD
    have hph : ‖(((Ideal.absNorm I.val : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift 0 ω)‖ = 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hND]
      simp [HeckeDyadic.shift]
    have h1 := rootCommon_norm_le η m g 0 I.val
    have h2 := hW ((Ideal.absNorm I.val : ℝ)/D)
    rw [norm_mul, norm_mul, norm_mul, hph, hDn, mul_one]
    have hprod : ‖rootCommon η m g 0 I.val‖ * ‖W ((Ideal.absNorm I.val : ℝ)/D)‖ ≤ L := by
      calc _ ≤ 1 * L := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = L := one_mul L
    have hprod0 : 0 ≤ ‖rootCommon η m g 0 I.val‖ * ‖W ((Ideal.absNorm I.val : ℝ)/D)‖ := by positivity
    have hD0 : 0 ≤ D^(-(1/2:ℝ)) := Real.rpow_nonneg hD.le _
    calc (D^(-(1/2:ℝ)) * (‖rootCommon η m g 0 I.val‖ * ‖W ((Ideal.absNorm I.val : ℝ)/D)‖))^2
        = (D^(-(1/2:ℝ)))^2 * (‖rootCommon η m g 0 I.val‖ * ‖W ((Ideal.absNorm I.val : ℝ)/D)‖)^2 := by
          ring
      _ ≤ (1/D) * L^2 := by
          rw [hDsq]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hprod0 hprod 2) (by positivity)
      _ = L^2/D := by ring
  have hcard : ((idealBall (b*D)).card : ℝ) ≤ 128 * (b*D) :=
    ideal_card_le (idealBall (b*D)) (b*D) (mul_nonneg hb hD.le)
      (fun I hI => ((mem_idealBall (b*D) I).mp hI).1)
      (fun I hI => ((mem_idealBall (b*D) I).mp hI).2)
  calc (dyadPoly η m g W D ω b).mass
      ≤ ∑ _I : (idealBall (b*D) : Finset (Ideal O)), L^2/D := Finset.sum_le_sum fun I _ => hterm I
    _ = ((idealBall (b*D)).card : ℝ) * (L^2/D) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ 128 * (b*D) * (L^2/D) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp

variable {ι : Type*} [Fintype ι]

/-- The separated row polynomial at the root `g` with the norm bound of each factor. -/
def sepList (η : Character) (m g : O) (W₁ W₂ : ℝ → ℂ) (D₁ D₂ ω₁ ω₂ b₁ b₂ : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t : ℝ) (B : ι → ℝ) :
    List (OrdPoly × ℝ) :=
  [(dyadPoly η m g W₁ D₁ ω₁ b₁, max 1 (b₁*D₁)), (dyadPoly η m g W₂ D₂ ω₂ b₂, max 1 (b₂*D₂))] ++
    (Finset.univ.toList.map (fun i => (slotPoly η m g (S i) (β i) t (P i), B i)))

theorem sepList_length (η : Character) (m g : O) (W₁ W₂ : ℝ → ℂ) (D₁ D₂ ω₁ ω₂ b₁ b₂ : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t : ℝ) (B : ι → ℝ) :
    (sepList η m g W₁ W₂ D₁ D₂ ω₁ ω₂ b₁ b₂ S β P t B).length = 2 + Fintype.card ι := by
  simp [sepList, Finset.length_toList]
  omega

/-- **The separated row at a sixth root is one ordinary polynomial in the core.** -/
theorem sep_eval (η : Character) (m u g : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2:O) ∣ m)
    (hw : u * g^6 ≠ 0) (W₁ W₂ : ℝ → ℂ) (D₁ D₂ ω₁ ω₂ b₁ b₂ : ℝ) (hD₁ : 0 < D₁) (hD₂ : 0 < D₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t : ℝ) (B : ι → ℝ) :
    polynomial (radRow η m (u * g^6) hm hmLam hm2) false W₁ D₁ 0 ω₁ *
        polynomial (radRow η m (u * g^6) hm hmLam hm2) false W₂ D₂ 0 ω₂ *
        ∏ i, normalizedSlot η m 1 (u * g^6) (S i) (β i) t (P i) =
      (OrdPoly.prod ((sepList η m g W₁ W₂ D₁ D₂ ω₁ ω₂ b₁ b₂ S β P t B).map Prod.fst)).eval u := by
  rw [OrdPoly.eval_prod]
  simp only [sepList, List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one, List.map_map, Function.comp_def]
  rw [Finset.prod_map_toList]
  simp only [dyadPoly_eval η m u g hm hmLam hm2 hw W₁ D₁ ω₁ b₁ hD₁ hs₁,
    dyadPoly_eval η m u g hm hmLam hm2 hw W₂ D₂ ω₂ b₂ hD₂ hs₂, slotPoly_eval]

/-- **The separated energy of one root class** under PR 93's selected all-source norm. -/
theorem separated_root_energy (cores : Finset O) (Y δ Kn Xmax X : ℝ) (hY : 0 ≤ Y)
    (hnorm : SelectedAllSourceNormBound cores Y δ Kn Xmax) (ε : ℝ) (hε : 0 < ε)
    (η : Character) (m g : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2:O) ∣ m)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hΦ : ∀ z : O, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re)
    (hcover : ∀ z, keep z → Φ (‖eisEmbedding z‖^2/K) ≠ 0 → ∃ u ∈ cores, z = u * g^6)
    (hnz : ∀ u ∈ cores, u * g^6 ≠ 0)
    (W₁ W₂ : ℝ → ℂ) (D₁ D₂ ω₁ ω₂ b₁ b₂ : ℝ) (hD₁ : 0 < D₁) (hD₂ : 0 < D₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t : ℝ) (B : ι → ℝ)
    (hB : ∀ i, (slotPoly η m g (S i) (β i) t (P i)).NormLe (B i) ∧ 1 ≤ B i)
    (hX : ((sepList η m g W₁ W₂ D₁ D₂ ω₁ ω₂ b₁ b₂ S β P t B).map Prod.snd).prod ≤ X)
    (hXmax : X ≤ Xmax) :
    radialEnergy (fun z => polynomial (radRow η m z hm hmLam hm2) false W₁ D₁ 0 ω₁ *
        polynomial (radRow η m z hm hmLam hm2) false W₂ D₂ 0 ω₂ *
        ∏ i, normalizedSlot η m 1 z (S i) (β i) t (P i)) keep Φ K ≤
      QuadraticInitialBound.diagonalControl Φ * (Kn*(X + Y^(1-δ)*X^δ) *
        ((idealDivisorConstant ε hε * X^ε)^(2 + Fintype.card ι) *
          ((sepList η m g W₁ W₂ D₁ D₂ ω₁ ω₂ b₁ b₂ S β P t B).map (fun q => q.1.mass)).prod)) := by
  set l := sepList η m g W₁ W₂ D₁ D₂ ω₁ ω₂ b₁ b₂ S β P t B with hl
  have hbounds : ∀ q ∈ l, q.1.NormLe q.2 ∧ 1 ≤ q.2 := by
    intro q hq
    simp only [hl, sepList, List.mem_append, List.mem_cons, List.mem_map, Finset.mem_toList,
      Finset.mem_univ, true_and, List.not_mem_nil, or_false] at hq
    rcases hq with (rfl | rfl) | ⟨i, rfl⟩
    · exact ⟨dyadPoly_normLe η m g W₁ D₁ ω₁ b₁, le_max_left _ _⟩
    · exact ⟨dyadPoly_normLe η m g W₂ D₂ ω₂ b₂, le_max_left _ _⟩
    · exact hB i
  have hN := OrdPoly.normLe_mono (OrdPoly.normLe_prod l hbounds) hX
  have h1 : 1 ≤ X := (OrdPoly.prod_bounds_ge_one l hbounds).trans hX
  have hF : ∀ u ∈ cores, polynomial (radRow η m (u * g^6) hm hmLam hm2) false W₁ D₁ 0 ω₁ *
      polynomial (radRow η m (u * g^6) hm hmLam hm2) false W₂ D₂ 0 ω₂ *
      ∏ i, normalizedSlot η m 1 (u * g^6) (S i) (β i) t (P i) =
        (OrdPoly.prod (l.map Prod.fst)).eval u := fun u hu =>
    sep_eval η m u g hm hmLam hm2 (hnz u hu) W₁ W₂ D₁ D₂ ω₁ ω₂ b₁ b₂ hD₁ hD₂ hs₁ hs₂ S β P t B
  have he := root_radial_energy_norm (fun z => polynomial (radRow η m z hm hmLam hm2) false W₁ D₁ 0 ω₁ *
      polynomial (radRow η m z hm hmLam hm2) false W₂ D₂ 0 ω₂ *
      ∏ i, normalizedSlot η m 1 z (S i) (β i) t (P i)) keep Φ K hΦ g cores hcover
    (OrdPoly.prod (l.map Prod.fst)) hF Y δ Kn Xmax X hnorm h1 hXmax hN
  have hm' := OrdPoly.mass_prod ε hε l hbounds X hX
  have hlen : l.length = 2 + Fintype.card ι := sepList_length η m g W₁ W₂ D₁ D₂ ω₁ ω₂ b₁ b₂ S β P t B
  rw [hlen] at hm'
  have hK0 : 0 ≤ Kn*(X + Y^(1-δ)*X^δ) := by
    have hK := hnorm.1
    have := Real.rpow_nonneg hY (1-δ)
    have := Real.rpow_nonneg (zero_le_one.trans h1) δ
    have : 0 ≤ X := zero_le_one.trans h1
    positivity
  refine he.trans ?_
  apply mul_le_mul_of_nonneg_left _ (QuadraticInitialBound.diagonalControl_nonneg Φ)
  exact mul_le_mul_of_nonneg_left hm' hK0

end
end QRH.ArviSelectedLeaf.R1
