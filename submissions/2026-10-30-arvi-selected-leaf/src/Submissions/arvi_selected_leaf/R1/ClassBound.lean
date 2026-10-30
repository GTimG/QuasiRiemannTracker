/-
Closed forms of the class energies.

For one root class, any row function that is the value at the core of a product of ordinary polynomials has
radial energy at most `diag Φ · 2Kn(X + Y) · (D_ε X^ε)^len · ∏ masses` (`list_class_energy`), from PR 93's
selected norm and `Y^{1-δ} X^δ ≤ X + Y`. This gives the direct bound (two dyadic polynomials and the slots)
and the short bound (one dyadic polynomial and the slots), with the dyadic masses `128 b L²` and the slot
masses `256 B²` of prime annulus pools.
-/
import Submissions.arvi_selected_leaf.R1.RootSum

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf.R1
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths CanonicalRowCompletion HeckeFamily HeckeDyadic ConcreteTraceCRT
open QuadraticInitialBound
open CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentSourceMass CenteredMomentOriginalRadialComparison
open Qrh.JointDetector Qrh.JointDetector.FineDetectorWords
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem rpow_mix_le (X Y δ : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Y^(1-δ) * X^δ ≤ X + Y := by
  rcases eq_or_lt_of_le (add_nonneg hX hY) with h0 | hpos
  · have hX0 : X = 0 := by linarith
    have hY0 : Y = 0 := by linarith
    subst hX0 hY0
    rcases eq_or_lt_of_le hδ0 with h | h
    · subst h; simp
    · rw [Real.zero_rpow h.ne']; simp
  · have h1 : Y^(1-δ) ≤ (X+Y)^(1-δ) := Real.rpow_le_rpow hY (by linarith) (by linarith)
    have h2 : X^δ ≤ (X+Y)^δ := Real.rpow_le_rpow hX (by linarith) hδ0
    calc Y^(1-δ) * X^δ ≤ (X+Y)^(1-δ) * (X+Y)^δ :=
          mul_le_mul h1 h2 (Real.rpow_nonneg hX _) (Real.rpow_nonneg hpos.le _)
      _ = X + Y := by rw [← Real.rpow_add hpos]; simp

/-- **The energy of a class whose rows are a product of ordinary polynomials in the core.** -/
theorem list_class_energy (cores : Finset O) (Y δ Kn Xmax X : ℝ) (hY : 0 ≤ Y) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hnorm : SelectedAllSourceNormBound cores Y δ Kn Xmax) (ε : ℝ) (hε : 0 < ε)
    (F : O → ℂ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hΦ : ∀ z : O, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) (g : O)
    (hcover : ∀ z, keep z → Φ (‖eisEmbedding z‖^2/K) ≠ 0 → ∃ u ∈ cores, z = u * g^6)
    (l : List (OrdPoly × ℝ)) (hl : ∀ q ∈ l, q.1.NormLe q.2 ∧ 1 ≤ q.2)
    (hF : ∀ u ∈ cores, F (u * g^6) = (OrdPoly.prod (l.map Prod.fst)).eval u)
    (hX : (l.map Prod.snd).prod ≤ X) (hXmax : X ≤ Xmax) :
    radialEnergy F keep Φ K ≤
      diagonalControl Φ * (2 * Kn * (X + Y)) *
        ((idealDivisorConstant ε hε * X^ε)^l.length * (l.map (fun q => q.1.mass)).prod) := by
  have hN := OrdPoly.normLe_mono (OrdPoly.normLe_prod l hl) hX
  have h1 : 1 ≤ X := (OrdPoly.prod_bounds_ge_one l hl).trans hX
  have he := root_radial_energy_norm F keep Φ K hΦ g cores hcover (OrdPoly.prod (l.map Prod.fst)) hF
    Y δ Kn Xmax X hnorm h1 hXmax hN
  have hm := OrdPoly.mass_prod ε hε l hl X hX
  have hK := hnorm.1
  have hX0 : 0 ≤ X := zero_le_one.trans h1
  have hmix := rpow_mix_le X Y δ hX0 hY hδ0 hδ1
  have hdiag := diagonalControl_nonneg Φ
  have hmass0 := (OrdPoly.prod (l.map Prod.fst)).mass_nonneg
  calc radialEnergy F keep Φ K
      ≤ diagonalControl Φ * (Kn * (X + Y^(1-δ) * X^δ) * (OrdPoly.prod (l.map Prod.fst)).mass) := he
    _ ≤ diagonalControl Φ * (2 * Kn * (X + Y) * (OrdPoly.prod (l.map Prod.fst)).mass) := by
        apply mul_le_mul_of_nonneg_left _ hdiag
        apply mul_le_mul_of_nonneg_right _ hmass0
        nlinarith
    _ ≤ diagonalControl Φ * (2 * Kn * (X + Y) *
          ((idealDivisorConstant ε hε * X^ε)^l.length * (l.map (fun q => q.1.mass)).prod)) := by
        apply mul_le_mul_of_nonneg_left _ hdiag
        exact mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

variable {ι : Type*} [Fintype ι]

theorem sepList_snd_prod (η : Character) (m g : O) (W₁ W₂ : ℝ → ℂ) (D₁ D₂ ω₁ ω₂ b₁ b₂ : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t : ℝ) (B : ι → ℝ) :
    ((sepList η m g W₁ W₂ D₁ D₂ ω₁ ω₂ b₁ b₂ S β P t B).map Prod.snd).prod =
      max 1 (b₁*D₁) * (max 1 (b₂*D₂) * ∏ i, B i) := by
  simp only [sepList, List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one, List.map_map, Function.comp_def]
  rw [Finset.prod_map_toList]
  ring

theorem sepList_mass_le (η : Character) (m g : O) (W₁ W₂ : ℝ → ℂ) (D₁ D₂ ω₁ ω₂ b₁ b₂ : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t : ℝ) (B : ι → ℝ)
    (m₁ m₂ : ℝ) (ms : ι → ℝ) (h₁ : (dyadPoly η m g W₁ D₁ ω₁ b₁).mass ≤ m₁)
    (h₂ : (dyadPoly η m g W₂ D₂ ω₂ b₂).mass ≤ m₂)
    (hs : ∀ i, (slotPoly η m g (S i) (β i) t (P i)).mass ≤ ms i) :
    ((sepList η m g W₁ W₂ D₁ D₂ ω₁ ω₂ b₁ b₂ S β P t B).map (fun q => q.1.mass)).prod ≤
      m₁ * (m₂ * ∏ i, ms i) := by
  simp only [sepList, List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one, List.map_map, Function.comp_def]
  rw [Finset.prod_map_toList]
  have hp : ∏ i, (slotPoly η m g (S i) (β i) t (P i)).mass ≤ ∏ i, ms i :=
    Finset.prod_le_prod₀ (fun i _ => OrdPoly.mass_nonneg _) (fun i _ => hs i)
  have h0₁ := (dyadPoly η m g W₁ D₁ ω₁ b₁).mass_nonneg
  have h0₂ := (dyadPoly η m g W₂ D₂ ω₂ b₂).mass_nonneg
  have h0p : 0 ≤ ∏ i, (slotPoly η m g (S i) (β i) t (P i)).mass :=
    Finset.prod_nonneg (fun i _ => OrdPoly.mass_nonneg _)
  rw [mul_assoc]
  exact mul_le_mul h₁ (mul_le_mul h₂ hp h0p (h0₂.trans h₂)) (mul_nonneg h0₂ h0p) (h0₁.trans h₁)

/-- **The direct class bound** (two dyadic polynomials and the slots). -/
theorem direct_class (cores : Finset O) (Y δ Kn Xmax X : ℝ) (hY : 0 ≤ Y) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hnorm : SelectedAllSourceNormBound cores Y δ Kn Xmax) (ε : ℝ) (hε : 0 < ε)
    (η : Character) (m g : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2:O) ∣ m)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hΦ : ∀ z : O, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re)
    (hcover : ∀ z, keep z → Φ (‖eisEmbedding z‖^2/K) ≠ 0 → ∃ u ∈ cores, z = u * g^6)
    (hnz : ∀ u ∈ cores, u * g^6 ≠ 0)
    (W₁ W₂ : ℝ → ℂ) (D₁ D₂ ω₁ ω₂ b₁ b₂ L₁ L₂ : ℝ) (hD₁ : 0 < D₁) (hD₂ : 0 < D₂) (hb₁ : 0 ≤ b₁)
    (hb₂ : 0 ≤ b₂) (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hW₁ : ∀ x, ‖W₁ x‖ ≤ L₁) (hW₂ : ∀ x, ‖W₂ x‖ ≤ L₂)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t : ℝ) (B ms : ι → ℝ)
    (hB : ∀ i, (slotPoly η m g (S i) (β i) t (P i)).NormLe (B i) ∧ 1 ≤ B i)
    (hms : ∀ i, (slotPoly η m g (S i) (β i) t (P i)).mass ≤ ms i)
    (hX : max 1 (b₁*D₁) * (max 1 (b₂*D₂) * ∏ i, B i) ≤ X) (hXmax : X ≤ Xmax) :
    radialEnergy (fun z => polynomial (radRow η m z hm hmLam hm2) false W₁ D₁ 0 ω₁ *
        polynomial (radRow η m z hm hmLam hm2) false W₂ D₂ 0 ω₂ *
        ∏ i, normalizedSlot η m 1 z (S i) (β i) t (P i)) keep Φ K ≤
      diagonalControl Φ * (2 * Kn * (X + Y)) *
        ((idealDivisorConstant ε hε * X^ε)^(2 + Fintype.card ι) *
          (128 * b₁ * L₁^2 * (128 * b₂ * L₂^2 * ∏ i, ms i))) := by
  set l := sepList η m g W₁ W₂ D₁ D₂ ω₁ ω₂ b₁ b₂ S β P t B with hl
  have hbounds : ∀ q ∈ l, q.1.NormLe q.2 ∧ 1 ≤ q.2 := by
    intro q hq
    simp only [hl, sepList, List.mem_append, List.mem_cons, List.mem_map, Finset.mem_toList,
      Finset.mem_univ, true_and, List.not_mem_nil, or_false] at hq
    rcases hq with (rfl | rfl) | ⟨i, rfl⟩
    · exact ⟨dyadPoly_normLe η m g W₁ D₁ ω₁ b₁, le_max_left _ _⟩
    · exact ⟨dyadPoly_normLe η m g W₂ D₂ ω₂ b₂, le_max_left _ _⟩
    · exact hB i
  have hF : ∀ u ∈ cores, polynomial (radRow η m (u * g^6) hm hmLam hm2) false W₁ D₁ 0 ω₁ *
      polynomial (radRow η m (u * g^6) hm hmLam hm2) false W₂ D₂ 0 ω₂ *
      ∏ i, normalizedSlot η m 1 (u * g^6) (S i) (β i) t (P i) =
        (OrdPoly.prod (l.map Prod.fst)).eval u := fun u hu =>
    sep_eval η m u g hm hmLam hm2 (hnz u hu) W₁ W₂ D₁ D₂ ω₁ ω₂ b₁ b₂ hD₁ hD₂ hs₁ hs₂ S β P t B
  have hXl : (l.map Prod.snd).prod ≤ X := by
    rw [hl, sepList_snd_prod]; exact hX
  have h := list_class_energy cores Y δ Kn Xmax X hY hδ0 hδ1 hnorm ε hε
    (fun z => polynomial (radRow η m z hm hmLam hm2) false W₁ D₁ 0 ω₁ *
      polynomial (radRow η m z hm hmLam hm2) false W₂ D₂ 0 ω₂ *
      ∏ i, normalizedSlot η m 1 z (S i) (β i) t (P i)) keep Φ K hΦ g hcover l
    hbounds hF hXl hXmax
  have hlen : l.length = 2 + Fintype.card ι := sepList_length η m g W₁ W₂ D₁ D₂ ω₁ ω₂ b₁ b₂ S β P t B
  rw [hlen] at h
  have hmass := sepList_mass_le η m g W₁ W₂ D₁ D₂ ω₁ ω₂ b₁ b₂ S β P t B _ _ ms
    (dyadPoly_mass_le η m g W₁ D₁ ω₁ b₁ L₁ hD₁ hb₁ hW₁)
    (dyadPoly_mass_le η m g W₂ D₂ ω₂ b₂ L₂ hD₂ hb₂ hW₂) hms
  refine h.trans ?_
  have h1 : 1 ≤ X := (OrdPoly.prod_bounds_ge_one l hbounds).trans hXl
  have hK := hnorm.1
  have hpre : 0 ≤ diagonalControl Φ * (2 * Kn * (X + Y)) := by
    have := diagonalControl_nonneg Φ
    have : 0 ≤ X + Y := by linarith
    positivity
  apply mul_le_mul_of_nonneg_left _ hpre
  have hD := idealDivisorConstant_pos ε hε
  have hXe : 0 ≤ X^ε := Real.rpow_nonneg (zero_le_one.trans h1) ε
  exact mul_le_mul_of_nonneg_left hmass (pow_nonneg (mul_nonneg hD.le hXe) _)

/-- The separated short polynomial at the root `g` (one dyadic polynomial and the slots). -/
def shortList (η : Character) (m g : O) (W : ℝ → ℂ) (D ω b : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t : ℝ) (B : ι → ℝ) :
    List (OrdPoly × ℝ) :=
  [(dyadPoly η m g W D ω b, max 1 (b*D))] ++
    (Finset.univ.toList.map (fun i => (slotPoly η m g (S i) (β i) t (P i), B i)))

/-- **The short class bound** (one dyadic polynomial and the slots). -/
theorem short_class (cores : Finset O) (Y δ Kn Xmax X : ℝ) (hY : 0 ≤ Y) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hnorm : SelectedAllSourceNormBound cores Y δ Kn Xmax) (ε : ℝ) (hε : 0 < ε)
    (η : Character) (m g : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2:O) ∣ m)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hΦ : ∀ z : O, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re)
    (hcover : ∀ z, keep z → Φ (‖eisEmbedding z‖^2/K) ≠ 0 → ∃ u ∈ cores, z = u * g^6)
    (hnz : ∀ u ∈ cores, u * g^6 ≠ 0)
    (W : ℝ → ℂ) (D ω b L : ℝ) (hD : 0 < D) (hb : 0 ≤ b) (hs : Function.support W ⊆ Set.Iic b)
    (hW : ∀ x, ‖W x‖ ≤ L)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t : ℝ) (B ms : ι → ℝ)
    (hB : ∀ i, (slotPoly η m g (S i) (β i) t (P i)).NormLe (B i) ∧ 1 ≤ B i)
    (hms : ∀ i, (slotPoly η m g (S i) (β i) t (P i)).mass ≤ ms i)
    (hX : max 1 (b*D) * ∏ i, B i ≤ X) (hXmax : X ≤ Xmax) :
    radialEnergy (fun z => polynomial (radRow η m z hm hmLam hm2) false W D 0 ω *
        ∏ i, normalizedSlot η m 1 z (S i) (β i) t (P i)) keep Φ K ≤
      diagonalControl Φ * (2 * Kn * (X + Y)) *
        ((idealDivisorConstant ε hε * X^ε)^(1 + Fintype.card ι) * (128 * b * L^2 * ∏ i, ms i)) := by
  set l := shortList η m g W D ω b S β P t B with hl
  have hbounds : ∀ q ∈ l, q.1.NormLe q.2 ∧ 1 ≤ q.2 := by
    intro q hq
    simp only [hl, shortList, List.mem_append, List.mem_cons, List.mem_map, Finset.mem_toList,
      Finset.mem_univ, true_and, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | ⟨i, rfl⟩
    · exact ⟨dyadPoly_normLe η m g W D ω b, le_max_left _ _⟩
    · exact hB i
  have hF : ∀ u ∈ cores, polynomial (radRow η m (u * g^6) hm hmLam hm2) false W D 0 ω *
      ∏ i, normalizedSlot η m 1 (u * g^6) (S i) (β i) t (P i) =
        (OrdPoly.prod (l.map Prod.fst)).eval u := by
    intro u hu
    rw [OrdPoly.eval_prod]
    simp only [hl, shortList, List.map_append, List.map_cons, List.map_nil, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one, List.map_map, Function.comp_def]
    rw [Finset.prod_map_toList]
    simp only [dyadPoly_eval η m u g hm hmLam hm2 (hnz u hu) W D ω b hD hs, slotPoly_eval]
  have hXl : (l.map Prod.snd).prod ≤ X := by
    simp only [hl, shortList, List.map_append, List.map_cons, List.map_nil, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one, List.map_map, Function.comp_def]
    rw [Finset.prod_map_toList]
    exact hX
  have h := list_class_energy cores Y δ Kn Xmax X hY hδ0 hδ1 hnorm ε hε
    (fun z => polynomial (radRow η m z hm hmLam hm2) false W D 0 ω *
      ∏ i, normalizedSlot η m 1 z (S i) (β i) t (P i)) keep Φ K hΦ g hcover l
    hbounds hF hXl hXmax
  have hlen : l.length = 1 + Fintype.card ι := by
    simp [hl, shortList, Finset.length_toList]
    omega
  rw [hlen] at h
  have hmass : (l.map (fun q => q.1.mass)).prod ≤ 128 * b * L^2 * ∏ i, ms i := by
    simp only [hl, shortList, List.map_append, List.map_cons, List.map_nil, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one, List.map_map, Function.comp_def]
    rw [Finset.prod_map_toList]
    have hp : ∏ i, (slotPoly η m g (S i) (β i) t (P i)).mass ≤ ∏ i, ms i :=
      Finset.prod_le_prod₀ (fun i _ => OrdPoly.mass_nonneg _) (fun i _ => hms i)
    have h0 := (dyadPoly η m g W D ω b).mass_nonneg
    have h0p : 0 ≤ ∏ i, (slotPoly η m g (S i) (β i) t (P i)).mass :=
      Finset.prod_nonneg (fun i _ => OrdPoly.mass_nonneg _)
    exact mul_le_mul (dyadPoly_mass_le η m g W D ω b L hD hb hW) hp h0p (by positivity)
  refine h.trans ?_
  have h1 : 1 ≤ X := (OrdPoly.prod_bounds_ge_one l hbounds).trans hXl
  have hK := hnorm.1
  have hpre : 0 ≤ diagonalControl Φ * (2 * Kn * (X + Y)) := by
    have := diagonalControl_nonneg Φ
    have : 0 ≤ X + Y := by linarith
    positivity
  apply mul_le_mul_of_nonneg_left _ hpre
  have hD := idealDivisorConstant_pos ε hε
  have hXe : 0 ≤ X^ε := Real.rpow_nonneg (zero_le_one.trans h1) ε
  exact mul_le_mul_of_nonneg_left hmass (pow_nonneg (mul_nonneg hD.le hXe) _)

end
end QRH.ArviSelectedLeaf.R1
