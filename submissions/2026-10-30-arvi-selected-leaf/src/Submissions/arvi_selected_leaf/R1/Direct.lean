/-
The direct per-root energy: at a fixed sixth root, the packed rows of the selected cores are bounded by PR 93's
selected all-source norm at the source bound of the whole row polynomial, times its coefficient mass.
-/
import Submissions.arvi_selected_leaf.R1.RowPoly
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeSlot

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf.R1
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalRowCompletion HeckeFamily
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentWholeSlotDeletion CenteredMomentRetainedEnergy CenteredMomentSourceMass
open Qrh.JointDetector Qrh.JointDetector.FineDetectorWords
local notation "O" => ActualEisensteinCubic.O

/-- **Energy of an ordinary polynomial under a selected all-source norm bound.** -/
theorem selected_energy_le (rows : Finset O) (Y δ Kn Xmax X : ℝ)
    (hnorm : SelectedAllSourceNormBound rows Y δ Kn Xmax) (p : OrdPoly) (hX1 : 1 ≤ X)
    (hXmax : X ≤ Xmax) (hp : p.NormLe X) :
    ∑ z ∈ rows, ‖p.eval z‖^2 ≤ Kn*(X + Y^(1-δ)*X^δ) * p.mass := by
  have h1 := OrdPoly.energy_le rows p
  have h2 := hnorm.2 X p.S hX1 hXmax (fun I hI => (hp I hI).2)
  exact h1.trans (mul_le_mul_of_nonneg_right h2 p.mass_nonneg)

variable {ι : Type*} [Fintype ι]

/-- The row polynomial with the norm bound of each factor. -/
def rowList (η : Character) (m g : O) (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ b₁ b₂ : ℝ) (B : ι → ℝ) : List (OrdPoly × ℝ) :=
  [(plainPoly η m g W₁ t X₁ b₁, max 1 (b₁*X₁)), (plainPoly η m g W₂ t X₂ b₂, max 1 (b₂*X₂))] ++
    (Finset.univ.toList.map (fun i => (slotPoly η m g (S i) (β i) t (P i), B i)))

theorem rowPoly_eq_list (η : Character) (m g : O) (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ b₁ b₂ : ℝ) (B : ι → ℝ) :
    rowPoly η m g W₁ W₂ S β P t X₁ X₂ b₁ b₂ =
      OrdPoly.prod ((rowList η m g W₁ W₂ S β P t X₁ X₂ b₁ b₂ B).map Prod.fst) := by
  simp only [rowPoly, rowList, List.map_append, List.map_cons, List.map_nil, List.map_map,
    Function.comp_def]

theorem plainPoly_normLe (η : Character) (m g : O) (W : ℝ → ℂ) (t X b : ℝ) :
    (plainPoly η m g W t X b).NormLe (max 1 (b*X)) := by
  intro I hI
  have h := (mem_idealBall (b*X) I).mp hI
  exact ⟨h.1, h.2.trans (le_max_right _ _)⟩

/-- The slot sources of a prime annulus pool are nonzero of norm at most `max 1 b · D`. -/
theorem slotPoly_normLe (η : Character) (m g : O) (rayM : Ideal O) (H : Subgroup (O ⧸ rayM)ˣ)
    (b D : ℝ) (β : Ideal O → ℂ) (t P : ℝ) (hD : 0 ≤ D) :
    (slotPoly η m g (CenteredMomentPrimeSlot.primePool rayM H b D) β t P).NormLe (max 1 (max 1 b * D)) := by
  intro I hI
  simp only [slotPoly, CenteredMomentPrimeSlot.primePool] at hI
  rw [Finset.mem_filter] at hI
  obtain ⟨hann, hprime, _⟩ := hI
  refine ⟨hprime.ne_zero, ?_⟩
  have h := (ConcretePrimeRowBridge.mem_idealsUpTo.mp hann).2
  have h' : (Ideal.absNorm I : ℝ) ≤ max 1 b * D :=
    (Nat.cast_le.mpr h).trans (Nat.floor_le (by positivity))
  exact h'.trans (le_max_right _ _)

/-- Mass of a normalized plain sum: at most `128·max(1,bX)·L²/X`. -/
theorem plainPoly_mass_le (η : Character) (m g : O) (W : ℝ → ℂ) (t X b L : ℝ) (hX : 0 < X)
    (hW : ∀ x, ‖W x‖ ≤ L) :
    (plainPoly η m g W t X b).mass ≤ 128 * max 1 (b*X) * L^2 / X := by
  have hL : 0 ≤ L := (norm_nonneg _).trans (hW 0)
  have hterm : ∀ I : (idealBall (b*X) : Finset (Ideal O)),
      ‖(Real.sqrt X : ℂ)⁻¹ * (rootCommon η m g t I.val * W ((Ideal.absNorm I.val : ℝ)/X))‖^2 ≤
        L^2 / X := by
    intro I
    have h1 := rootCommon_norm_le η m g t I.val
    have h2 := hW ((Ideal.absNorm I.val : ℝ)/X)
    rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have hs : (Real.sqrt X)⁻¹^2 = 1/X := by
      rw [inv_pow, Real.sq_sqrt hX.le, one_div]
    have hprod : ‖rootCommon η m g t I.val‖ * ‖W ((Ideal.absNorm I.val : ℝ)/X)‖ ≤ L := by
      calc _ ≤ 1 * L := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = L := one_mul L
    have hprod0 : 0 ≤ ‖rootCommon η m g t I.val‖ * ‖W ((Ideal.absNorm I.val : ℝ)/X)‖ := by positivity
    calc ((Real.sqrt X)⁻¹ * (‖rootCommon η m g t I.val‖ * ‖W ((Ideal.absNorm I.val : ℝ)/X)‖))^2
        = (Real.sqrt X)⁻¹^2 * (‖rootCommon η m g t I.val‖ * ‖W ((Ideal.absNorm I.val : ℝ)/X)‖)^2 := by
          ring
      _ ≤ (1/X) * L^2 := by
          rw [hs]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hprod0 hprod 2) (by positivity)
      _ = L^2/X := by ring
  have hcard : ((idealBall (b*X)).card : ℝ) ≤ 128 * max 1 (b*X) :=
    DescentFiberCost.finite_ideal_count_real (idealBall (b*X)) (max 1 (b*X)) (le_max_left _ _)
      (fun I hI => ((mem_idealBall (b*X) I).mp hI).1)
      (fun I hI => ((mem_idealBall (b*X) I).mp hI).2.trans (le_max_right _ _))
  calc (plainPoly η m g W t X b).mass
      ≤ ∑ _I : (idealBall (b*X) : Finset (Ideal O)), L^2/X := Finset.sum_le_sum fun I _ => hterm I
    _ = ((idealBall (b*X)).card : ℝ) * (L^2/X) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ 128 * max 1 (b*X) * (L^2/X) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- Mass of a normalized slot with coefficients bounded by `Bβ` on a source set of at most `N` ideals. -/
theorem slotPoly_mass_le (η : Character) (m g : O) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (t P Bβ N : ℝ) (hP : 0 < P) (hβ : ∀ I ∈ S, ‖β I‖ ≤ Bβ) (hN : (S.card : ℝ) ≤ N) :
    (slotPoly η m g S β t P).mass ≤ N * Bβ^2 / P := by
  have hterm : ∀ I : S, ‖(Real.sqrt P : ℂ)⁻¹ * β I.val * rootCommon η m g t I.val‖^2 ≤ Bβ^2 / P := by
    intro I
    have h1 := rootCommon_norm_le η m g t I.val
    have h2 := hβ I.val I.property
    have hB : 0 ≤ Bβ := (norm_nonneg _).trans h2
    rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have hs : (Real.sqrt P)⁻¹^2 = 1/P := by
      rw [inv_pow, Real.sq_sqrt hP.le, one_div]
    have hprod : ‖β I.val‖ * ‖rootCommon η m g t I.val‖ ≤ Bβ := by
      calc _ ≤ Bβ * 1 := mul_le_mul h2 h1 (norm_nonneg _) hB
        _ = Bβ := mul_one Bβ
    have hprod0 : 0 ≤ ‖β I.val‖ * ‖rootCommon η m g t I.val‖ := by positivity
    calc ((Real.sqrt P)⁻¹ * ‖β I.val‖ * ‖rootCommon η m g t I.val‖)^2
        = (Real.sqrt P)⁻¹^2 * (‖β I.val‖ * ‖rootCommon η m g t I.val‖)^2 := by ring
      _ ≤ (1/P) * Bβ^2 := by
          rw [hs]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hprod0 hprod 2) (by positivity)
      _ = Bβ^2/P := by ring
  calc (slotPoly η m g S β t P).mass ≤ ∑ _I : S, Bβ^2/P := Finset.sum_le_sum fun I _ => hterm I
    _ = (S.card : ℝ) * (Bβ^2/P) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ N * (Bβ^2/P) := mul_le_mul_of_nonneg_right hN (by positivity)
    _ = _ := by ring

/-- **The direct per-root energy.** -/
theorem direct_root (rows : Finset O) (Y δ Kn Xmax : ℝ) (hY : 0 ≤ Y)
    (hnorm : SelectedAllSourceNormBound rows Y δ Kn Xmax) (ε : ℝ) (hε : 0 < ε)
    (η : Character) (m g : O) (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (P : ι → ℝ) (t X₁ X₂ b₁ b₂ : ℝ) (B : ι → ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀ i, 0 < P i)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hB : ∀ i, (slotPoly η m g (S i) (β i) t (P i)).NormLe (B i) ∧ 1 ≤ B i)
    (hXmax : ((rowList η m g W₁ W₂ S β P t X₁ X₂ b₁ b₂ B).map Prod.snd).prod ≤ Xmax) :
    ∑ u ∈ rows, ‖positiveSlotRow η m 1 (u * g^6) W₁ W₂ S β P t X₁ X₂‖^2 ≤
      Kn*(((rowList η m g W₁ W₂ S β P t X₁ X₂ b₁ b₂ B).map Prod.snd).prod +
        Y^(1-δ)*((rowList η m g W₁ W₂ S β P t X₁ X₂ b₁ b₂ B).map Prod.snd).prod^δ) *
      ((idealDivisorConstant ε hε *
          ((rowList η m g W₁ W₂ S β P t X₁ X₂ b₁ b₂ B).map Prod.snd).prod^ε)^
          (rowList η m g W₁ W₂ S β P t X₁ X₂ b₁ b₂ B).length *
        ((rowList η m g W₁ W₂ S β P t X₁ X₂ b₁ b₂ B).map (fun q => q.1.mass)).prod) := by
  set l := rowList η m g W₁ W₂ S β P t X₁ X₂ b₁ b₂ B with hl
  have hbounds : ∀ q ∈ l, q.1.NormLe q.2 ∧ 1 ≤ q.2 := by
    intro q hq
    simp only [hl, rowList, List.mem_append, List.mem_cons, List.mem_map, Finset.mem_toList,
      Finset.mem_univ, true_and, List.not_mem_nil, or_false] at hq
    rcases hq with (rfl | rfl) | ⟨i, rfl⟩
    · exact ⟨plainPoly_normLe η m g W₁ t X₁ b₁, le_max_left _ _⟩
    · exact ⟨plainPoly_normLe η m g W₂ t X₂ b₂, le_max_left _ _⟩
    · exact hB i
  have heval : ∀ u : O, positiveSlotRow η m 1 (u * g^6) W₁ W₂ S β P t X₁ X₂ =
      (OrdPoly.prod (l.map Prod.fst)).eval u := by
    intro u
    rw [positiveSlotRow_root η m u g W₁ W₂ S β P t X₁ X₂ b₁ b₂ hX₁ hX₂ hP hs₁ hs₂, rowPoly_eq_list _ _ _ _ _ _ _ _ _ _ _ _ _ B]
  simp_rw [heval]
  have hN := OrdPoly.normLe_prod l hbounds
  have h1 := OrdPoly.prod_bounds_ge_one l hbounds
  have he := selected_energy_le rows Y δ Kn Xmax _ hnorm _ h1 hXmax hN
  have hm := OrdPoly.mass_prod ε hε l hbounds _ le_rfl
  have hK0 : 0 ≤ Kn*((l.map Prod.snd).prod + Y^(1-δ)*(l.map Prod.snd).prod^δ) := by
    have hK := hnorm.1
    have hX0 : 0 ≤ (l.map Prod.snd).prod := by linarith
    have := Real.rpow_nonneg hY (1-δ)
    have := Real.rpow_nonneg hX0 δ
    positivity
  exact he.trans (mul_le_mul_of_nonneg_left hm hK0)

end
end QRH.ArviSelectedLeaf.R1
