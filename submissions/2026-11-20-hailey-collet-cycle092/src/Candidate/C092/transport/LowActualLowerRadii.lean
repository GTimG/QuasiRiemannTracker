/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   The genuine lower near-H low-response step on a finite source bank. -/
import Candidate.C092.transport.LowActualBankPayment

set_option autoImplicit false
namespace QRH.Cycle092.LowActual
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths
open QRH.Cycle092.NativeStrip QRH.Record12518109Source QRH.Record12518109Existence
open QRH.Cycle092.WholeSlot QRH.Cycle090 QRH.SourceCertificate
open HeckeFamily CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open OAI.SevenEighths.Cycle61Moment CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

/-- A preceding genuine source closes the original positive low-response
energy at H. The original mesh precedes every finite mark and label; its
buffer precedes the slot supplier's constant; all energy constants precede
U, whole-slot widths, phases, ordinary tests and lengths. -/
theorem low_step_below_H {n y e : ℝ}
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (cover : EarlierCover OpenWidth y)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY)
    (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (he0 : 0 ≤ e) (he1 : e ≤ (responseUpper : ℝ))
    (hp : e*max 0 (lowBracketAt y) < (u-rho : ℚ)) :
    ∃ mesh : ℝ, 0 < mesh ∧
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∃ buffer : ℝ, 0 < buffer ∧
    ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
      (hHr : RayOrthogonality.globalUnits rayM ≤ Hr),
    ∀ (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1 : ℝ) 2 →
    ∀ bΦ : ℝ, 2 ≤ bΦ → ∀ (η η₀ : Character) (Q : Ideal O),
      Q ≤ rayM → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∀ Cslot : ℝ, 0 ≤ Cslot →
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ U : ℝ in atTop,
    ∀ V : ℝ, (98/100 : ℝ) ≤ V → V ≤ (H : ℝ) →
    ∀ (θ : Slot → RayQuotient.Characters rayM Hr) (w σ v : Slot → ℝ) (t height : ℝ),
      (∀ j, 0 ≤ w j) → (∀ j, w j ≤ mesh) →
      (∀ j, (33/50 : ℝ) ≤ σ j) → (∀ j, σ j ≤ (33/50 : ℝ)) →
      0 ≤ height → (∀ j, |v j| ≤ height) →
    ∀ (Φ : 𝓢(ℝ,ℂ)), Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ →
      (∀ x, 0 ≤ (Φ x).re) → ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),
      0 < X₁ → 0 < X₂ →
      Box (n/V) (y/V) 0
        (length (U^V) X₁) (length (U^V) X₂) 0 →
      (∑ j, w j) ≤ sourceWidth n y-(u : ℝ) →
      energy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
        (originalPools rayM Hr 2 U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
        (fun j => U^(w j)) X₁ X₂
        (fun z => initialKeep η (internalQ Q η₀) z ∧
          LowRows Finset.univ η (fixedBadMask*idealGenerator 1) 1 t U e (Cslot*U^buffer) w
            (originalPools rayM Hr 2 U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
            (fun j => U^(w j)) z) Φ (U^V) ≤
        C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
          (1+|t|+height)^degree*U^(V+(u : ℝ)-(rho : ℝ)/4+(5/6)*max 0 ((H : ℝ)-V)) := by
  let δ : ℝ := (rho : ℝ)/(16*(responseUpper : ℝ))
  have hδ : 0 < δ := by norm_num [δ,rho,responseUpper]
  have hδfee : 3*(responseUpper : ℝ)*δ ≤ (rho : ℝ)/2 := by norm_num [δ,rho,responseUpper]
  have hminH : (98/100 : ℝ) ≤ (H : ℝ) := by norm_num [H,u]
  obtain ⟨bank,hbank,hnet⟩ := finite_left_radius_bank hminH hδ
  let decrement (r : ℝ) := min (radiusWidth n y r/2) δ
  let l (r : ℝ) := radiusWidth n y r-decrement r
  have hwidth (r : ℝ) (hr : r ∈ bank) := radius_width_pos hy1 hn1 (hbank r hr).1
  have hd (r : ℝ) (hr : r ∈ bank) : 0 < decrement r := lt_min (by linarith [hwidth r hr]) hδ
  have hdw (r : ℝ) (hr : r ∈ bank) : decrement r < radiusWidth n y r :=
    (min_le_left _ _).trans_lt (by linarith [hwidth r hr])
  have hl (r : ℝ) (hr : r ∈ bank) : 0 < l r := sub_pos.mpr (hdw r hr)
  have hprevious (r : ℝ) (hr : r ∈ bank) : UniformBox (n/r) (y/r) (l r) :=
    radius_bank_source hβ cover hy0 hy1 hn0 hn1 (hbank r hr).1 (hbank r hr).2
      (l r) (hl r hr).le (sub_lt_self _ (hd r hr))
  let εsrc : ℝ := (rho : ℝ)/16
  have hεsrc : 0 < εsrc := by norm_num [εsrc,rho]
  obtain ⟨sourceMesh,hsm,hsource⟩ := finite_bank_mesh bank (fun r => n/r) (fun r => y/r) l hprevious hεsrc
  let mesh := min δ ((98/100 : ℝ)*sourceMesh)
  have hm : 0 < mesh := lt_min hδ (mul_pos (by norm_num) hsm)
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _
  let buffer : ℝ := (rho : ℝ)/(16*(1+(Fintype.card Slot : ℝ)))
  have hb : 0 < buffer := by
    have hrho : (0 : ℝ) < (rho : ℝ) := by norm_num [rho]
    dsimp [buffer]; positivity
  have hbfee : buffer*(Fintype.card Slot : ℝ) ≤ (rho : ℝ)/16 := by
    have hEq : buffer*(16*(1+(Fintype.card Slot : ℝ))) = (rho : ℝ) := by
      dsimp [buffer]; field_simp
    nlinarith only [hEq,hb]
  refine ⟨buffer,hb,?_⟩
  intro rayM _ Hr hHr W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72 Cslot hCslot
  obtain ⟨degree,controls,Csrc,hCsrc,hsourceU⟩ := finite_bank_metadata bank
    (fun r => n/r) (fun r => y/r) l hsource (by norm_num : (0 : ℝ) < 98/100)
    Slot rayM Hr hHr W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  let C := (max 1 Cslot)^(Fintype.card Slot)*Csrc
  have hC : 0 < C := mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _) hCsrc
  refine ⟨degree,controls,C,hC,?_⟩
  filter_upwards [hsourceU,eventually_ge_atTop (1 : ℝ)] with U hsourceU hU
  intro V hVmin hVH
  have hV : 0 < V := (by norm_num : (0 : ℝ) < 98/100).trans_le hVmin
  have hV1 : V ≤ 1 := hVH.trans H_real_bounds.2.le
  obtain ⟨r,hr,hrV,hrδ⟩ := hnet V hVmin hVH
  have hrpos : 0 < r := (by norm_num : (0 : ℝ) < 98/100).trans_le (hbank r hr).1
  intro θ w σ v t height hw hwm hσlo hσhi hh hv Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ hbox hwidthU
  obtain ⟨F,hF,hdel,hex,hboxes⟩ := selection_with_source_boxes w mesh V (l r) hw hwm hm.le hV.le (hl r hr).le
  have hcard : (Finset.univ\F).card ≤ Fintype.card Slot := by
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_univ)
  have herror : buffer*((Finset.univ\F).card : ℝ)+V*εsrc ≤ (rho : ℝ)/4 := by
    have hc : ((Finset.univ\F).card : ℝ) ≤ (Fintype.card Slot : ℝ) := by exact_mod_cast hcard
    have h := mul_le_mul_of_nonneg_left hc hb.le
    have hvfee : V*εsrc ≤ (rho : ℝ)/16 := by
      have h := mul_le_mul_of_nonneg_right hV1 hεsrc.le
      simpa [εsrc] using h
    linarith [show (0 : ℝ) < (rho : ℝ) by norm_num [rho]]
  have hfee := lower_bank_fee he0 he1 hδ.le (sub_nonneg.mpr hrV) hrδ.le hV1 (hd r hr).le
    (min_le_right _ _) hm.le (min_le_left _ _) hδfee
  have hprice := lower_bank_paid (n := n) hy0 hy1 he0 he1 hp hrpos hrV hVH
    (hwidth r hr).le (hd r hr).le hm.le hfee
  have hwm' (j : Slot) : w j/V ≤ sourceMesh :=
    mesh_rescale (by norm_num : (0 : ℝ) < 98/100) hVmin hsm.le (min_le_right _ _) (hwm j)
  have hnc : n/V ≤ n/r := by
    apply (div_le_div_iff₀ hV hrpos).2
    have hnpos : 0 ≤ n := (source_domain.1.le.trans hy0).trans hn0
    nlinarith only [mul_nonneg hnpos (sub_nonneg.mpr hrV)]
  have hyc : y/V ≤ y/r := by
    apply (div_le_div_iff₀ hV hrpos).2
    have hypos := source_domain.1.le.trans hy0
    nlinarith only [mul_nonneg hypos (sub_nonneg.mpr hrV)]
  have hbox' : Box (n/r) (y/r) 0 (length (U^V) X₁) (length (U^V) X₂) 0 := by
    refine ⟨hbox.1,hbox.2.1,?_,hbox.2.2.2⟩
    rcases hbox.2.2.1 with h | h
    · exact Or.inl ⟨h.1.trans hnc,h.2.trans hyc⟩
    · exact Or.inr ⟨h.1.trans hyc,h.2.trans hnc⟩
  have hE := radial_low_energy (e := e) rayM Hr hHr (hsourceU V hVmin r hr) F θ w σ v t height mesh
    hw hwm' hσlo hσhi hh hv Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ hU hV hCslot hCsrc.le he0
    (hboxes _ _ _ _ hbox') hwidthU hdel hprice herror
  have hc : Cslot^(Finset.univ\F).card*Csrc ≤ C := by
    dsimp [C]
    apply mul_le_mul_of_nonneg_right _ hCsrc.le
    calc
      _ ≤ (max 1 Cslot)^(Finset.univ\F).card := by gcongr; exact le_max_right _ _
      _ ≤ (max 1 Cslot)^(Fintype.card Slot) := by gcongr; exact le_max_left _ _
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hheight : 0 ≤ (1+|t|+height)^degree := by positivity
  have hmul := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
      (1+|t|+height)^degree*U^(V+(u : ℝ)-(rho : ℝ)/4+(5/6)*max 0 ((H : ℝ)-V)) by positivity)
  calc
    _ ≤ _ := hE
    _ ≤ _ := by convert hmul using 1 <;> ring

end
end QRH.Cycle092.LowActual
