/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual independent-pair low P3 branch uniformly at every V>=H.
The earlier source caps are frozen at n/H,y/H; all live lengths stay original. -/
import Candidate.C092.transport.StrongPairLowBank
import Candidate.C092.transport.LowActualUpperRadii

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open OAI.SevenEighths.Cycle61Moment
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
open QRH.Record12518109Source QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.LowActual
local notation "O" => ActualEisensteinCubic.O

theorem low_pair_near_radii {n y e Vmax : ℝ}
    (hmax : (98/100:ℝ) ≤ Vmax) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (cover : EarlierCover PairOpenWidth y)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (he0 : 0 ≤ e) (he1 : e ≤ (responseUpper:ℝ))
    (hp : e*max 0 (lowBracketAt y) < (u-rho:ℚ)) :
    ∃ mesh : ℝ,0 < mesh ∧
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∃ buffer : ℝ,0 < buffer ∧
    ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
      (hHr : RayOrthogonality.globalUnits rayM ≤ Hr),
    ∀ W : ℝ→ℂ,ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1:ℝ) 2 →
    ∀ bΦ : ℝ,2 ≤ bΦ → Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ →
    ∀ (η₁ η₂ η₀₁ η₀₂ : Character) (Q₁ Q₂ : Ideal O),
      Q₁ ≤ rayM → internalQ Q₁ η₀₁ ≠ 0 → internalQ Q₁ η₀₁ ≠ ⊤ → internalQ Q₁ η₀₁ ≤ Ideal.span {(72:O)} →
      Q₂ ≤ rayM → internalQ Q₂ η₀₂ ≠ 0 → internalQ Q₂ η₀₂ ≠ ⊤ → internalQ Q₂ η₀₂ ≤ Ideal.span {(72:O)} →
    ∀ Cslot : ℝ,0 ≤ Cslot →
    ∃ degree : ℕ,∃ controls : Finset (ℕ×ℕ),∃ C : ℝ,0 < C ∧
    ∀ᶠ U : ℝ in atTop,∀ V : ℝ,(98/100:ℝ) ≤ V → V ≤ Vmax →
    ∀ (θ₁ θ₂ : Slot→RayQuotient.Characters rayM Hr) (w σ₁ σ₂ v₁ v₂ : Slot→ℝ)
      (t₁ t₂ height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ mesh) →
      (∀ i,(33/50:ℝ) ≤ σ₁ i) → (∀ i,σ₁ i ≤ (33/50:ℝ)) →
      (∀ i,(33/50:ℝ) ≤ σ₂ i) → (∀ i,σ₂ i ≤ (33/50:ℝ)) →
      0 ≤ height → (∀ i,|v₁ i| ≤ height) → (∀ i,|v₂ i| ≤ height) →
      (∑ i,w i) ≤ sourceWidth n y-(u:ℝ) →
    ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),0 < X₁ → 0 < X₂ →
      length U X₁ ≤ n → length U X₂ ≤ y →
    ∀ (s : Finset FreeRow) (mark : Slot→FreeRow→ℂ),
      (∀ u∈s,initialKeep η₁ (internalQ Q₁ η₀₁) u.val) →
      (∀ u∈s,initialKeep η₂ (internalQ Q₂ η₀₂) u.val) →
      (∀ u∈s,rowNorm u ≤ U^V) →
      (∀ u∈s,∀ i,‖mark i u‖=
        ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools rayM Hr 2 U w i) (originalCoefficients rayM Hr hHr η₀₁ θ₁ W U w σ₁ v₁ i) t₁ (U^(w i))‖) →
      (∀ u∈s,∀ i,‖mark i u‖=
        ‖normalizedSlot η₂ (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools rayM Hr 2 U w i) (originalCoefficients rayM Hr hHr η₀₂ θ₂ W U w σ₂ v₂ i) t₂ (U^(w i))‖) →
      (∀ u∈s,∀ i,‖mark i u‖^2 ≤ (Cslot*U^buffer)*U^(e*w i)) →
    finiteEnergy s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
      C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
        (1+|t₁|+|t₂|+height)^degree*U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V)) := by
  let δ : ℝ := (rho : ℝ)/(16*(responseUpper : ℝ))
  have hδ : 0 < δ := by norm_num [δ,rho,responseUpper]
  have hδfee : 3*(responseUpper : ℝ)*δ ≤ (rho : ℝ)/2 := by norm_num [δ,rho,responseUpper]
  have hminH : (98/100 : ℝ) ≤ (H : ℝ) := by norm_num [H,u]
  obtain ⟨bank0,hbank0,hnet0⟩ := finite_left_radius_bank hminH hδ
  let bank := insert (H : ℝ) bank0
  have hbank (r : ℝ) (hr : r ∈ bank) : (98/100 : ℝ) ≤ r ∧ r ≤ (H : ℝ) := by
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact ⟨hminH,le_rfl⟩
    · exact hbank0 r hr
  have hnet (V : ℝ) (hlo : (98/100 : ℝ) ≤ V) (hhi : V ≤ (H : ℝ)) :
      ∃ r ∈ bank, r ≤ V ∧ V-r < δ := by
    obtain ⟨r,hr,hV,hδr⟩ := hnet0 V hlo hhi
    exact ⟨r,Finset.mem_insert_of_mem hr,hV,hδr⟩
  let decrement (r : ℝ) := min (radiusWidth n y r/2) δ
  let l (r : ℝ) := radiusWidth n y r-decrement r
  have hwidth (r : ℝ) (hr : r ∈ bank) := radius_width_pos hy1 hn1 (hbank r hr).1
  have hd (r : ℝ) (hr : r ∈ bank) : 0 < decrement r := lt_min (by linarith [hwidth r hr]) hδ
  have hdw (r : ℝ) (hr : r ∈ bank) : decrement r < radiusWidth n y r :=
    (min_le_left _ _).trans_lt (by linarith [hwidth r hr])
  have hl (r : ℝ) (hr : r ∈ bank) : 0 < l r := sub_pos.mpr (hdw r hr)
  have hprevious (r : ℝ) (hr : r ∈ bank) : PairUniformBox (n/r) (y/r) (l r) :=
    pair_radius_bank_source hβ cover hy0 hy1 hn0 hn1 (hbank r hr).1 (hbank r hr).2
      (l r) (hl r hr).le (sub_lt_self _ (hd r hr))
  let εsrc : ℝ := (rho : ℝ)/(16*Vmax)
  have hmaxpos : 0 < Vmax := (by norm_num : (0 : ℝ) < 98/100).trans_le hmax
  have hεsrc : 0 < εsrc := div_pos (by norm_num [rho]) (by positivity)
  have hεfee : Vmax*εsrc = (rho : ℝ)/16 := by dsimp [εsrc]; field_simp
  obtain ⟨sourceMesh,hsm,hsource⟩ := pair_finite_bank_mesh bank (fun r => n/r) (fun r => y/r) l hprevious hεsrc
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
  intro rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72 Cslot hCslot
  obtain ⟨degree,controls,Csrc,hCsrc,hsourceU⟩ := pair_finite_bank_metadata bank
    (fun r => n/r) (fun r => y/r) l hsource (by norm_num : (0 : ℝ) < 98/100)
    Slot rayM Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  let C := (max 1 Cslot)^(Fintype.card Slot)*Csrc
  have hC : 0 < C := mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _) hCsrc
  refine ⟨degree,controls,C,hC,?_⟩
  filter_upwards [hsourceU,eventually_gt_atTop (1 : ℝ)] with U hsourceU hU
  intro V hVmin hVmax
  have hV : 0 < V := (by norm_num : (0 : ℝ) < 98/100).trans_le hVmin
  have hchoice : ∃ r ∈ bank, r ≤ V ∧
      ((V ≤ (H : ℝ) ∧ V-r < δ) ∨ ((H : ℝ) ≤ V ∧ r = (H : ℝ))) := by
    by_cases hVH : V ≤ (H : ℝ)
    · obtain ⟨r,hr,hrV,hrδ⟩ := hnet V hVmin hVH
      exact ⟨r,hr,hrV,Or.inl ⟨hVH,hrδ⟩⟩
    · exact ⟨(H : ℝ),Finset.mem_insert_self _ _,(le_of_not_ge hVH),Or.inr ⟨le_of_not_ge hVH,rfl⟩⟩
  obtain ⟨r,hr,hrV,hsector⟩ := hchoice
  have hrpos : 0 < r := (by norm_num : (0 : ℝ) < 98/100).trans_le (hbank r hr).1
  intro θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi hh hv₁ hv₂ hwidthU
    p X₁ X₂ hX₁ hX₂ hXN hXY s mark hk₁ hk₂ hy hmark₁ hmark₂ hlow
  obtain ⟨F,hF,hdel,_⟩ := select_before_rows w mesh (V*l r) hw hwm hm.le (mul_nonneg hV.le (hl r hr).le)
  have hcard : (Finset.univ\F).card ≤ Fintype.card Slot := by
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_univ)
  have herror : buffer*((Finset.univ\F).card : ℝ)+V*εsrc ≤ (rho : ℝ)/4 := by
    have hc : ((Finset.univ\F).card : ℝ) ≤ (Fintype.card Slot : ℝ) := by exact_mod_cast hcard
    have h := mul_le_mul_of_nonneg_left hc hb.le
    have hvfee : V*εsrc ≤ (rho : ℝ)/16 := by
      have h := mul_le_mul_of_nonneg_right hVmax hεsrc.le
      simpa [hεfee] using h
    linarith [show (0 : ℝ) < (rho : ℝ) by norm_num [rho]]
  have hprice : e*max 0 (sourceWidth n y-(u : ℝ)-V*(l r)+mesh) <
      (u : ℝ)-(rho : ℝ)/2+(5/6)*max 0 ((H : ℝ)-V) := by
    rcases hsector with ⟨hVH,hrδ⟩ | ⟨hHV,rfl⟩
    · have hV1 : V ≤ 1 := hVH.trans H_real_bounds.2.le
      have hfee := lower_bank_fee he0 he1 hδ.le (sub_nonneg.mpr hrV) hrδ.le hV1 (hd r hr).le
        (min_le_right _ _) hm.le (min_le_left _ _) hδfee
      exact lower_bank_paid (n := n) hy0 hy1 he0 he1 hp hrpos hrV hVH
        (hwidth r hr).le (hd r hr).le hm.le hfee
    · have hfee := lower_bank_fee he0 he1 hδ.le (by norm_num : (0 : ℝ) ≤ (H : ℝ)-(H : ℝ))
        (by linarith : (H : ℝ)-(H : ℝ) ≤ δ) H_real_bounds.2.le (hd (H : ℝ) hr).le
        (min_le_right _ _) hm.le (min_le_left _ _) hδfee
      have hpriceH := lower_bank_paid (n := n) hy0 hy1 he0 he1 hp H_real_bounds.1 le_rfl le_rfl
        (hwidth (H : ℝ) hr).le (hd (H : ℝ) hr).le hm.le hfee
      have hcap := mul_le_mul_of_nonneg_right hHV (hl (H : ℝ) hr).le
      have hcost : e*max 0 (sourceWidth n y-(u : ℝ)-V*l (H : ℝ)+mesh) ≤
          e*max 0 (sourceWidth n y-(u : ℝ)-(H : ℝ)*l (H : ℝ)+mesh) :=
        mul_le_mul_of_nonneg_left (max_le_max_left 0 (by linarith only [hcap])) he0
      have hmax0 : max 0 ((H : ℝ)-V) = 0 := max_eq_left (sub_nonpos.mpr hHV)
      simpa [hmax0] using hcost.trans_lt (by simpa using hpriceH)
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
  have hNX : length (U^V) X₁ ≤ n/r := by
    rw [length_rpow_base U X₁ V (zero_lt_one.trans hU)]
    exact (div_le_div_of_nonneg_right hXN hV.le).trans hnc
  have hYX : length (U^V) X₂ ≤ y/r := by
    rw [length_rpow_base U X₂ V (zero_lt_one.trans hU)]
    exact (div_le_div_of_nonneg_right hXY hV.le).trans hyc
  have hE := low_pair_paid (allowance:=(5/6)*max 0 ((H:ℝ)-V)) rayM Hr hHr
    (hsourceU V hVmin r hr) F θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm'
    hσ₁lo hσ₁hi hσ₂lo hσ₂hi hh hv₁ hv₂ hF hU.le hV hCsrc.le hCslot he0
    hwidthU hdel hprice herror p X₁ X₂ hX₁ hX₂ hNX hYX s mark hk₁ hk₂ hy
    (fun u hu i _=>hmark₁ u hu i) (fun u hu i _=>hmark₂ u hu i) (fun u hu i _=>hlow u hu i)
  have hc : Cslot^(Finset.univ\F).card*Csrc ≤ C := by
    dsimp [C]
    apply mul_le_mul_of_nonneg_right _ hCsrc.le
    calc
      _ ≤ (max 1 Cslot)^(Finset.univ\F).card := by gcongr; exact le_max_right _ _
      _ ≤ (max 1 Cslot)^(Fintype.card Slot) := by gcongr; exact le_max_left _ _
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  have hheight : 0 ≤ (1+|t₁|+|t₂|+height)^degree := by positivity
  have hmul := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
      (1+|t₁|+|t₂|+height)^degree*U^(V+(u : ℝ)-(rho : ℝ)/4+(5/6)*max 0 ((H : ℝ)-V)) by positivity)
  calc
    _ ≤ _ := hE
    _ ≤ _ := by convert hmul using 1 <;> ring

#print axioms low_pair_near_radii
end
end QRH.Cycle092.StrongPair
