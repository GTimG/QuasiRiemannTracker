/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual native source and whole-slot energy transport retain their original
OpenAI/Collet/Sil/Bebel/Levy/Gao attribution through the imports. -/
import Candidate.C092.transport.SmallCoreNative
import Candidate.C092.transport.LowActualRadialEnergy

set_option autoImplicit false
namespace QRH.Cycle092.SmallCore
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

variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (rayM : Ideal O) [NeZero rayM]
local instance c092LocalInst_Candidate_C092_transport_SmallCoreEnergy_07401ce6243c84c5_001 : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (Hr : Subgroup (O ⧸ rayM)ˣ) (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)

theorem ordinary_caps_rescale {N Y U V X₁ X₂ : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hb : Box N Y 0 (length U X₁) (length U X₂) 0) :
    Box (N/V) (Y/V) 0 (length (U^V) X₁) (length (U^V) X₂) 0 := by
  rw [length_rpow_base U X₁ V hU,length_rpow_base U X₂ V hU]
  refine ⟨div_nonneg hb.1 hV.le,div_nonneg hb.2.1 hV.le,?_,by norm_num,by norm_num⟩
  rcases hb.2.2.1 with h | h
  · exact Or.inl ⟨div_le_div_of_nonneg_right h.1 hV.le,div_le_div_of_nonneg_right h.2 hV.le⟩
  · exact Or.inr ⟨div_le_div_of_nonneg_right h.1 hV.le,div_le_div_of_nonneg_right h.2 hV.le⟩

theorem native_labelled {n y V bslot a b bΦ mesh σlo σhi ε U C : ℝ}
    {W : ℝ→ℂ} {η η₀ : Character} {Q : Ideal O} {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (hy0 : QRH.Cycle090.sourceY0 ≤ y) (hy1 : y ≤ QRH.Cycle090.sourceY) (hn0 : y ≤ n) (hn1 : n ≤ QRH.Cycle090.sourceRatio*y)
    (hV0 : radiusMin ≤ V) (hV1 : V ≤ 98/100)
    (hsrc : InitialAffineAt (α:=Slot) rayM Hr hHr
      (Qrh.TwoSlot.AnchorContinuum.PositiveSource.face nativeCost)
      W bslot a b bΦ mesh σlo σhi 1 1 ε U η η₀ Q degree controls C) :
    LabelledAt (α:=Slot) rayM Hr hHr (n/V) (y/V) (quota n y V/V)
      W bslot a b bΦ mesh σlo σhi 1 1 ε U η η₀ Q degree controls C := by
  intro T θ w σ v t height hw hwm hlo hhi hh hv M hM hM' Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ hb
  have he : M=1 := le_antisymm hM' hM
  subst M
  exact hsrc T θ w σ v t height hw hwm hlo hhi hh hv 1 le_rfl le_rfl
    Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ (native_admissible hy0 hy1 hn0 hn1 hV0 hV1 hb)

/-- Actual original two-ordinary and marked energy throughout [.89424,.98].
There is no earlier-source, derivative, scalar-price, or analytic moment premise.
The actual low-response class is retained, with response allowed up to one.
Mesh precedes slot data; all metadata precede U, V, the profiles and heights. -/
theorem original_small_radii {n y e : ℝ}
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hy0 : QRH.Cycle090.sourceY0 ≤ y) (hy1 : y ≤ QRH.Cycle090.sourceY) (hn0 : y ≤ n) (hn1 : n ≤ QRH.Cycle090.sourceRatio*y)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    ∃ mesh : ℝ, 0 < mesh ∧
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∃ buffer : ℝ, 0 < buffer ∧
    ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
      (hHr : RayOrthogonality.globalUnits rayM ≤ Hr),
    ∀ (W : ℝ→ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1 : ℝ) 2 →
    ∀ bΦ : ℝ, 2 ≤ bΦ → ∀ (η η₀ : Character) (Q : Ideal O),
      Q ≤ rayM → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∀ Cslot : ℝ, 0 ≤ Cslot →
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ U : ℝ in atTop,
    ∀ V : ℝ, radiusMin ≤ V → V ≤ 98/100 →
    ∀ (θ : Slot→RayQuotient.Characters rayM Hr) (w σ v : Slot→ℝ) (t height : ℝ),
      (∀ j, 0 ≤ w j) → (∀ j, w j ≤ mesh) →
      (∀ j, (33/50 : ℝ) ≤ σ j) → (∀ j, σ j ≤ (33/50 : ℝ)) →
      0 ≤ height → (∀ j, |v j| ≤ height) →
    ∀ (Φ : 𝓢(ℝ,ℂ)), Function.support (Φ : ℝ→ℂ) ⊆ Set.Iic bΦ →
      (∀ x, 0 ≤ (Φ x).re) → ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),
      0 < X₁ → 0 < X₂ → Box n y 0 (length U X₁) (length U X₂) 0 →
      (∑ j, w j) ≤ QRH.Cycle090.sourceWidth n y-(u : ℝ) →
      energy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
        (originalPools rayM Hr 2 U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
        (fun j=>U^(w j)) X₁ X₂
        (fun z=>initialKeep η (internalQ Q η₀) z ∧
          LowRows Finset.univ η (fixedBadMask*idealGenerator 1) 1 t U e (Cslot*U^buffer) w
            (originalPools rayM Hr 2 U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
            (fun j=>U^(w j)) z) Φ (U^V)  ≤ 
        C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
          (1+|t|+height)^degree*U^(V+(u : ℝ)-(rho : ℝ)/4+(5/6)*max 0 ((H : ℝ)-V)) := by
  let ε : ℝ := (rho : ℝ)/16
  have hε : 0 < ε := by norm_num [ε,rho]
  obtain ⟨sourceMesh,hsourceMesh,hsource⟩ := native_source hβ ε hε
  let mesh := min (radiusMin*sourceMesh) (1/100000)
  have hrad : 0 < radiusMin := by norm_num [radiusMin]
  have hmesh : 0 < mesh := lt_min (mul_pos hrad hsourceMesh) (by norm_num)
  refine ⟨mesh,hmesh,?_⟩
  intro Slot _ _
  let buffer : ℝ := (rho : ℝ)/(16*((Fintype.card Slot : ℝ)+1))
  have hbuffer : 0 < buffer := by dsimp [buffer]; apply div_pos (by norm_num [rho]); positivity
  refine ⟨buffer,hbuffer,?_⟩
  intro rayM _ Hr hHr W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72 Cslot hCslot
  obtain ⟨degree,controls,C,hC,hZ⟩ := hsource Slot rayM Hr hHr W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  let A : ℝ := (max 1 Cslot)^(Fintype.card Slot)
  have hA : 0 < A := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  refine ⟨degree,controls,A*C,mul_pos hA hC,?_⟩
  obtain ⟨Z₀,hZ₀⟩ := Filter.eventually_atTop.mp hZ
  have hlarge := (tendsto_rpow_atTop hrad).eventually (eventually_ge_atTop Z₀)
  filter_upwards [hlarge,eventually_ge_atTop (1 : ℝ)] with U hUmin hU
  intro V hV0 hV1 θ w σ v t height hw hwm hσlo hσhi hh hv Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ hbox hwidth
  have hV := (quota_guards hy0 hy1 hn0 hn1 hV0 hV1).1
  have hUpos := zero_lt_one.trans_le hU
  have hsrc₀ := hZ₀ (U^V) (hUmin.trans (Real.rpow_le_rpow_of_exponent_le hU hV0))
  have hsrc := native_labelled rayM Hr hHr hy0 hy1 hn0 hn1 hV0 hV1 hsrc₀
  obtain ⟨F,hFwidth,hFdelete,_⟩ := select_before_rows w mesh (quota n y V) hw hwm hmesh.le
    (quota_guards hy0 hy1 hn0 hn1 hV0 hV1).2.1.le
  have hordinary := ordinary_caps_rescale hUpos hV hbox
  have hFbox : Box (n/V) (y/V) (V*(quota n y V/V))
      (length (U^V) X₁) (length (U^V) X₂) (∑ j∈F,w j) := by
    refine ⟨hordinary.1,hordinary.2.1,hordinary.2.2.1,
      Finset.sum_nonneg (fun j _=>hw j),?_⟩
    simpa only [mul_div_cancel₀ _ hV.ne'] using hFwidth
  have hrel (j : Slot) : w j/V ≤ sourceMesh :=
    mesh_rescale hrad hV0 hsourceMesh.le (min_le_left _ _) (hwm j)
  have hprice := native_price (n:=n) (L:=QRH.Cycle090.sourceWidth n y-(u : ℝ))
    hy0 hy1 hV0 hV1 he0 he1 le_rfl (min_le_right _ _ : mesh ≤ 1/100000)
  have hcard : ((Finset.univ\F).card : ℝ) ≤ (Fintype.card Slot : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.subset_univ (Finset.univ\F))
  have hbuf : buffer*((Finset.univ\F).card : ℝ) ≤ (rho : ℝ)/16 := by
    have hm := mul_le_mul_of_nonneg_left hcard hbuffer.le
    have hbn : buffer*(Fintype.card Slot : ℝ) ≤ (rho : ℝ)/16 := by
      dsimp [buffer]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16*((Fintype.card Slot : ℝ)+1))).mpr
      norm_num [rho]
      nlinarith
    exact hm.trans hbn
  have herr : buffer*((Finset.univ\F).card : ℝ)+V*ε ≤ (rho : ℝ)/4 := by
    have heV := mul_le_mul_of_nonneg_right (show V ≤ 1 by linarith) hε.le
    dsimp [ε] at *
    norm_num [rho] at *
    linarith
  have hdelete' : (∑ j∈Finset.univ\F,w j) ≤ max 0
      ((∑ j,w j)-V*(quota n y V/V)+mesh) := by
    simpa only [mul_div_cancel₀ _ hV.ne'] using hFdelete
  have hprice' : e*max 0 (QRH.Cycle090.sourceWidth n y-(u : ℝ)-V*(quota n y V/V)+mesh) <
      (u : ℝ)-(rho : ℝ)/2+(5/6)*max 0 ((H : ℝ)-V) := by
    simpa only [mul_div_cancel₀ _ hV.ne'] using hprice
  have hb := LowActual.radial_low_energy rayM Hr hHr hsrc F θ w σ v t height mesh hw hrel
    hσlo hσhi hh hv Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ hU hV hCslot hC.le he0
    hFbox hwidth hdelete' hprice' herr
  have hp₀ : Cslot^(Finset.univ\F).card ≤ A := by
    have h₀ := pow_le_pow_left₀ hCslot (le_max_right 1 Cslot) (Finset.univ\F).card
    have h₁ := pow_le_pow_right₀ (le_max_left 1 Cslot)
      (show (Finset.univ\F).card ≤ Fintype.card Slot by exact_mod_cast hcard)
    exact h₀.trans h₁
  have hnonneg : 0 ≤ (C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
      (1+|t|+height)^degree)*U^(V+(u : ℝ)-(rho : ℝ)/4+(5/6)*max 0 ((H : ℝ)-V)) := by
    have hd := QuadraticInitialBound.diagonalControl_nonneg Φ
    positivity
  calc
    _  ≤  Cslot^(Finset.univ\F).card*
        ((C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
          (1+|t|+height)^degree)*U^(V+(u : ℝ)-(rho : ℝ)/4+(5/6)*max 0 ((H : ℝ)-V))) := by
      simpa only [mul_assoc] using hb
    _  ≤  A*((C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
          (1+|t|+height)^degree)*U^(V+(u : ℝ)-(rho : ℝ)/4+(5/6)*max 0 ((H : ℝ)-V))) :=
      mul_le_mul_of_nonneg_right hp₀ hnonneg
    _ = _ := by ring

end
end QRH.Cycle092.SmallCore
#print axioms QRH.Cycle092.SmallCore.original_small_radii
