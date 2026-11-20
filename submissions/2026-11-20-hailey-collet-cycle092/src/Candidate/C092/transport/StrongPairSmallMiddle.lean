/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite authentic two-anchor energies. A common physical mark is represented
at each anchor by an exact norm equality, not by a new analytic bound. -/
import Candidate.C092.transport.StrongPairSmallFinite

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
local notation "O" => ActualEisensteinCubic.O

open CenteredMomentEnergyBands
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.NativeStrip

/-- The original P.1 response pays all finite common marks through 7/8.
The two fixed characters, their inducing ideals and their keeps are independent.
Every positive ordinary length below its original cap remains live. -/
theorem independent_small_middle {n y e : ℝ}
    (hβ : (51/100:ℝ)  ≤  HeckeZeroSupremum.beta)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (he0 : 0 ≤ e) (he1 : e ≤ 3/4)
    (Slot : Type) [Fintype Slot] [DecidableEq Slot] :
    ∃ buffer : ℝ,0<buffer ∧
    ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
      (hHr : RayOrthogonality.globalUnits rayM ≤ Hr),
    ∀ bΦ : ℝ,0<bΦ → Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ →
    ∀ (η₁ η₂ η₀₁ η₀₂ : Character) (Q₁ Q₂ : Ideal O),
      Q₁ ≤ rayM → internalQ Q₁ η₀₁ ≠ 0 → internalQ Q₁ η₀₁ ≠ ⊤ → internalQ Q₁ η₀₁ ≤ Ideal.span {(72:O)} →
      Q₂ ≤ rayM → internalQ Q₂ η₀₂ ≠ 0 → internalQ Q₂ η₀₂ ≠ ⊤ → internalQ Q₂ η₀₂ ≤ Ideal.span {(72:O)} →
    ∀ Cslot : ℝ,0 ≤ Cslot →
    ∃ degree : ℕ,∃ controls : Finset (ℕ×ℕ),∃ C : ℝ,0<C ∧
    ∀ᶠ U : ℝ in atTop,
    ∀ V : ℝ,0 ≤ V → V ≤ 7/8 →
    ∀ (T : Finset Slot) (w : Slot→ℝ) (t₁ t₂ height : ℝ),
      (∀ i,0 ≤ w i) → 0 ≤ height → (∑ i∈T,w i) ≤ sourceWidth n y-(u:ℝ) →
    ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),0<X₁ → 0<X₂ →
      length U X₁ ≤ n → length U X₂ ≤ y →
    ∀ (s : Finset FreeRow) (mark : Slot→FreeRow→ℂ),
      (∀ z∈s,initialKeep η₁ (internalQ Q₁ η₀₁) z.val) →
      (∀ z∈s,initialKeep η₂ (internalQ Q₂ η₀₂) z.val) →
      (∀ z∈s,rowNorm z ≤ U^V) →
      (∀ z∈s,∀ i∈T,‖mark i z‖^2 ≤ (Cslot*U^buffer)*U^(e*w i)) →
      finiteEnergyOn T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark  ≤ 
        C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
          (1+|t₁|+|t₂|+height)^degree*
          U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V)) := by
  let buffer : ℝ:=1/(10000*(1+(Fintype.card Slot:ℝ)))
  have hb : 0<buffer := by dsimp [buffer]; positivity
  have hfee : buffer*(Fintype.card Slot:ℝ) ≤ 1/10000 := by
    have heq : buffer*(10000*(1+(Fintype.card Slot:ℝ)))=1 := by dsimp [buffer]; field_simp
    nlinarith only [heq,hb]
  refine ⟨buffer,hb,?_⟩
  intro rayM _ Hr hHr bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ hQ₁r hQ₁0 hQ₁t hQ₁72 hQ₂r hQ₂0 hQ₂t hQ₂72 Cslot hCslot
  obtain ⟨d,S,C₀,hC₀,hsrc⟩:=independent_pair_distinct_source hβ rayM Hr hHr bΦ hbΦ hΦs
    η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ hQ₁r hQ₁0 hQ₁t hQ₁72 hQ₂r hQ₂0 hQ₂t hQ₂72
  let A : ℝ:=(max 1 Cslot)^(Fintype.card Slot)
  have hA : 0<A := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  refine ⟨d,S,A*C₀,mul_pos hA hC₀,?_⟩
  filter_upwards [hsrc,eventually_gt_atTop (1:ℝ)] with U hsrc hU
  intro V hV0 hV1 T w t₁ t₂ height hw hh hwidth p X₁ X₂ hX₁ hX₂ hXN hXY s mark hk₁ hk₂ hy hlow
  have hUp : 0<U := zero_lt_one.trans hU
  have hn : n ≤ 1 := by norm_num [sourceRatio,sourceY] at hn1 hy1; linarith only [hn1,hy1]
  have hy' : y ≤ 1 := hy1.trans (by norm_num [sourceY])
  have lengths:=ordinary_lengths_below_U hU hn hy'
    (show Box n y 0 (length U X₁) (length U X₂) 0 from
      ⟨length_nonneg _ _ hU,length_nonneg _ _ hU,Or.inl ⟨hXN,hXY⟩,le_rfl,le_rfl⟩)
  have hsE:=hsrc hU.le V hV0 (hV1.trans (by norm_num)) p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ lengths.1 lengths.2 s hk₁ hk₂ hy
  have hTcard : (T.card:ℝ) ≤ (Fintype.card Slot:ℝ) := by exact_mod_cast Finset.card_le_univ T
  have hbuf : buffer*(T.card:ℝ) ≤ 1/10000 :=
    (mul_le_mul_of_nonneg_left hTcard hb.le).trans hfee
  have hS : 0 ≤ ∑ i∈T,w i := Finset.sum_nonneg (fun i _=>hw i)
  have hpaid:=unmarked_middle_paid hV1 he1 hS
    (hwidth.trans (original_width_cap_sharp hy0 hy1 hn0)) hbuf
  have herase:=finite_delete_all T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂
    mark (Cslot*U^buffer) U e w hUp (by positivity) hlow
  have hpow : Cslot^T.card ≤ A := by
    apply (pow_le_pow_left₀ hCslot (le_max_right _ _) _).trans
    exact pow_le_pow_right₀ (le_max_left _ _) (Finset.card_le_univ T)
  have hdiag:=QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  calc
    _  ≤  ((Cslot*U^buffer)^T.card*U^(e*∑ i∈T,w i))*
      (C₀*QuadraticInitialBound.diagonalControl radialMajorant*(p.control S)^2*
       (1+|t₁|+|t₂|+height)^d*U^(V+1/10000)) :=
      herase.trans (mul_le_mul_of_nonneg_left hsE (by positivity))
    _ = (Cslot^T.card*C₀*QuadraticInitialBound.diagonalControl radialMajorant*(p.control S)^2*
       (1+|t₁|+|t₂|+height)^d)*U^(V+1/10000+buffer*(T.card:ℝ)+e*∑ i∈T,w i) := by
      rw [mul_pow,←Real.rpow_mul_natCast hUp.le]
      rw [Real.rpow_add hUp (V+1/10000+buffer*(T.card:ℝ)) (e*∑ i∈T,w i),
        Real.rpow_add hUp (V+1/10000) (buffer*(T.card:ℝ))]
      ring
    _  ≤  _ := by
      have hr:=Real.rpow_le_rpow_of_exponent_le hU.le hpaid
      gcongr

#print axioms independent_small_middle
end
end QRH.Cycle092.StrongPair
