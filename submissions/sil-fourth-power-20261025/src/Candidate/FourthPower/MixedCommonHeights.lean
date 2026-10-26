/- Copyright (c) 2026 Sil. Apache-2.0.
Exact absorption of an independent residual-column height. The centered
rectangles have the same product of lengths, so their common phase is
unchanged by subtraction. Original prefixes and the genuine common ideal
appear explicitly in the extracted phase, whose norm is one.
-/
import Candidate.FourthPower.MixedCommonSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedCommonHeights
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceLiveColumn
open CenteredMomentRectangle CenteredMomentCommonMaskEnergy CenteredMomentLattice
open MixedLiveNormalization ReferencePrimeEnclosure MixedCanonicalSource
local notation "Id" => Ideal HeckeFamily.O

def heightPhase (x v : ℝ) : ℂ := (x:ℂ)^(Complex.I*v)

theorem height_phase_mul (x y v : ℝ) (hx : 0≤x) (hy : 0≤y) :
    heightPhase (x*y) v=heightPhase x v*heightPhase y v := by
  simpa only [heightPhase,Complex.ofReal_mul] using Complex.mul_cpow_ofReal_nonneg hx hy (Complex.I*v)

theorem height_phase_norm (x v : ℝ) (hx : 0<x) : ‖heightPhase x v‖=1 := by
  simpa only [heightPhase,Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,mul_zero,sub_self,Real.rpow_zero] using
    Complex.norm_cpow_eq_rpow_re_of_pos hx (Complex.I*v)

theorem height_phase_ratio (x y v : ℝ) (hx : 0<x) (hy : 0<y) :
    heightPhase (x/y) v*heightPhase y v=heightPhase x v := by
  rw [←height_phase_mul _ _ v (div_pos hx hy).le hy.le,div_mul_cancel₀ _ hy.ne']

/-- Multiplicativity is valid also at zero; no vanishing convention for
the phase at zero is used later. Nonzero ideals are required for norm one. -/
def idealHeight (v : ℝ) : Id→*ℂ where
  toFun I := heightPhase (I.absNorm:ℝ) v
  map_one' := by simp [heightPhase]
  map_mul' I J := by
    simpa only [map_mul,Nat.cast_mul] using
      height_phase_mul (I.absNorm:ℝ) (J.absNorm:ℝ) v (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem ideal_height_norm (v : ℝ) (I : Id) (hI : I≠0) : ‖idealHeight v I‖=1 := by
  apply height_phase_norm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem phase_profile_shift (W : ℝ→ℂ) (t v x : ℝ) (hx : 0<x) :
    phaseProfile W (t+v/(2*Real.pi)) x=phaseProfile W t x*heightPhase x v := by
  simp only [phaseProfile,JointLogSeparation.logPhase_add_frequency,logPhase_eq_normPower v x hx,heightPhase]
  ring

theorem height_coefficient_add (β : Id→ℂ) (t v : ℝ) (I : Id) (hI : I≠0) :
    heightCoefficient (heightCoefficient β t) v I=heightCoefficient β (t+v) I := by
  have hn : (I.absNorm:ℂ)≠0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  simp only [heightCoefficient,Complex.ofReal_add,mul_add,Complex.cpow_add _ _ hn]
  ring

/-- The same scalar works for both rectangles precisely because their
products of lengths agree. The existing individual phase frequencies may
be unequal; both receive the same additional height. -/
theorem rectangle_height (W₁ W₂ : ℝ→ℂ) (t₁ t₂ v X₁ X₂ Y₁ Y₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hXY : X₁*X₂=Y₁*Y₂) (I J : Id) (hI : I≠0) (hJ : J≠0) :
    heightPhase (X₁*X₂) v*
      idealRectangle (phaseProfile W₁ (t₁+v/(2*Real.pi))) (phaseProfile W₂ (t₂+v/(2*Real.pi)))
        X₁ X₂ Y₁ Y₂ I J=
      (idealHeight v I*idealHeight v J)*
        idealRectangle (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) X₁ X₂ Y₁ Y₂ I J := by
  have hnI : 0<(I.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hnJ : 0<(J.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hp (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
      heightPhase (X*Y) v*heightPhase ((I.absNorm:ℝ)/X) v*heightPhase ((J.absNorm:ℝ)/Y) v=
        idealHeight v I*idealHeight v J := by
    rw [height_phase_mul X Y v hX.le hY.le]
    calc
      _ = (heightPhase ((I.absNorm:ℝ)/X) v*heightPhase X v)*
          (heightPhase ((J.absNorm:ℝ)/Y) v*heightPhase Y v) := by ring
      _ = _ := by rw [height_phase_ratio _ X v hnI hX,height_phase_ratio _ Y v hnJ hY];rfl
  unfold idealRectangle
  rw [phase_profile_shift W₁ t₁ v _ (div_pos hnI hX₁),
    phase_profile_shift W₂ t₂ v _ (div_pos hnJ hX₂),
    phase_profile_shift W₁ t₁ v _ (div_pos hnI hY₁),
    phase_profile_shift W₂ t₂ v _ (div_pos hnJ hY₂)]
  have hpX := hp X₁ X₂ hX₁ hX₂
  have hpY := hp Y₁ Y₂ hY₁ hY₂
  rw [←hXY] at hpY
  calc
    _ = (heightPhase (X₁*X₂) v*heightPhase ((I.absNorm:ℝ)/X₁) v*heightPhase ((J.absNorm:ℝ)/X₂) v)*
          (phaseProfile W₁ t₁ ((I.absNorm:ℝ)/X₁)*phaseProfile W₂ t₂ ((J.absNorm:ℝ)/X₂))-
        (heightPhase (X₁*X₂) v*heightPhase ((I.absNorm:ℝ)/Y₁) v*heightPhase ((J.absNorm:ℝ)/Y₂) v)*
          (phaseProfile W₁ t₁ ((I.absNorm:ℝ)/Y₁)*phaseProfile W₂ t₂ ((J.absNorm:ℝ)/Y₂)) := by ring
    _ = _ := by rw [hpX,hpY];ring

variable {α : Type*} [Fintype α]
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _

omit [Fintype α] in
theorem slot_coefficient_height (ν : α→Character) (R₀ : α→Finset Id) (t v : ℝ)
    (i : α) (I : Id) (hI : I≠0) :
    heightCoefficient (slotCoefficient ν R₀ t i) v I=slotCoefficient ν R₀ (t+v) i I :=
  height_coefficient_add _ t v I hI

theorem profile_height (R seed : Id) (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (t₁ t₂ v X₁ X₂ Y₁ Y₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hXY : X₁*X₂=Y₁*Y₂) (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0)
    (u : Tuple α) (hu : ∀j,u j≠0) :
    heightPhase (X₁*X₂) v*
      profileCoefficient R (fun i=>heightCoefficient (ν i) v) Wslot P
        (phaseProfile W₁ (t₁+v/(2*Real.pi))) (phaseProfile W₂ (t₂+v/(2*Real.pi)))
        X₁ X₂ Y₁ Y₂ d.1 d.2 seed u=
      idealHeight v (d.1*d.2)*idealHeight v (finiteTupleProduct u)*
        profileCoefficient R ν Wslot P (phaseProfile W₁ t₁) (phaseProfile W₂ t₂)
          X₁ X₂ Y₁ Y₂ d.1 d.2 seed u := by
  have hm : (∏i,heightCoefficient (ν i) v (u (Sum.inl i))*Wslot i ((u (Sum.inl i)).absNorm/P i))=
      (∏i,ν i (u (Sum.inl i))*Wslot i ((u (Sum.inl i)).absNorm/P i))*
        ∏i,idealHeight v (u (Sum.inl i)) := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [heightCoefficient,idealHeight,MonoidHom.coe_mk,OneHom.coe_mk,heightPhase,
      Complex.ofReal_natCast]
    ring
  have hp : idealHeight v (finiteTupleProduct u)=
      (∏i,idealHeight v (u (Sum.inl i)))*idealHeight v (u (Sum.inr 0))*idealHeight v (u (Sum.inr 1)) := by
    simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two,map_mul,map_prod]
    ring
  have hr := rectangle_height W₁ W₂ t₁ t₂ v X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hXY
    (d.1*u (Sum.inr 0)) (d.2*u (Sum.inr 1)) (mul_ne_zero hd.1 (hu _)) (mul_ne_zero hd.2 (hu _))
  simp only [map_mul] at hr
  unfold profileCoefficient
  rw [hm,hp,map_mul]
  calc
    _ = (∏i,ν i (u (Sum.inl i))*Wslot i ((u (Sum.inl i)).absNorm/P i))*
        (∏i,idealHeight v (u (Sum.inl i)))*
        (if IsCoprime (finiteTupleProduct u) R then 1 else 0)*
        (if seed∣finiteTupleProduct u then 1 else 0)*
        (heightPhase (X₁*X₂) v*
          idealRectangle (phaseProfile W₁ (t₁+v/(2*Real.pi))) (phaseProfile W₂ (t₂+v/(2*Real.pi)))
            X₁ X₂ Y₁ Y₂ (d.1*u (Sum.inr 0)) (d.2*u (Sum.inr 1))) := by ring
    _ = _ := by rw [hr];ring

/-- Arbitrary tuple multipliers, including the literal fifth-free and
injectivity indicator, pass through the exact height identity. -/
theorem column_height (Q : Finset (Tuple α)) (hQ : ∀u∈Q,∀j,u j≠0) (weight : Tuple α→ℂ)
    (R seed : Id) (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (t₁ t₂ v X₁ X₂ Y₁ Y₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hXY : X₁*X₂=Y₁*Y₂) (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (I : Id) :
    heightPhase (X₁*X₂) v*
      finiteColumnCoefficient Q (fun u=>weight u*
        profileCoefficient R (fun i=>heightCoefficient (ν i) v) Wslot P
          (phaseProfile W₁ (t₁+v/(2*Real.pi))) (phaseProfile W₂ (t₂+v/(2*Real.pi)))
          X₁ X₂ Y₁ Y₂ d.1 d.2 seed u) I=
      idealHeight v (d.1*d.2)*idealHeight v I*
        finiteColumnCoefficient Q (fun u=>weight u*
          profileCoefficient R ν Wslot P (phaseProfile W₁ t₁) (phaseProfile W₂ t₂)
            X₁ X₂ Y₁ Y₂ d.1 d.2 seed u) I := by
  unfold finiteColumnCoefficient
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  obtain ⟨huQ,huI⟩ := Finset.mem_filter.mp hu
  have he := profile_height R seed ν Wslot P W₁ W₂ t₁ t₂ v X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hXY d hd u (hQ u huQ)
  rw [huI] at he
  calc
    _ = weight u*(heightPhase (X₁*X₂) v*profileCoefficient R
        (fun i=>heightCoefficient (ν i) v) Wslot P
        (phaseProfile W₁ (t₁+v/(2*Real.pi))) (phaseProfile W₂ (t₂+v/(2*Real.pi)))
        X₁ X₂ Y₁ Y₂ d.1 d.2 seed u) := by ring
    _ = _ := by rw [he];ring

def residualPhase (T : ℝ) (d : Id×Id) (G : Id) (v : ℝ) : ℂ :=
  heightPhase (T/(pairNorm d*(G.absNorm:ℝ))) v

theorem residual_phase_norm (T : ℝ) (hT : 0<T) (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0)
    (G : Id) (hG : G≠0) (v : ℝ) : ‖residualPhase T d G v‖=1 := by
  have hGpos : 0<(G.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hG)
  exact height_phase_norm _ _ (div_pos hT (mul_pos (pairNorm_pos hd.1 hd.2) hGpos))

/-- Conversion from the original height on the residual ideal I to the
shifted profile on G*I. Its phase includes both G and the original d. -/
theorem residual_column_height (Q : Finset (Tuple α)) (hQ : ∀u∈Q,∀j,u j≠0) (weight : Tuple α→ℂ)
    (R seed G : Id) (hG : G≠0) (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (t₁ t₂ v X₁ X₂ Y₁ Y₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hXY : X₁*X₂=Y₁*Y₂) (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (I : Id) :
    finiteColumnCoefficient Q (fun u=>weight u*
      profileCoefficient R ν Wslot P (phaseProfile W₁ t₁) (phaseProfile W₂ t₂)
        X₁ X₂ Y₁ Y₂ d.1 d.2 seed u) (G*I)*idealHeight v I=
      residualPhase (X₁*X₂) d G v*
        finiteColumnCoefficient Q (fun u=>weight u*
          profileCoefficient R (fun i=>heightCoefficient (ν i) v) Wslot P
            (phaseProfile W₁ (t₁+v/(2*Real.pi))) (phaseProfile W₂ (t₂+v/(2*Real.pi)))
            X₁ X₂ Y₁ Y₂ d.1 d.2 seed u) (G*I) := by
  have he := column_height Q hQ weight R seed ν Wslot P W₁ W₂ t₁ t₂ v X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hXY d hd (G*I)
  have hGpos : 0<(G.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hG)
  have hphase : residualPhase (X₁*X₂) d G v*(idealHeight v (d.1*d.2)*idealHeight v G)=
      heightPhase (X₁*X₂) v := by
    have hh := height_phase_ratio (X₁*X₂) (pairNorm d*(G.absNorm:ℝ)) v
      (mul_pos hX₁ hX₂) (mul_pos (pairNorm_pos hd.1 hd.2) hGpos)
    rw [height_phase_mul _ _ v (pairNorm_pos hd.1 hd.2).le hGpos.le] at hh
    have hdphase : idealHeight v (d.1*d.2)=heightPhase (pairNorm d) v := by
      change heightPhase (((d.1*d.2).absNorm:ℝ)) v=heightPhase (pairNorm d) v
      simp only [map_mul,Nat.cast_mul,pairNorm]
    change heightPhase ((X₁*X₂)/(pairNorm d*(G.absNorm:ℝ))) v*
      (idealHeight v (d.1*d.2)*heightPhase (G.absNorm:ℝ) v)=_
    rw [hdphase]
    exact hh
  have hne : idealHeight v (d.1*d.2)*idealHeight v G≠0 := by
    apply mul_ne_zero
    · exact norm_ne_zero_iff.mp (by rw [ideal_height_norm v _ (mul_ne_zero hd.1 hd.2)];norm_num)
    · exact norm_ne_zero_iff.mp (by rw [ideal_height_norm v G hG];norm_num)
  apply mul_left_cancel₀ hne
  simp only [map_mul] at he
  calc
    _ = heightPhase (X₁*X₂) v*finiteColumnCoefficient Q (fun u=>weight u*
        profileCoefficient R (fun i=>heightCoefficient (ν i) v) Wslot P
          (phaseProfile W₁ (t₁+v/(2*Real.pi))) (phaseProfile W₂ (t₂+v/(2*Real.pi)))
          X₁ X₂ Y₁ Y₂ d.1 d.2 seed u) (G*I) := by rw [he];simp only [map_mul];ring
    _ = _ := by rw [←hphase];ring

end
end Candidate.FourthPower.MixedCommonHeights
