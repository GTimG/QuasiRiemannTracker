import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondCoarseShell
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondSourceControls
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentCommonHeightEnvelope
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildSourceCaps

/-- Fixed coefficient cost for the coarse tail. Its large size is harmless:
it is chosen before all scales, rows, allocations and heights. -/
def coarseFixedControl (N : ℕ)(Cs b bs : ℝ) : ℝ :=
  (2*(bs*bs))*(Cs^N)^2*((128*bs)^2*(128*b*Cs)^N)^2*2

lemma coarse_fixed_control_pos (N : ℕ)(Cs b bs : ℝ)
    (hCs : 1≤Cs)(hb : 1≤b)(hbs : 1≤bs) : 0<coarseFixedControl N Cs b bs := by
  unfold coarseFixedControl
  positivity

/-- Actual scale and coefficient gates imply a uniform coarse polynomial
bound; this does not assume an analytic moment estimate. -/
theorem actual_coarse_control_fixed {ι : Type*}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs b bs cap Z B₁ B₂ : ℝ)(hCs : 1≤Cs)(hb : 1≤b)(hbs : 1≤bs)
    (hcap : 0≤ cap)(hZ : 1≤Z)(hB₁ : 0≤B₁)(hB₂ : 0≤B₂)
    (s : Data ι)(hcard : Fintype.card ι≤N)(hM : ∀j,s.M j≤Cs)
    (hhi : ∀j,s.hi j≤b)(hb₁ : s.b₁≤bs)(hb₂ : s.b₂≤bs)
    (hscales : ∀second j,Cycle63.Physical.sourcePlainScales s.toSource second j≤Z^cap)
    (hP : ∀j,s.P j≤Z^cap) :
    coarseAllocationControl s B₁ B₂≤
      coarseFixedControl N Cs b bs*(B₁*B₂)^2*Z^(((N:ℝ)+2)*cap) := by
  have hz : 0<Z := lt_of_lt_of_le (by norm_num) hZ
  have hzcap : 1≤Z^cap := Real.one_le_rpow hZ hcap
  have hm0 : ∀j,0≤ s.M j := fun j=>zero_le_one.trans (s.M_ge_one j)
  have hpM : (∏j,s.M j)≤Cs^N := by
    calc
      _≤∏_j : ι,Cs := Finset.prod_le_prod₀ (fun j _=>hm0 j) (fun j _=>hM j)
      _=Cs^(Fintype.card ι) := by simp
      _≤Cs^N := pow_le_pow_right₀ hCs hcard
  have hfac0 : ∀j,0≤128*max 1 (s.hi j)*s.M j := fun j=>mul_nonneg (by positivity) (hm0 j)
  have hpF : (∏j,128*max 1 (s.hi j)*s.M j)≤(128*b*Cs)^N := by
    calc
      _≤∏_j : ι,128*b*Cs := Finset.prod_le_prod₀ (fun j _=>hfac0 j) (fun j _=>by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (max_le hb (hhi j)) (by norm_num)
        · exact hM j
        · exact hm0 j
        · positivity)
      _=(128*b*Cs)^(Fintype.card ι) := by simp
      _≤_ := pow_le_pow_right₀ (by nlinarith [mul_le_mul hb hCs (by norm_num : (0:ℝ)≤1) (by linarith : 0≤b)]) hcard
  have hrow : coarseRowControl s B₁ B₂≤((128*bs)^2*(128*b*Cs)^N)*(B₁*B₂) := by
    unfold coarseRowControl
    calc
      _≤(128*bs*B₁)*(128*bs*B₂)*(128*b*Cs)^N := by
        apply mul_le_mul _ hpF (Finset.prod_nonneg (fun j _=>hfac0 j)) (by positivity)
        apply mul_le_mul
        · gcongr; exact max_le hbs hb₁
        · gcongr; exact max_le hbs hb₂
        · positivity
        · positivity
      _=_ := by ring
  have hsize (second : Bool) : coarseRowSize s second≤Z^(((N:ℝ)+2)*cap) := by
    have hp : (∏j,max 1 (s.P j))≤(Z^cap)^N := by
      calc
        _≤∏_j : ι,Z^cap := Finset.prod_le_prod₀ (fun _ _=>by positivity)
          (fun j _=>max_le hzcap (hP j))
        _=(Z^cap)^(Fintype.card ι) := by simp
        _≤_ := pow_le_pow_right₀ hzcap hcard
    unfold coarseRowSize
    calc
      _≤Z^cap*Z^cap*(Z^cap)^N := by
        apply mul_le_mul _ hp (Finset.prod_nonneg (fun _ _=>by positivity)) (by positivity)
        exact mul_le_mul (max_le hzcap (hscales second 0)) (max_le hzcap (hscales second 1))
          (by positivity) (by positivity)
      _=Z^(((N:ℝ)+2)*cap) := by
        rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz,←Real.rpow_add hz]
        congr 1
        ring
  have hMprod0 : 0≤∏j,s.M j := Finset.prod_nonneg (fun j _=>hm0 j)
  have hrow0 : 0≤ coarseRowControl s B₁ B₂ := by
    unfold coarseRowControl
    exact mul_nonneg (by positivity) (Finset.prod_nonneg (fun j _=>hfac0 j))
  unfold coarseAllocationControl
  calc
    _≤(2*(bs*bs))*(Cs^N)^2*(((128*bs)^2*(128*b*Cs)^N)*(B₁*B₂))^2*
        (2*Z^(((N:ℝ)+2)*cap)) := by
      apply mul_le_mul _ (by linarith [hsize false,hsize true])
        (add_nonneg (coarse_row_size_nonneg s false) (coarse_row_size_nonneg s true)) (by positivity)
      apply mul_le_mul _ (pow_le_pow_left₀ hrow0 hrow 2) (sq_nonneg _) (by positivity)
      apply mul_le_mul _ (pow_le_pow_left₀ hMprod0 hpM 2) (sq_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (max_le hbs hb₁) (max_le hbs hb₂) (by positivity) (by positivity)) (by norm_num)
    _=_ := by unfold coarseFixedControl; ring

/-- The two literal common allocations inherit the coarse bound from the
original input, uniformly in both newly introduced characters and heights. -/
theorem actual_two_common_coarse_control {ι : Type*}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs b bs cap Z B₁ B₂ : ℝ)(hCs : 1≤Cs)(hb : 1≤b)(hbs : 1≤bs)
    (hcap : 0≤ cap)(hZ : 1≤Z)(hB₁ : 0≤B₁)(hB₂ : 0≤B₂)
    (s : Input ι)(hcard : Fintype.card ι≤N)(hM : ∀j,s.M j≤Cs)
    (hupper : s.upper≤b)(hb₁ : s.b₁≤bs)(hb₂ : s.b₂≤bs)
    (hscales : ∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap)
    (hP : ∀j,s.P j≤Z^cap)
    (C₁ R₁ : Ideal O)(A₁ : actualAllocations s.pools C₁)(χ₁ : Character)(t₁ : ℝ)
    (C₂ R₂ : Ideal O)(A₂ : actualAllocations (child s C₁ R₁ A₁ χ₁ t₁).pools C₂)
    (χ₂ : Character)(t₂ : ℝ) :
    coarseAllocationControl
      (commonData (withHeight (child s C₁ R₁ A₁ χ₁ t₁) χ₂ t₂) C₂ R₂ A₂) B₁ B₂≤
      coarseFixedControl N Cs b bs*(B₁*B₂)^2*Z^(((N:ℝ)+2)*cap) := by
  apply actual_coarse_control_fixed N Cs b bs cap Z B₁ B₂ hCs hb hbs hcap hZ hB₁ hB₂
  · exact (live_card_le A₂.val).trans ((live_card_le A₁.val).trans hcard)
  · intro j; exact hM j.val.val
  · intro j; exact (s.upper_ge j.val.val).trans hupper
  · exact hb₁
  · exact hb₂
  · intro second j
    have hn : (1:ℝ)≤(A₂.val (Sum.inr j)).absNorm := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (alloc_ne (child s C₁ R₁ A₁ χ₁ t₁) C₂ A₂ (Sum.inr j)))
    have hh := actual_child_plain_scale_le s C₁ R₁ A₁ χ₁ t₁ second j
    apply le_trans _ (hh.trans (hscales second j))
    cases second <;> fin_cases j
    · exact div_le_self (child s C₁ R₁ A₁ χ₁ t₁).X₁_pos.le hn
    · exact div_le_self (child s C₁ R₁ A₁ χ₁ t₁).X₂_pos.le hn
    · exact div_le_self (child s C₁ R₁ A₁ χ₁ t₁).Y₁_pos.le hn
    · exact div_le_self (child s C₁ R₁ A₁ χ₁ t₁).Y₂_pos.le hn
  · intro j; exact hP j.val.val

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
