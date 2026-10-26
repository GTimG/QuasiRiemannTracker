import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.HighResidualAllocation
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.HighCommonExponent
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily Cycle63HighResidual
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonHeightEnvelope
open CenteredMomentAmplificationChildInput CenteredMomentAllocatedChildCapacity
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentEligibleEnergy CenteredMomentSlotRatios CenteredMomentActiveDivisorShell

/-- Both common allocations only delete original slots. Their analytic
control is therefore bounded before either allocation or final height. -/
theorem actual_two_common_control_fixed {ι : Type*} [Fintype ι]
    (N : ℕ) (Cs bs : ℝ) (hCs : 1≤Cs) (hbs : 1≤bs)
    (s : Input ι) (hcard : Fintype.card ι≤N) (hM : ∀i,s.M i≤Cs)
    (hb₁ : s.b₁≤bs) (hb₂ : s.b₂≤bs)
    (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁) (χ₁ : Character) (t₁ : ℝ)
    (C₂ R₂ : Ideal O) (B₂ : actualAllocations (child s C₁ R₁ B₁ χ₁ t₁).pools C₂)
    (χ₂ : Character) (t₂ : ℝ) :
    wholeControl (commonData (withHeight (child s C₁ R₁ B₁ χ₁ t₁) χ₂ t₂) C₂ R₂ B₂)≤
      2*bs*Cs^N := by
  apply wholeControl_fixed N Cs bs hCs hbs
  · exact (live_card_le B₂.val).trans ((live_card_le B₁.val).trans hcard)
  · intro j
    exact hM j.val.val
  · exact hb₁
  · exact hb₂

/-- A fixed slot-window bound pays the complete residual and plain
clipping allowance. The denominator is the original logarithmic scale. -/
theorem fixed_source_allowance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (L bs : ℝ) (hL : 0≤L) (hbs : 1≤bs)
    (s : Data ι) (hcard : Fintype.card ι≤N)
    (hwindow : ∀i,logWindow (s.lo i) (s.hi i)≤L)
    (hb₁ : s.b₁≤bs) (hb₂ : s.b₂≤bs) (Z : ℝ) (hZ : 1<Z) :
    s.toSource.allowance Z+Cycle63.Physical.plainClipAllowance Z ![s.b₁,s.b₂]≤
      ((N:ℝ)*L+2*Real.log bs)/Real.log Z := by
  have hsum : (∑i,logWindow (s.lo i) (s.hi i))≤(N:ℝ)*L := by
    calc
      _≤∑_i : ι,L := Finset.sum_le_sum (fun i _=>hwindow i)
      _=(Fintype.card ι:ℝ)*L := by simp
      _≤_ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hL
  have hp₁ : Real.log (max 1 s.b₁)≤Real.log bs :=
    Real.log_le_log (by positivity) (max_le hbs hb₁)
  have hp₂ : Real.log (max 1 s.b₂)≤Real.log bs :=
    Real.log_le_log (by positivity) (max_le hbs hb₂)
  unfold Source.allowance Cycle63.Physical.plainClipAllowance
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Real.logb]
  rw [←add_div,←add_div]
  apply div_le_div_of_nonneg_right _ (Real.log_pos hZ).le
  change (∑i,logWindow (s.lo i) (s.hi i))+
    (Real.log (max 1 s.b₁)+Real.log (max 1 s.b₂))≤_
  linarith

/-- All fixed support allowances vanish uniformly before the source,
its two common allocations, and both character/height choices are known. -/
theorem eventual_two_common_allowance (N : ℕ) (L bs ε : ℝ)
    (hL : 0≤L) (hbs : 1≤bs) (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀{ι : Type}[Fintype ι][DecidableEq ι](s : Input ι),
      Fintype.card ι≤N → (∀i,logWindow (s.lo i) (s.hi i)≤L) →
      s.b₁≤bs → s.b₂≤bs →
      ∀(C₁ R₁ : Ideal O)(B₁ : actualAllocations s.pools C₁)(χ₁ : Character)(t₁ : ℝ)
        (C₂ R₂ : Ideal O)(B₂ : actualAllocations (child s C₁ R₁ B₁ χ₁ t₁).pools C₂)
        (χ₂ : Character)(t₂ : ℝ),
      let src := commonData (withHeight (child s C₁ R₁ B₁ χ₁ t₁) χ₂ t₂) C₂ R₂ B₂
      src.toSource.allowance Z+Cycle63.Physical.plainClipAllowance Z ![src.b₁,src.b₂]≤ε := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (((N:ℝ)*L+2*Real.log bs)/ε)),eventually_gt_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro ι _ _ s hcard hwindow hb₁ hb₂ C₁ R₁ B₁ χ₁ t₁ C₂ R₂ B₂ χ₂ t₂ src
  apply (fixed_source_allowance N L bs hL hbs src
    ((live_card_le B₂.val).trans ((live_card_le B₁.val).trans hcard))
    (fun j=>hwindow j.val.val) hb₁ hb₂ Z hZ).trans
  exact (div_le_iff₀ (Real.log_pos hZ)).mpr
    (by nlinarith [(div_le_iff₀ hε).mp hz])

/-- The first common child retains exactly the original slot dictionary;
its new natural character does not change the slot coefficients. -/
theorem actual_child_matches {ι : Type*}[Fintype ι][DecidableEq ι]
    (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (s : Input ι)(η₀ : Character)(θ : ι→RayQuotient.Characters M H)
    (w σ v : ι→ℝ)(W : ℝ→ℂ)(b Z : ℝ)
    (hm : CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ v W b Z)
    (C R : Ideal O)(B : actualAllocations s.pools C)(χ : Character)(t : ℝ) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (child s C R B χ t) η₀
      (fun j=>θ j.val) (fun j=>w j.val) (fun j=>σ j.val) (fun j=>v j.val) W b Z := by
  exact ⟨fun j I=>hm.character j.val I,fun j x=>hm.profile j.val x,
    fun j=>hm.pool j.val,fun j=>hm.scale j.val⟩

/-- The first common allocation cannot enlarge any of the four plain
scales used by the final shell theorem. -/
theorem actual_child_plain_scale_le {ι : Type*}[Fintype ι]
    (s : Input ι)(C R : Ideal O)(B : actualAllocations s.pools C)(χ : Character)(t : ℝ)
    (second : Bool)(j : Fin 2) :
    Cycle63.Physical.sourcePlainScales (child s C R B χ t).toData.toSource second j≤
      Cycle63.Physical.sourcePlainScales s.toData.toSource second j := by
  have hnorm : (1:ℝ)≤(B.val (Sum.inr j)).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (alloc_ne s C B (Sum.inr j)))
  cases second <;> fin_cases j
  · exact div_le_self s.X₁_pos.le hnorm
  · exact div_le_self s.X₂_pos.le hnorm
  · exact div_le_self s.Y₁_pos.le hnorm
  · exact div_le_self s.Y₂_pos.le hnorm

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
