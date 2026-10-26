/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Raw.FixedMissingMoment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Raw.UniformSources

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily HeckeDyadic ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentEnergySlotHeight
open CenteredMomentEnergyProfiles CenteredMomentInductionEnergy
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot CenteredMomentEnergyBands
open QRH.Record12518109Source Record12518109Natural.InitialNatural
local notation "O" => HeckeFamily.O
local notation "ps" => CompletedGauss.primeSupport

/-- Dividing a quotient scale by a nonzero ideal only shortens its clipped
logarithmic length. This also admits every logarithmic Sobolev point. -/
theorem puncture_log_length_le (Z x upper : ℝ) (hZ : 1<Z)
    (R : Ideal O) (D : Finset (Ideal O)) (hD : D∈(ps R).powerset)
    (hx : x≤upper-Real.log ((∏ I∈D,I).absNorm:ℝ)) :
    length Z (Real.exp x)≤length Z (Real.exp upper) := by
  have hn : (∏ I∈D,I)≠0 := Finset.prod_ne_zero_iff.mpr (by
    intro I hI
    exact (support_prime R I ((Finset.mem_powerset.mp hD) hI)).ne_zero)
  have hone : (1:ℝ)≤((∏ I∈D,I).absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hn)
  have hxu : x≤upper := by linarith [Real.log_nonneg hone]
  exact Real.logb_le_logb_of_le hZ (lt_of_lt_of_le zero_lt_one (le_max_left 1 _))
    (max_le_max le_rfl (Real.exp_le_exp.mpr hxu))

def rawSourceBudget (CP CN DP DN : ℝ) (TP TN : Finset (ℕ×ℕ))
    (degreeP degreeN : ℕ) (Φ W₁ W₂ : 𝓢(ℝ,ℂ)) (t height Z M ε : ℝ) : ℝ :=
  CP*QuadraticInitialBound.diagonalControl Φ*
    (DP*(sourceControl TP W₁*sourceControl TP W₂))^2*
    (1+|t|+height)^degreeP*Z^(M+ε)+
  CN*QuadraticInitialBound.diagonalControl Φ*
    (DN*(sourceControl TN W₁*sourceControl TN W₂))^2*
    (1+|t|+height)^degreeN*Z^(M+ε)

variable {α : Type*} [DecidableEq α]
variable (rayModulus : Ideal O) [NeZero rayModulus]
local instance : Finite (O ⧸ rayModulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (Hray : Subgroup (O ⧸ rayModulus)ˣ)
variable (hH : RayOrthogonality.globalUnits rayModulus ≤ Hray)

/-- The fixed-missing-radical RAW moment with its analytic premise discharged
by the literal previous source and the genuine natural initial source.
All derivative controls and the multiplicity/deletion constant are chosen
before Z, the moving mask, the row selectors and the actual quotient scales.
No source-energy bound is added as a premise. -/
theorem actual_fixed_missing_source_moment
    (F : Finset α) (Mslot : α→ℝ) (hMslot : ∀i∈F,0≤Mslot i)
    (slotUpper B loss εmask : ℝ) (hB : 0≤B) (hloss : 0<loss) (hεmask : 0<εmask)
    (SP SN : Finset (ℕ×ℕ)) :
    ∃TP : Finset (ℕ×ℕ), ∃DP : ℝ, ∃TN : Finset (ℕ×ℕ), ∃DN C : ℝ,
      0<DP ∧ 0<DN ∧ 0<C ∧
    ∀(face : SourceFace)(Kcap : ℝ)(W : ℝ→ℂ)
      (a b bΦ mesh σlo σhi Mmin Mmax εsource Z : ℝ),2≤Z →
    ∀(η η₀ : Character)(Q : Ideal O)(degreeP degreeN : ℕ)(CP CN : ℝ),
      0≤CP → 0≤CN →
      InitialAffineAt (α:=α) rayModulus Hray hH face W
        slotUpper a b bΦ mesh σlo σhi Mmin Mmax εsource Z η η₀ Q degreeP SP CP →
      InitialNaturalAt (α:=α) rayModulus Hray hH Kcap W
        slotUpper a b bΦ mesh σlo σhi Mmin Mmax εsource Z η η₀ Q degreeN SN CN →
    ∀(left : Bool)(u₀ : O)(unit : FirstSourceLabel→O)(H : Ideal O), H≠0 →
    ∀labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      (∀l∈labels,((Ideal.span {(nonzeroJointSourceRow l).val}).absNorm:ℝ)≤Z^B) →
      (∀l∈labels,((Ideal.span {(nonzeroJointSourceRow l).val}*H).absNorm:ℝ)≤Z^B) →
      (∀l∈labels,Supported l.val.1.1.1 ∧ l.val.1.1.2≠0 ∧
        Supported l.val.2.1.1 ∧ l.val.2.1.2≠0) →
      (∀l∈labels,ps l.val.1.1.1=ps l.val.1.1.2 ∧ ps l.val.2.1.1=ps l.val.2.1.2) →
      (∀l∈labels,(l.val.1.1.1.absNorm:ℝ)≤Z^B ∧ (l.val.1.1.2.absNorm:ℝ)≤Z^B ∧
        (l.val.2.1.1.absNorm:ℝ)≤Z^B ∧ (l.val.2.1.2.absNorm:ℝ)≤Z^B) →
      (∀l∈labels,firstSourceMissing left l.val.1=H) →
    ∀R : Ideal O,R≠0 →
      (∀l : labels,initialKeep η (internalQ Q η₀) (nonzeroJointSourceRow l.val).val) →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ)),0≤b →
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
    ∀(θ : α→RayQuotient.Characters rayModulus Hray)(w σ freq : α→ℝ)(t height : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤mesh) →
      (∀i∈F,σlo≤σ i) → (∀i∈F,σ i≤σhi) → 0≤height → (∀i∈F,|freq i|≤height) →
      (∀i∈F,∀I∈primePool rayModulus Hray slotUpper (Z^(w i)),Prime I) →
      (∀i∈F,∀I∈primePool rayModulus Hray slotUpper (Z^(w i)),
        ‖idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I‖≤Mslot i) →
      (∀i∈F,∀I∈primePool rayModulus Hray slotUpper (Z^(w i)),
        idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I≠0 →
        (I.absNorm:ℝ)≤slotUpper*Z^(w i)) →
    ∀(M m₁ m₂ cap : ℝ),Mmin≤M → M≤Mmax → DownwardCaps face Kcap m₁ m₂ cap M →
      (∑i∈F,w i)≤cap →
    ∀(Φ : 𝓢(ℝ,ℂ)),Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ → (∀x,0≤(Φ x).re) →
    ∀(lo hi low high A : ℝ)(lx ly weight : labels→ℝ),
      (∀l : labels,1≤(Φ (‖eisEmbedding (nonzeroJointSourceRow l.val).val‖^2/(Z^M))).re) →
      lo≤hi → low≤high → length Z (Real.exp hi)≤m₁ → length Z (Real.exp high)≤m₂ →
      (∀l,lx l∈Set.Icc lo hi) → (∀l,ly l∈Set.Icc low high) →
      0≤A → (∀l,0≤weight l) → (∀l,weight l≤A) →
      let N:=fun l : labels=>naturalRow η (nonzeroJointSourceRow l.val).val
        (nonzeroJointSourceRow l.val).property
      (∑l : labels,weight l*‖polynomial (excluded (N l).character (R*H)) false W₁ (Real.exp (lx l)) 0 0*
        polynomial (excluded (N l).character (R*H)) false W₂ (Real.exp (ly l)) 0 0*
        ∏i∈F,naturalSlot (excluded (N l).character (R*H))
          (primePool rayModulus Hray slotUpper (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))‖^2)≤
      C*Z^loss*A*((∏I∈ps (R*H),I).absNorm:ℝ)^εmask*
        ((1+2*(hi-lo))*((1+2*(high-low))*
          rawSourceBudget CP CN DP DN TP TN degreeP degreeN Φ W₁ W₂ t height Z M εsource)) := by
  obtain ⟨TP,DP,hDP,hprior⟩ := initialAffineAt_derivative_uniform (α:=α) rayModulus Hray hH SP
  obtain ⟨TN,DN,hDN,hnatural⟩ := initialNaturalAt_derivative_uniform (α:=α) rayModulus Hray hH SN
  obtain ⟨C,hC,hraw⟩ := actual_fixed_missing_weighted_raw_moment F (fun _=>slotUpper) Mslot
    hMslot B loss εmask hB hloss hεmask
  refine ⟨TP,DP,TN,DN,C,hDP,hDN,hC,?_⟩
  intro face Kcap W a b bΦ mesh σlo σhi Mmin Mmax εsource Z hZ₂
    η η₀ Q degreeP degreeN CP CN hCP hCN hp hn left u₀ unit H hH0 labels
    hrow hsupport hsupported heq hnorm hmissing R hR hkeep W₁ W₂ hb hs₁ hs₂
    θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
    M m₁ m₂ cap hMlo hMhi hcaps hcap Φ hΦs hΦ
    lo hi low high A lx ly weight hcover hlo hlow hm₁ hm₂ hlx hly hA hweight hweightA N
  have hZ : 1<Z := by linarith
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hbudget : 0≤rawSourceBudget CP CN DP DN TP TN degreeP degreeN Φ W₁ W₂ t height Z M εsource := by
    unfold rawSourceBudget
    have hd := QuadraticInitialBound.diagonalControl_nonneg Φ
    positivity
  apply hraw left u₀ unit Z hZ₂ H hH0 labels hrow hsupport hsupported heq hnorm hmissing
    η (internalQ Q η₀) R hR hkeep W₁ W₂ a b hb hs₁ hs₂
    (fun i=>primePool rayModulus Hray slotUpper (Z^(w i)))
    (fun i=>relativeCharacter rayModulus Hray hH η₀ (θ i)) (fun _=>W)
    (fun i=>Z^(w i)) σ freq t hprime (fun i _=>Real.rpow_pos_of_pos hZ0 _) hβ hslot
    Φ (Z^M) _ lo hi low high A lx ly weight (Real.rpow_pos_of_pos hZ0 _) hΦ hcover
    hbudget hlo hlow hlx hly hA hweight hweightA
  intro D₁ hD₁ D₂ hD₂ J hJ j k x hx y hy
  have hlen₁ := (puncture_log_length_le Z x hi hZ (R*H) D₁ hD₁ hx.2).trans hm₁
  have hlen₂ := (puncture_log_length_le Z y high hZ (R*H) D₂ hD₂ hy.2).trans hm₂
  have hshort : (∑i∈F\J,w i)≤cap :=
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun i hi _=>hw i hi)).trans hcap
  rcases downward_completion hcaps hlen₁ hlen₂ hshort with hadmit | hadmit
  · have he := hprior face W slotUpper a b bΦ mesh σlo σhi Mmin Mmax εsource Z hZ0
      η η₀ Q degreeP CP hCP hp F θ w σ freq t height hw hwm hσlo hσhi hh hv
      J M hMlo hMhi Φ hΦs hΦ W₁ W₂ hs₁ hs₂ j k (Real.exp x) (Real.exp y)
      (Real.exp_pos _) (Real.exp_pos _) hadmit
    apply he.trans
    unfold rawSourceBudget
    apply le_add_of_nonneg_right
    have hd := QuadraticInitialBound.diagonalControl_nonneg Φ
    positivity
  · have he := hnatural Kcap W slotUpper a b bΦ mesh σlo σhi Mmin Mmax εsource Z hZ0
      η η₀ Q degreeN CN hCN hn F θ w σ freq t height hw hwm hσlo hσhi hh hv
      J M hMlo hMhi Φ hΦs hΦ W₁ W₂ hs₁ hs₂ j k (Real.exp x) (Real.exp y)
      (Real.exp_pos _) (Real.exp_pos _) hadmit
    apply he.trans
    unfold rawSourceBudget
    apply le_add_of_nonneg_left
    have hd := QuadraticInitialBound.diagonalControl_nonneg Φ
    positivity

end
end OAI.SevenEighths.Record12518109Raw
#print axioms OAI.SevenEighths.Record12518109Raw.puncture_log_length_le
#print axioms OAI.SevenEighths.Record12518109Raw.actual_fixed_missing_source_moment
