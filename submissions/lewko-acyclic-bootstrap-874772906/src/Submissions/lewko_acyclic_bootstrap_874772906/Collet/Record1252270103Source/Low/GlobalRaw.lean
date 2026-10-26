/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Raw.SourceMoment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.RawCaps

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Low
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
open QRH.Record12518109Source Record12518109Raw QRH.Record1252270103Low
local notation "O" => HeckeFamily.O
local notation "ps" => CompletedGauss.primeSupport

/-- The single strictly earlier global source budget, uniform over all derivative
choices. It contains no natural-fallback partner. -/
def globalRawBudget (CP DP : ℝ) (TP : Finset (ℕ×ℕ)) (degreeP : ℕ)
    (Φ W₁ W₂ : 𝓢(ℝ,ℂ)) (t height Z M ε : ℝ) : ℝ :=
  CP*QuadraticInitialBound.diagonalControl Φ*
    (DP*(sourceControl TP W₁*sourceControl TP W₂))^2*
    (1+|t|+height)^degreeP*Z^(M+ε)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayModulus : Ideal O) [NeZero rayModulus]
local instance : Finite (O ⧸ rayModulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (Hray : Subgroup (O ⧸ rayModulus)ˣ)
variable (hH : RayOrthogonality.globalUnits rayModulus ≤ Hray)

/-- The literal fixed-missing RAW norm from a strictly earlier global source.
All common-mask deletion branches enter by total capacity, including every
shortened plain and zero-slot branch. The exact ray character, full puncture
R*H, inherited height and original zero filter remain in the conclusion.
The constant is fixed before the surviving slot set, radius and row selectors. -/
theorem global_fixed_missing_source_moment_all_slots
    (Mslot : α→ℝ) (hMslot : ∀i,0≤Mslot i)
    (slotUpper B loss εmask : ℝ) (hB : 0≤B) (hloss : 0<loss) (hεmask : 0<εmask)
    (SP : Finset (ℕ×ℕ)) :
    ∃TP : Finset (ℕ×ℕ), ∃DP C : ℝ, 0<DP ∧ 0<C ∧
    ∀F : Finset α,
    ∀(Bprev lam hprev : ℝ), 0≤lam → ∀(W : ℝ→ℂ)
      (a b bΦ mesh σlo σhi Mmin Mmax εsource Z : ℝ),2≤Z →
    ∀(η η₀ : Character)(Q : Ideal O)(degreeP : ℕ)(CP : ℝ), 0≤CP →
      InitialAffineAt (α:=α) rayModulus Hray hH (SourceFace.mk Bprev lam 0 Bprev 0 hprev) W
        slotUpper a b bΦ mesh σlo σhi Mmin Mmax εsource Z η η₀ Q degreeP SP CP →
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
    ∀(M m₁ m₂ cap : ℝ),Mmin≤M → M≤Mmax → cap≤hprev*M → m₁+m₂+lam*cap≤Bprev*M →
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
          globalRawBudget CP DP TP degreeP Φ W₁ W₂ t height Z M εsource)) := by
  obtain ⟨TP,DP,hDP,hprior⟩ := initialAffineAt_derivative_uniform (α:=α) rayModulus Hray hH SP
  choose C₀ hC₀ hraw using fun F : Finset α=>actual_fixed_missing_weighted_raw_moment F
    (fun _=>slotUpper) Mslot (fun i _=>hMslot i) B loss εmask hB hloss hεmask
  let C : ℝ:=1+∑F : Finset α,C₀ F
  have hC : 0<C:=by
    have hs:=Finset.sum_nonneg (s:=(Finset.univ:Finset (Finset α))) (fun F _=>(hC₀ F).le)
    dsimp only [C]
    linarith
  refine ⟨TP,DP,C,hDP,hC,?_⟩
  intro F Bprev lam hprev hlam W a b bΦ mesh σlo σhi Mmin Mmax εsource Z hZ₂
    η η₀ Q degreeP CP hCP hp left u₀ unit H hH0 labels
    hrow hsupport hsupported heq hnorm hmissing R hR hkeep W₁ W₂ hb hs₁ hs₂
    θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
    M m₁ m₂ cap hMlo hMhi hslotcap hcapacity hcap Φ hΦs hΦ
    lo hi low high A lx ly weight hcover hlo hlow hm₁ hm₂ hlx hly hA hweight hweightA N
  have hZ : 1<Z := by linarith
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hbudget : 0≤globalRawBudget CP DP TP degreeP Φ W₁ W₂ t height Z M εsource := by
    unfold globalRawBudget
    have hd := QuadraticInitialBound.diagonalControl_nonneg Φ
    positivity
  have hCF : C₀ F≤C:=by
    have hs:=Finset.single_le_sum (s:=(Finset.univ:Finset (Finset α)))
      (f:=C₀) (fun G _=>(hC₀ G).le) (Finset.mem_univ F)
    dsimp only [C]
    linarith
  have hscale : 0≤(1+2*(hi-lo))*((1+2*(high-low))*
      globalRawBudget CP DP TP degreeP Φ W₁ W₂ t height Z M εsource):=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) hbudget)
  apply le_trans _ (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCF (Real.rpow_nonneg hZ0.le loss)) hA)
        (Real.rpow_nonneg (Nat.cast_nonneg _) εmask)) hscale)
  apply hraw F left u₀ unit Z hZ₂ H hH0 labels hrow hsupport hsupported heq hnorm hmissing
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
  have hadmit := global_shortening_admission Bprev lam hprev m₁ m₂ cap M
    (length Z (Real.exp x)) (length Z (Real.exp y)) (∑i∈F\J,w i)
    hlam (length_nonneg _ _ hZ) (length_nonneg _ _ hZ)
    (Finset.sum_nonneg (fun i hi => hw i (Finset.mem_sdiff.mp hi).1))
    hlen₁ hlen₂ hshort hslotcap hcapacity
  exact hprior (SourceFace.mk Bprev lam 0 Bprev 0 hprev) W
    slotUpper a b bΦ mesh σlo σhi Mmin Mmax εsource Z hZ0
    η η₀ Q degreeP CP hCP hp F θ w σ freq t height hw hwm hσlo hσhi hh hv
    J M hMlo hMhi Φ hΦs hΦ W₁ W₂ hs₁ hs₂ j k (Real.exp x) (Real.exp y)
    (Real.exp_pos _) (Real.exp_pos _) hadmit

end
end OAI.SevenEighths.Record1252270103Low
#print axioms OAI.SevenEighths.Record1252270103Low.global_fixed_missing_source_moment_all_slots
