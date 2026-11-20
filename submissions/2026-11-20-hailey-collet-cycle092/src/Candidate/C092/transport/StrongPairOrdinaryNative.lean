/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine native ordinary collar: one marked fourth and one freely small-error
unmarked fourth. This permits the actual witness m>.5 without changing it. -/
import Candidate.C092.transport.StrongPairOrdinaryUnmarked

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
local notation "O" => ActualEisensteinCubic.O
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
variable (hH : RayOrthogonality.globalUnits M ≤ H)

theorem marked_unmarked_pair_at {N Y l bΦ mesh ε ε₀ Z C₁ C₂ : ℝ} {W : ℝ→ℂ}
    {η₁ η₂ η₀₁ η₀₂ : Character} {Q₁ Q₂ : Ideal O} {d₁ d₂ : ℕ} {S₁ S₂ : Finset (ℕ×ℕ)}
    (hY : Y ≤ 1) (hε : ε₀ ≤ ε) (hZ : 1 < Z) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hΦs : Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ)
    (hsrc : LabelledAt (α:=Fin 2×Slot) M H hH N N (2*l) W 2 (1/4) (9/4) bΦ mesh
      (33/50) (33/50) 1 1 ε₀ Z η₁ η₀₁ Q₁ d₁ S₁ C₁)
    (hshort : ∀ (p : Profiles (1/4) (9/4)) (j : Fin 2) (t height X : ℝ),
      0 ≤ height → 0 < X → X ≤ Z →∀ s : Finset FreeRow,
      (∀ u∈s,initialKeep η₂ (internalQ Q₂ η₀₂) u.val) → (∀ u∈s,rowNorm u ≤ Z) →
      (∑ u∈s,‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile j) t X‖^4) ≤
      C₂*QuadraticInitialBound.diagonalControl radialMajorant*(sourceControl S₂ (p.profile j))^4*
        (1+|t|+height)^d₂*Z^(1+ε₀)) :
    PairAt (Slot:=Slot) M H hH N Y l W bΦ mesh ε Z η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
      (max d₁ d₂) (S₁∪S₂) (C₁+C₂+1) := by
  intro T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hlo₁ hhi₁ hlo₂ hhi₂ hh hv₁ hv₂ hsum
    p X₁ X₂ hX₁ hX₂ hXN hXY s mark hk₁ hk₂ hy hm₁ hm₂
  have hX₂Z : X₂ ≤ Z := by
    have hlen : Real.logb Z (max 1 X₂) ≤ 1 := hXY.trans hY
    have hmax := (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le (le_max_left _ _))).mp hlen
    exact (le_max_right 1 X₂).trans (by simpa only [Real.rpow_one] using hmax)
  have hL := native_arm M H hH hsrc T θ₁ w σ₁ v₁ t₁ height hw hwm hlo₁ hhi₁ hh hv₁ hΦs p 0 X₁ hX₁
    hZ hXN (by linarith) s mark hk₁ hy hm₁
  have hR := hshort p 1 t₂ height X₂ hh hX₂ hX₂Z s hk₂ hy
  let G := (C₁+C₂+1)*QuadraticInitialBound.diagonalControl radialMajorant*
    (1+|t₁|+|t₂|+height)^(max d₁ d₂)*Z^(1+ε)
  let A := sourceControl (S₁∪S₂) (p.profile 0)
  let B := sourceControl (S₁∪S₂) (p.profile 1)
  have hd := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  have hheight : 1 ≤ 1+|t₁|+|t₂|+height := by linarith [abs_nonneg t₁,abs_nonneg t₂]
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hp₁ : (1+|t₁|+height)^d₁ ≤ (1+|t₁|+|t₂|+height)^(max d₁ d₂) :=
    (pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg t₂]) _).trans (pow_le_pow_right₀ hheight (le_max_left _ _))
  have hp₂ : (1+|t₂|+height)^d₂ ≤ (1+|t₁|+|t₂|+height)^(max d₁ d₂) :=
    (pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg t₁]) _).trans (pow_le_pow_right₀ hheight (le_max_right _ _))
  have hpZ : Z^(1+ε₀) ≤ Z^(1+ε) := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hA := control_mono S₁ (S₁∪S₂) Finset.subset_union_left (p.profile 0)
  have hB := control_mono S₂ (S₁∪S₂) Finset.subset_union_right (p.profile 1)
  have hL' : (∑ u∈s,(‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 0) t₁ X₁‖^2*
      ∏ i∈T,‖mark i u‖^2)^2) ≤ G*A^4 := by
    apply hL.trans
    dsimp [G,A]
    have hc : C₁ ≤ C₁+C₂+1 := by linarith
    have ha := sourceControl_nonneg S₁ (p.profile 0)
    calc
      _ ≤ (C₁+C₂+1)*QuadraticInitialBound.diagonalControl radialMajorant*
        (sourceControl (S₁∪S₂) (p.profile 0))^4*(1+|t₁|+|t₂|+height)^(max d₁ d₂)*Z^(1+ε) := by gcongr
      _ = _ := by ring
  have hR' : (∑ u∈s,‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 1) t₂ X₂‖^4) ≤ G*B^4 := by
    apply hR.trans
    dsimp [G,B]
    have hc : C₂ ≤ C₁+C₂+1 := by linarith
    have hb := sourceControl_nonneg S₂ (p.profile 1)
    calc
      _ ≤ (C₁+C₂+1)*QuadraticInitialBound.diagonalControl radialMajorant*
        (sourceControl (S₁∪S₂) (p.profile 1))^4*(1+|t₁|+|t₂|+height)^(max d₁ d₂)*Z^(1+ε) := by gcongr
      _ = _ := by ring
  have hcs := finite_split_cauchy_on T T le_rfl s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark
  simp only [Finset.sdiff_self,Finset.prod_empty,mul_one,←pow_mul,show (2:ℕ)*2=4 from rfl] at hcs
  have h := hcs.trans (common_cauchy_factor hG hL' hR')
  convert h using 1 <;> dsimp [G,A,B,Profiles.control] <;> ring

/-- This is an actual source, not an assumed unmarked fourth. Its positive
error is freely chosen before the finite arithmetic data. -/
theorem native_marked_unmarked_box (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {N Y l : ℝ} (hN : N ≤ 1/2) (hY : Y ≤ 1) (hl0 : 0 ≤ l)
    (hlcap : 2*l < 3/20) (hlmean : 2*l < (1-2*N)/2) : PairUniformBox N Y l := by
  intro ε hε
  let ε₀ := min ε (1/2:ℝ)
  have hε₀ : 0 < ε₀ := lt_min hε (by norm_num)
  have hε₀1 : ε₀ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hε₀ε : ε₀ ≤ ε := min_le_left _ _
  obtain ⟨mesh,hm,hsource⟩ := QRH.Cycle092.LowActual.native_mean_box hβ hN hN
    (by positivity : (0:ℝ) ≤ 2*l) hlcap (by linarith) ε₀ hε₀
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _ M _ H hH W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  obtain ⟨d₁,S₁,C₁,hC₁,hs₁⟩ := hsource (Fin 2×Slot) M H hH W hW hWs bΦ hbΦ η₁ η₀₁ Q₁
    hQ₁ray hQ₁0 hQ₁top hQ₁72
  obtain ⟨d₂,S₂,C₂,hC₂,hs₂⟩ := freely_small_unmarked_fourth hβ M H hH bΦ ε₀ (by linarith)
    hε₀ hε₀1 hΦs η₂ η₀₂ Q₂ hQ₂ray hQ₂0 hQ₂top hQ₂72
  refine ⟨max d₁ d₂,S₁∪S₂,C₁+C₂+1,by positivity,?_⟩
  filter_upwards [hs₁,hs₂,eventually_gt_atTop (1:ℝ)] with Z hs₁ hs₂ hZ
  exact marked_unmarked_pair_at M H hH hY hε₀ε hZ hC₁.le hC₂.le hΦs hs₁ (hs₂ hZ.le)

#print axioms native_marked_unmarked_box
end
end QRH.Cycle092.StrongPair
