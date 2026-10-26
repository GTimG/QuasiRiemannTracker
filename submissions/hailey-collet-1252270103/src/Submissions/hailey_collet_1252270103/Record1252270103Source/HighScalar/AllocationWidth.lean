/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Three literal common allocations retain the original marked slot widths.
The third allocation is the optional forced common divisor. -/
import Submissions.hailey_collet_1252270103.Record12518109Natural.CommonSurvivingSlots
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.HighScalar
noncomputable section
open OAI OAI.SevenEighths Record12518109Natural CommonSupply MarkedPlain
open scoped Classical BigOperators
open Filter HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentAllocatedChildCapacity
open CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem actual_three_stage_live_width (N : ℕ) (a : ℝ) (ha : 0<a)
    (s : Input ι) (hcard : Fintype.card ι≤N) (hs : a≤s.lower)
    (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (hf₁ : frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P≠0)
    (χ₁ : Character) (t₁ : ℝ) (C₂ R₂ : Ideal O)
    (B₂ : actualAllocations (child s C₁ R₁ B₁ χ₁ t₁).pools C₂)
    (hf₂ : let first:=child s C₁ R₁ B₁ χ₁ t₁
      frozenCoefficient B₂.val C₂ R₂ first.ν first.W first.P≠0)
    (χ₂ : Character) (t₂ : ℝ) (C₃ R₃ : Ideal O)
    (B₃ : actualAllocations (child (child s C₁ R₁ B₁ χ₁ t₁) C₂ R₂ B₂ χ₂ t₂).pools C₃)
    (hf₃ : let second:=child (child s C₁ R₁ B₁ χ₁ t₁) C₂ R₂ B₂ χ₂ t₂
      frozenCoefficient B₃.val C₃ R₃ second.ν second.W second.P≠0)
    (Z : ℝ) (hZ : 1<Z) :
    (∑i,Real.logb Z (s.P i))-Real.logb Z (C₁.absNorm:ℝ)-Real.logb Z (C₂.absNorm:ℝ)-
      Real.logb Z (C₃.absNorm:ℝ)+3*(N:ℝ)*Real.logb Z (min 1 a)≤
      ∑i : liveIndices B₃.val,Real.logb Z (s.P i.val.val.val) := by
  have h12:=actual_two_stage_live_width N a ha s hcard hs C₁ R₁ B₁ hf₁ χ₁ t₁ C₂ R₂ B₂ hf₂ Z hZ
  have h3:=actual_common_live_width N a ha
    (child (child s C₁ R₁ B₁ χ₁ t₁) C₂ R₂ B₂ χ₂ t₂)
    ((live_card_le B₂.val).trans ((live_card_le B₁.val).trans hcard)) hs C₃ R₃ B₃ hf₃ Z hZ
  change (∑i : liveIndices B₂.val,Real.logb Z (s.P i.val.val))-Real.logb Z (C₃.absNorm:ℝ)+
    (N:ℝ)*Real.logb Z (min 1 a)≤∑i : liveIndices B₃.val,Real.logb Z (s.P i.val.val.val) at h3
  linarith

/-- The threshold precedes every input and all three allocations. Only the
original finite cardinality and fixed annular lower bound enter it. -/
theorem eventual_three_common_large_width (N : ℕ) (a ε wmin : ℝ)
    (ha : 0<a) (hε : 0<ε) (hmin : 0≤wmin) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀s : Input ι,Fintype.card ι≤N →a≤s.lower →
    ∀(C₁ R₁ : Ideal O)(B₁ : actualAllocations s.pools C₁),
    frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P≠0 →
    ∀(χ₁ : Character)(t₁ : ℝ)(C₂ R₂ : Ideal O)
      (B₂ : actualAllocations (child s C₁ R₁ B₁ χ₁ t₁).pools C₂),
    (let first:=child s C₁ R₁ B₁ χ₁ t₁;
      frozenCoefficient B₂.val C₂ R₂ first.ν first.W first.P≠0) →
    ∀(χ₂ : Character)(t₂ : ℝ)(C₃ R₃ : Ideal O)
      (B₃ : actualAllocations (child (child s C₁ R₁ B₁ χ₁ t₁) C₂ R₂ B₂ χ₂ t₂).pools C₃),
    (let second:=child (child s C₁ R₁ B₁ χ₁ t₁) C₂ R₂ B₂ χ₂ t₂;
      frozenCoefficient B₃.val C₃ R₃ second.ν second.W second.P≠0) →
    ∀w : ι→ℝ,(∀i,s.P i=Z^(w i)) →(∀i,0≤w i) →
    let large:=largeSlots (originalSlots (fun i : liveIndices B₃.val=>i.val.val.val)) w wmin
    0≤∑i∈large,w i ∧(∑i∈large,w i)≤∑i,w i ∧
      (∑i,w i)-ε-(N:ℝ)*wmin≤Real.logb Z (C₁.absNorm:ℝ)+
        Real.logb Z (C₂.absNorm:ℝ)+Real.logb Z (C₃.absNorm:ℝ)+∑i∈large,w i := by
  filter_upwards [eventually_two_stage_width_padding (3*N) a (2*ε) ha (by positivity)] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s hcard hs C₁ R₁ B₁ hf₁ χ₁ t₁ C₂ R₂ B₂ hf₂ χ₂ t₂ C₃ R₃ B₃ hf₃ w hw hnonneg large
  have hh:=actual_three_stage_live_width N a ha s hcard hs C₁ R₁ B₁ hf₁ χ₁ t₁
    C₂ R₂ B₂ hf₂ χ₂ t₂ C₃ R₃ B₃ hf₃ Z hZ.1
  simp_rw [hw,Real.logb_rpow (zero_lt_one.trans hZ.1) hZ.1.ne'] at hh
  have hinj : Function.Injective (fun i : liveIndices B₃.val=>i.val.val.val) := by
    intro i j hij
    exact Subtype.ext (Subtype.ext (Subtype.ext hij))
  rw [sum_originalSlots _ hinj] at hh
  have hl:=large_width_lower (originalSlots (fun i : liveIndices B₃.val=>i.val.val.val)) w wmin N
    ((Finset.card_le_univ _).trans hcard) hmin
  have hz:=hZ.2
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hz
  refine ⟨Finset.sum_nonneg (fun i _=>hnonneg i),Finset.sum_le_univ_sum_of_nonneg hnonneg,?_⟩
  dsimp only [large]
  linarith only [hh,hl,hz]

/-- Allocate the two fixed errors to the source's existing width allowance. -/
lemma high_width_of_original_ledger {total live c₁ c₂ forced ε wmin D b allowance : ℝ} {N : ℕ}
    (htotal : D*b≤total) (hloss : ε+(N:ℝ)*wmin≤2*D*allowance)
    (hledger : total-ε-(N:ℝ)*wmin≤c₁+c₂+forced+live) :
    D*(b-2*allowance)≤live+c₁+c₂+forced := by nlinarith only [htotal,hloss,hledger]

end
end QRH.Record1252270103Source.HighScalar
#print axioms QRH.Record1252270103Source.HighScalar.actual_three_stage_live_width
#print axioms QRH.Record1252270103Source.HighScalar.eventual_three_common_large_width
#print axioms QRH.Record1252270103Source.HighScalar.high_width_of_original_ledger
