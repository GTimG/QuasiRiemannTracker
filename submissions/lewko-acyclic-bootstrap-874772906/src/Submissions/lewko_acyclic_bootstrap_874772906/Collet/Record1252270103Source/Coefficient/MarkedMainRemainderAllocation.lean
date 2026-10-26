/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual selected-allocation controls for the marked MAIN remainders.
Both allocation cards and the original raw-volume normalization are retained. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialPhysicalChildBounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocationCost
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.MarkedMainRemainder
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale CenteredMomentCommonRawCost
open CenteredMomentAllocationCost CenteredMomentOriginalCommonHarmonic Record1252270103Second
open CenteredMomentSourceInputTailUniform (plainControl plainControl_nonneg)
open QRH.Record1252270103Source.InitialPhysical
local notation "O"=>HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance markedMainRemainderDecidable : DecidableEq ι:=Classical.decEq _

theorem slot_control_product (s : Input ι) (N : ℕ) (Cs : ℝ)
    (hN : Fintype.card ι≤N) (hCs : 1≤Cs) (hM : ∀i,s.M i≤Cs) :
    (∏i,s.M i)≤Cs^N := by
  calc
    _≤∏_i:ι,Cs := Finset.prod_le_prod₀
      (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _=>hM i)
    _=Cs^Fintype.card ι := by simp
    _≤Cs^N := pow_le_pow_right₀ hCs hN

theorem selected_frozen_norm (s : Input ι) (N : ℕ) (Cs : ℝ)
    (hN : Fintype.card ι≤N) (hCs : 1≤Cs) (hM : ∀i,s.M i≤Cs)
    (C R : Ideal O) (B : actualAllocations s.pools C) :
    ‖frozenCoefficient B.val C R s.ν s.W s.P‖≤Cs^N :=
  (frozenCoefficient_norm B.val C R s.ν s.W s.P s.M s.ν_bound s.W_bound s.M_ge_one).trans
    (slot_control_product s N Cs hN hCs hM)

theorem selected_child_plain_control (s : Input ι) (N : ℕ) (Cs : ℝ)
    (hN : Fintype.card ι≤N) (hCs : 1≤Cs) (hM : ∀i,s.M i≤Cs)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) :
    plainControl (child s C R B τ t) W₁ W₂≤
      Cs^N*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂) := by
  have hn:Fintype.card (liveIndices B.val)≤N := by
    calc
      _≤Fintype.card ι := by simpa only [Fintype.card_coe] using Finset.card_le_univ (liveIndices B.val)
      _≤N := hN
  have hp:=slot_control_product (child s C R B τ t) N Cs hn hCs (fun i=>hM i.val)
  have hh:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hp (apply_nonneg (SchwartzMap.seminorm ℝ 0 0) W₁))
    (apply_nonneg (SchwartzMap.seminorm ℝ 0 0) W₂)
  simpa only [plainControl,mul_assoc] using hh

theorem uniform_allocation_card_square (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀{ι : Type*}[Fintype ι](s : Input ι),Fintype.card ι≤N→
    ∀C : Ideal O,C≠0→((actualAllocations s.pools C).card:ℝ)^2≤D*(C.absNorm:ℝ)^ε := by
  obtain ⟨D,hD,hcard⟩:=actualAllocations_uniform_small_power (N+2) (ε/2) (half_pos hε)
  refine ⟨D^2,sq_pos_of_pos hD,?_⟩
  intro ι _ s hN C hC
  have hc:=hcard (ι:=ι⊕Fin 2) (by simpa only [Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_right hN 2)
    s.pools C hC
  have hh:=pow_le_pow_left₀ (Nat.cast_nonneg (actualAllocations s.pools C).card) hc 2
  rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg _),show ε/2*(2:ℕ)=ε by norm_num] at hh
  exact hh

/-- The selected nonzero frozen coefficient gives the norm comparison;
the deleted marked scales are not identified with the ideal norm. -/
theorem selected_child_volume_ratio (s : Input ι) (N : ℕ) (bs : ℝ)
    (hN : Fintype.card ι≤N) (hbs : 1≤bs) (hupper : s.upper≤bs)
    (C R : Ideal O) (hC : C≠0) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hf : frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    volume (child s C R B τ t)/volume s≤bs^N/(C.absNorm:ℝ) := by
  have hb:=alloc_ne s C B
  have hprod : finiteTupleProduct B.val=C := (Finset.mem_filter.mp B.property).2
  have hred:=rawReduction_pos B.val hb s.P s.P_pos
  have hn:=(actual_reduction_norm B.val hb C R hprod s.ν s.W s.P s.P_pos
    s.lower s.upper s.lower_pos s.slot_support hf).2
  have hp:(max 1 s.upper)^Fintype.card ι≤bs^N :=
    (pow_le_pow_left₀ (by positivity) (max_le hbs hupper) _).trans (pow_le_pow_right₀ hbs hN)
  have hn':(C.absNorm:ℝ)≤rawReduction B.val s.P*bs^N :=
    hn.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp hred.le)
  have hv:volume (child s C R B τ t)*rawReduction B.val s.P=volume s := by
    rw [child_volume_remaining]
    exact raw_scale_identity B.val hb (s.X₁*s.X₂) s.P
  have hNC:(0:ℝ)<C.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  apply (div_le_div_iff₀ (volume_pos s) hNC).mpr
  calc
    _≤volume (child s C R B τ t)*(rawReduction B.val s.P*bs^N) :=
      mul_le_mul_of_nonneg_left hn' (volume_pos _).le
    _=bs^N*volume s := by rw [←hv];ring

/-- A genuine fixed annular constant supplies Lambda=Cann/NC for the
second zero term, with the original parent volume T. -/
theorem selected_child_radius_cap (s : Input ι) (N : ℕ) (hi bs b : ℝ)
    (hN : Fintype.card ι≤N) (hhi : 1≤hi) (hbs : 1≤bs) (hb : 0≤b)
    (hslot0 : ∀i,0≤s.hi i) (hslot : ∀i,s.hi i≤hi) (hupper : s.upper≤bs)
    (hb₁ : 0≤s.b₁) (hb₂ : 0≤s.b₂) (h₁ : s.b₁≤b) (h₂ : s.b₂≤b)
    (C R : Ideal O) (hC : C≠0) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hf : frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    sourceRadius (child s C R B τ t)≤(hi^N*b^2*bs^N/(C.absNorm:ℝ))*volume s := by
  have hn:Fintype.card (liveIndices B.val)≤N := by
    calc
      _≤Fintype.card ι := by simpa only [Fintype.card_coe] using Finset.card_le_univ (liveIndices B.val)
      _≤N := hN
  have hp:(∏i:liveIndices B.val,s.hi i.val)≤hi^N := by
    calc
      _≤∏_i:liveIndices B.val,hi := Finset.prod_le_prod₀
        (fun i _=>hslot0 i.val) (fun i _=>hslot i.val)
      _=hi^Fintype.card (liveIndices B.val) := by simp
      _≤hi^N := pow_le_pow_right₀ hhi hn
  have hvol:=selected_child_volume_ratio s N bs hN hbs hupper C R hC B τ t hf
  have hvol':volume (child s C R B τ t)≤(bs^N/(C.absNorm:ℝ))*volume s :=
    (div_le_iff₀ (volume_pos s)).mp hvol
  rw [sourceRadius_volume]
  change (∏i:liveIndices B.val,s.hi i.val)*s.b₁*s.b₂*volume (child s C R B τ t)≤_
  have hplain:s.b₁*s.b₂≤b^2 := by nlinarith
  have hp':(∏i:liveIndices B.val,s.hi i.val)*s.b₁*s.b₂≤hi^N*b^2 := by
    simpa only [mul_assoc] using mul_le_mul hp hplain (mul_nonneg hb₁ hb₂) (pow_nonneg (zero_le_one.trans hhi) _)
  exact (mul_le_mul hp' hvol' (volume_pos _).le (by positivity)).trans_eq (by ring)

end
end QRH.Record1252270103Source.MarkedMainRemainder
#print axioms QRH.Record1252270103Source.MarkedMainRemainder.slot_control_product
#print axioms QRH.Record1252270103Source.MarkedMainRemainder.selected_frozen_norm
#print axioms QRH.Record1252270103Source.MarkedMainRemainder.selected_child_plain_control
#print axioms QRH.Record1252270103Source.MarkedMainRemainder.uniform_allocation_card_square
#print axioms QRH.Record1252270103Source.MarkedMainRemainder.selected_child_volume_ratio
#print axioms QRH.Record1252270103Source.MarkedMainRemainder.selected_child_radius_cap
