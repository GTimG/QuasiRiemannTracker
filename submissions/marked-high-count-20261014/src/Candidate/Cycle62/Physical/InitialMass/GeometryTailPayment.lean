/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Physical.InitialMass.GeometryHighPayment
import Candidate.Cycle62.Physical.InitialMass.GeometryZeroPayment

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve Cycle62Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstScale
open CenteredMomentLogDyadic CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
local instance tailPaymentDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Coarse actual scalar mass for arbitrary-power tail payment. No moving
first-label power remains outside the fixed physical-D factor. -/
theorem actual_geometry_tail_mass_box {ι : Type} [Fintype ι] [DecidableEq ι]
    (reflected : Bool)(N : ℕ)(lo ap : ℝ)(hlo : 0<lo)(hap : 0<ap)
    (s : Input ι)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(M Z ξ B εmass : ℝ)
    (hZ : 1<Z)(hK : 0<Z^M)(hB : 0≤B)(hem : 0≤εmass)
    (hn : Fintype.card ι≤N)(hl : lo≤s.lower)(hs : Squarefree seed)
    (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)(hsource : sourceRadius s≤Z^B)
    (hA : |Real.logb Z (volume s)|≤B)
    (hs₁ : ∀x,s.W₁ x≠0→ap≤x)(hs₂ : ∀x,s.W₂ x≠0→ap≤x)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK key)) :
    geometryFirstHighMass reflected s R seed W M Z ξ εmass hK key j≤
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) key*Z^(B*εmass+5*B) := by
  have hm := actual_geometry_uniform_high_mass reflected N lo ap hlo hap s R seed W M Z ξ B εmass
    hZ hK hem hn hl hs hz₁ hz₂ hsource hs₁ hs₂ key j
  have hbox := geometry_high_side_box reflected _ B _ hB hA (by
    intro i
    have h := actual_geometry_norm_caps s R seed (Z^M) Z ξ B hs hz₁ hz₂ hsource j.1.val i
    exact ⟨Real.logb_nonneg hZ h.1,(Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le h.1)).mpr h.2⟩)
  change |geometryHighSide reflected (Real.logb Z (CenteredMomentExceptionalAmplitudePair.volume s.toData))
    (geometryExponents s R seed (Z^M) Z ξ j.1.val)|≤5*B at hbox
  apply hm.trans
  rw [mul_div_assoc,←Real.rpow_sub (zero_lt_one.trans hZ)]
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [abs_le.mp hbox]))
    (geometry_high_factor_pos reflected _ key (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le

/-- The complete actual first-column mass, times any additional radius
power, is paid by true first-label/projector counting and the original seed. -/
theorem eventual_actual_geometry_tail_column_payment {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ)(lo ap B L ξ εmass εcount : ℝ)(hlo : 0<lo)(hap : 0<ap)
    (hB : 0≤B)(hL : 0≤L)(hξ : 0≤ξ)(hem : 0≤εmass)(hec : 0<εcount) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(s : Input ι)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(M T : ℝ)(hZ : 1<Z),
      Fintype.card ι≤N → lo≤s.lower → Squarefree seed → seed≠0 →
      s.W₁ 0=0 → s.W₂ 0=0 → 0<sourceRadius s → sourceRadius s≤Z^B →
      |Real.logb Z (volume s)|≤B → 0≤M →
      (∀x,s.W₁ x≠0→ap≤x) → (∀x,s.W₂ x≠0→ap≤x) →
    ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    ∀rows : Finset (FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK key)),
      rows⊆firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK key) (fun _=>logAnnulus) →
      (∀j∈rows,(j.2.1.val.absNorm:ℝ)≤Z^L) →
      (∑j : rows,geometryFirstHighMass reflected s R seed W M Z ξ εmass hK key j.val*Z^T)≤
        C*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) key*
          Z^(B*εmass+T+6*B+L+3*εcount)/(seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := eventual_actual_zero_column_payment (ι:=ι)
    B 0 B L ξ εcount hB (by norm_num) hB hL hξ hec
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro s R seed W M T hZ hn hl hs hs0 hz₁ hz₂ hsource hcap hA hM hs₁ hs₂ reflected key hK rows hrows hpool
  have hV : volume s≤Z^B := by
    apply (Real.logb_le_iff_le_rpow hZ (volume_pos s)).mp
    exact (abs_le.mp hA).2
  have hKi : (Z^M)⁻¹≤Z^(0:ℝ) := by
    rw [Real.rpow_zero]; exact inv_le_one_of_one_le₀ (Real.one_le_rpow hZ.le hM)
  apply hz.2 s R seed (Z^M) hK key hs hs0 hz₁ hz₂ hsource hcap hV hKi rows
    (fun j hj=>actual_first_live_squarefree _ _ j (hrows hj)) hpool
    (geometryHighFactor reflected (geometrySupportConstant N lo ap ap) key)
    (B*εmass+T+6*B+L) _
    (geometry_high_factor_pos reflected _ key (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le
    (fun j=>mul_nonneg (geometry_first_high_mass_nonneg reflected s R seed W M Z ξ εmass hK key j.val)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
  intro j
  let factor := geometryHighFactor reflected (geometrySupportConstant N lo ap ap) key
  have hm := actual_geometry_tail_mass_box reflected N lo ap hlo hap s R seed W M Z ξ B εmass
    hZ hK hB hem hn hl hs hz₁ hz₂ hcap hA hs₁ hs₂ key j.val
  have hg := actual_geometry_norm_caps s R seed (Z^M) Z ξ B hs hz₁ hz₂ hcap j.val.1.val 2
  have hv : geometryExponents s R seed (Z^M) Z ξ j.val.1.val 2≤B :=
    (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hg.1)).mpr hg.2
  have hD := actual_first_divisor_ne_zero (geometryFirstSource s R seed (Z^M) Z ξ hK key j.val.1) j.val.2.1
  have hDlog : Real.logb Z (j.val.2.1.val.absNorm:ℝ)≤L :=
    (Real.logb_le_iff_le_rpow hZ (norm_pos _ hD)).mpr (hpool j.val j.property)
  apply zero_cost_power_payment Z _ factor T 0 (B*εmass+5*B) (B*εmass+T+6*B+L)
    (geometryExponents s R seed (Z^M) Z ξ j.val.1.val 2) (j.val.2.1.val.absNorm:ℝ)
    hZ (norm_pos _ hD)
    (geometry_high_factor_pos reflected _ key (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le
    (by simpa only [Real.rpow_zero,div_one] using hm) (by linarith)

/-- Actual common allocation multiplicities and frozen controls are included
in the same arbitrary-power payment; no allocation cardinality is assumed. -/
theorem eventual_actual_geometry_tail_allocation_payment {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ)(Cs bs lo ap B U ξ εmass εcount : ℝ)(hCs : 1≤Cs)
    (hlo : 0<lo)(hap : 0<ap)(hB : 0≤B)(hU : 0≤U)(hξ : 0≤ξ)
    (hem : 0<εmass)(hec : 0<εcount) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(s : Input ι)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(M T : ℝ)(hZ : 1<Z),
      Fintype.card ι≤N → (∀j,s.M j≤Cs) → lo≤s.lower → Squarefree seed → seed≠0 →
      s.W₁ 0=0 → s.W₂ 0=0 → 0<sourceRadius s → sourceRadius s≤Z^B →
      |Real.logb Z (volume s)|≤B → 0≤M →
      (∀x,s.W₁ x≠0→ap≤x) → (∀x,s.W₂ x≠0→ap≤x) →
      (∀j I,I∈s.pools j→(I.absNorm:ℝ)≤Z^U) →
    ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    let A := Real.logb Z (volume s)
    let rows := firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK key) (fun _=>logAnnulus)
    let weight := fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)
    (∑j : rows,∑alloc : actualAllocations s.pools
      (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j.val),
      geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N bs j.val alloc*Z^T)≤
      C*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) key*
        Z^(B*εmass+T+6*B+((N:ℝ)+2)*U+3*εcount)/(seed.absNorm:ℝ) := by
  obtain ⟨D,hD,hmass⟩ := actual_geometry_allocation_mass N Cs bs εmass hCs hem
  obtain ⟨C,hC,hbound⟩ := eventual_actual_geometry_tail_column_payment (ι:=ι) N lo ap B
    (((N:ℝ)+2)*U) ξ εmass εcount hlo hap hB (by positivity) hξ hem.le hec
  refine ⟨D*C,mul_pos hD hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro s R seed W M T hZ hn hM hl hs hs0 hz₁ hz₂ hsource hcap hA hMrow hs₁ hs₂ hpool
    reflected key hK A rows weight
  have hpayment := hz.2 s R seed W M T hZ hn hl hs hs0 hz₁ hz₂ hsource hcap hA hMrow hs₁ hs₂
    reflected key rows (Finset.Subset.refl _)
    (fun j _=>actual_geometry_projector_cap s N R seed (Z^M) Z ξ U hK hn hZ.le hU hpool key j)
  have hcolumn (j : rows) : geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j.val≠0 := by
    cases reflected
    · exact (geometryFirstSource s R seed (Z^M) Z ξ hK key j.val.1).hC.1
    · exact (geometryFirstSource s R seed (Z^M) Z ξ hK key j.val.1).hD.1
  calc
    _≤∑j : rows,D*(geometryFirstHighMass reflected s R seed W M Z ξ εmass hK key j.val*Z^T) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [←Finset.sum_mul]
      have hh := hmass s hn hM reflected R seed (Z^M) Z ξ M A hK key weight j.val (hcolumn j)
      apply (mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)).trans_eq
      dsimp only [geometryFirstHighMass,A,weight,CenteredMomentAmplificationChildInput.volume,
        CenteredMomentExceptionalAmplitudePair.volume]
      ring
    _=D*(∑j : rows,geometryFirstHighMass reflected s R seed W M Z ξ εmass hK key j.val*Z^T) :=
      (Finset.mul_sum _ _ _).symm
    _≤D*_ := mul_le_mul_of_nonneg_left hpayment hD.le
    _=_ := by ring

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_tail_mass_box
#print axioms OAI.SevenEighths.Cycle62InitialMass.eventual_actual_geometry_tail_column_payment
#print axioms OAI.SevenEighths.Cycle62InitialMass.eventual_actual_geometry_tail_allocation_payment
