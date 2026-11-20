/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
All root-ball size caps on the actual divided source. Only the two original
ordinary coordinates are in the ordered box; the equal-product reference
may have a companion much longer than the old short label. -/
import Candidate.C092.transport.FirstRootInverseGeometry
import Candidate.C092.transport.RawSidesZeroTailGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP KernelRowPools KernelRowProfiles KernelRowExpansion
open MixedPrincipalPair MixedPrincipalWindow MixedInnerExceptionalBlock MixedOriginalNormCap MixedOriginalTail
open CenteredMomentEnergyBands
open Candidate.FourthPower QRH.SilDensitySplit.CubeFree.Packet.Grouped QRH.Cycle090 QRH.Cycle092.NativeStrip
namespace QRH.Cycle092.FixedFramePacking
local notation "Id" => Ideal HeckeFamily.O

theorem width_injected {ι κ:Type} [Fintype ι] [Fintype κ] (f:ι↪κ)
    (w:κ→ℝ) (hw:∀i,0 ≤ w i) : (∑i,w (f i)) ≤ ∑j,w j := by
  classical
  calc
    _ = ∑ j∈(Finset.univ:Finset ι).map f,w j := (Finset.sum_map _ _ _).symm
    _  ≤  _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _=>hw j)

structure BallCaps {ι:Type} [Fintype ι] (s:Source ι (1/4) (9/4)) (Z n y:ℝ) (w:ι→ℝ) : Prop where
  floor : Z^(-8:ℝ)  ≤  s.L
  x₁ : s.X₁  ≤  Z^(8:ℝ)
  x₂ : s.X₂  ≤  Z^(8:ℝ)
  y₁ : s.Y₁  ≤  Z^(8:ℝ)
  y₂ : s.Y₂  ≤  Z^(8:ℝ)
  slots : (∏i,s.P i)  ≤  Z^(8:ℝ)
  pool : poolCap s  ≤  Z^(8:ℝ)
  norm : sourceNormCap s.P (9/4) s.T s.d  ≤  Z^(8:ℝ)
  volume : sourceVolume s  ≤  Z^(8:ℝ)
  invVolume : (sourceVolume s)⁻¹  ≤  Z^2
  originalBox : Box n y (sourceWidth n y) (length Z s.X₁) (length Z s.X₂) (∑i,w i)

theorem restored_caps (N:ℕ) : ∀ᶠ Z:ℝ in atTop,1<Z ∧
    ∀ (ι:Type) [Fintype ι] (s:Source ι (1/4) (9/4)) (S:Finset PrimeIdeal) (d:IdealPair)
    (X₁ X₂ Y₁ Y₂ M₁ M₂ n y l:ℝ) (w:ι→ℝ),
    (Fintype.card ι ≤ N) → (∀i,0 ≤ w i) → (∀i,s.P i=Z^(w i)) →
    sourceY0 ≤ y → y ≤ sourceY → n ≤ sourceRatio*y →
    length Z X₁ ≤ n → length Z X₂ ≤ y → (∑i,w i) ≤ l → l ≤ sourceWidth n y →
    Z^(115/1000:ℝ) ≤ X₁ → Z^(115/1000:ℝ) ≤ X₂ → Z^(115/1000:ℝ) ≤ Y₁ → Z^(115/1000:ℝ) ≤ Y₂ →
    X₁ ≤ M₁ → Y₁ ≤ M₁ → X₂ ≤ M₂ → Y₂ ≤ M₂ → M₁ ≤ Z → M₂ ≤ Z →
    d∈divisorPool (supportedRectangle S (9/4) M₁ M₂) →
    s.X₁=X₁/(d.1.absNorm:ℝ) → s.X₂=X₂/(d.2.absNorm:ℝ) →
    s.Y₁=Y₁/(d.1.absNorm:ℝ) → s.Y₂=Y₂/(d.2.absNorm:ℝ) →
    s.L=min (min s.X₁ s.X₂) (min s.Y₁ s.Y₂) →
    BallCaps s Z n y w := by
  filter_upwards [QRH.SilDensitySplit.CubeFree.FP.MixedOriginalTailCaps.eventually_source_caps N (9/4) 1 1 1 (by norm_num),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<115/1000)).eventually_ge_atTop (9/4:ℝ)] with Z hs hzq
  refine ⟨hs.1,?_⟩
  intro ι inst s S d X₁ X₂ Y₁ Y₂ M₁ M₂ n y l w hN hw hP hy0 hy1 hn hxn hxy hsum hl
    hq₁ hq₂ hq₃ hq₄ hxM₁ hyM₁ hxM₂ hyM₂ hM₁ hM₂ hd hx₁ hx₂ hY₁ hY₂ hL
  have hz:=hs.1
  have hz0:=zero_lt_one.trans hz
  have hq:=Real.rpow_pos_of_pos hz0 (115/1000:ℝ)
  have hc:=root_divisor_caps S (9/4) M₁ M₂ hd
  have two {x:ℝ} (hh:Z^(115/1000:ℝ) ≤ x) {D:ℝ} (hD:1 ≤ D) : x/D ≤ x :=
    div_le_self (hq.le.trans hh) hD
  have h1:=hx₁.le.trans (two hq₁ hc.1)
  have h2:=hx₂.le.trans (two hq₂ hc.2.1)
  have h3:=hY₁.le.trans (two hq₃ hc.1)
  have h4:=hY₂.le.trans (two hq₄ hc.2.1)
  have bx (X:ℝ):0 ≤ length Z X := Real.logb_nonneg hz (le_max_left _ _)
  have bX : Box n y (sourceWidth n y) (length Z s.X₁) (length Z s.X₂) (∑i,w i) :=
    ⟨bx _,bx _,Or.inl ⟨(length_mono Z _ _ hz h1).trans hxn,(length_mono Z _ _ hz h2).trans hxy⟩,
    Finset.sum_nonneg (fun i _=>hw i),hsum.trans hl⟩
  have htot:=RawSides.box_total_cap hy0 hy1 hn bX
  have hW:(∑i,w i) ≤ 1:=by linarith [bx s.X₁,bx s.X₂]
  have hP1:(∏i,s.P i) ≤ Z^(1:ℝ):=by
    simp_rw [hP];rw [←Real.rpow_sum_of_pos hz0]; exact Real.rpow_le_rpow_of_exponent_le hz.le hW
  have h1':=h1.trans (hxM₁.trans hM₁)
  have h2':=h2.trans (hxM₂.trans hM₂)
  have h3':=h3.trans (hyM₁.trans hM₁)
  have h4':=h4.trans (hyM₂.trans hM₂)
  have hsup:=hs.2 ι (1/4) s hN (by simpa using h1') (by simpa using h2')
    (by simpa using h3') (by simpa using h4') hP1
  have hlower:=root_four_lengths_lower S (9/4) M₁ M₂ Z X₁ X₂ Y₁ Y₂ hd hz (by norm_num) hM₁ hM₂
    ⟨hzq.trans hq₁,hzq.trans hq₂,hzq.trans hq₃,hzq.trans hq₄⟩
  rw [←hx₁,←hx₂,←hY₁,←hY₂,←hL] at hlower
  have h8 : Z ≤ Z^(8:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hz.le (by norm_num : (1:ℝ) ≤ 8)
  have h48: Z^(2*1+1+1:ℝ)  ≤  Z^(8:ℝ) := Real.rpow_le_rpow_of_exponent_le hz.le (by norm_num)
  have hfloor:Z^(-8:ℝ) ≤ Z⁻¹ := by
    simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le hz.le (by norm_num : (-8:ℝ) ≤ -1)
  have hP8 : (∏i,s.P i) ≤ Z^(8:ℝ) := (show _≤Z by simpa only [Real.rpow_one] using hP1).trans h8
  refine ⟨hfloor.trans hlower,h1'.trans h8,h2'.trans h8,h3'.trans h8,h4'.trans h8,
    hP8,hsup.1.trans h48,hsup.2.trans h48,?_,?_,bX⟩
  · exact (RawSides.root_volume_of_box s w hP hz hy0 hy1 hn bX).trans
      (Real.rpow_le_rpow_of_exponent_le hz.le (by norm_num))
  · apply divided_volume_reciprocal hz (hlower.trans s.hX₁) (hlower.trans s.hX₂)
    calc
      (1:ℝ)=∏ _i:ι,(1:ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _=>zero_le_one) (fun i _=>s.hP i)

#print axioms restored_caps
end QRH.Cycle092.FixedFramePacking
