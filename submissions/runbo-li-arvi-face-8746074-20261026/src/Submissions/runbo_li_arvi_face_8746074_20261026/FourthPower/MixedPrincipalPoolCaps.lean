/- Copyright (c) 2026 Sil. Apache-2.0.
Full finite-pool norm bounds for principal conductor admissibility.
This includes zero coefficient columns, so no divisor-pool term is lost.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedInnerExceptionalPair
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedOriginalTailCaps

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedPrincipalPoolCaps
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRectangle CenteredMomentFirstSectors CenteredMomentLattice
open CenteredMomentSourceZeroEnergy
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedOriginalTail MixedOriginalTailCaps MixedInnerExceptionalPair
open MixedLiteralAllocation MixedCommonCoefficient MixedCompletedRows
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
local notation "Id" => Ideal HeckeFamily.O
local instance {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

theorem residual_plain_norm (d : Id) (hd : d≠0) (b X Y : ℝ)
    (hb : 0≤b) (hX : 0≤X) (hY : 0≤Y) (I : Id)
    (hI : I∈residualPool d hd (plainSupportPool b X Y)) :
    (I.absNorm:ℝ)≤128*b*(X+Y)/(d.absNorm:ℝ) := by
  rw [residual_plain_pool] at hI
  have hn : (I.absNorm:ℝ)≤b*(X+Y)/(d.absNorm:ℝ) := by
    rcases Finset.mem_union.mp hI with hI|hI
    · have hh := (mem_idealBall _ _).mp hI |>.2
      apply hh.trans
      have hy : 0≤b*(Y/(d.absNorm:ℝ)) := mul_nonneg hb (div_nonneg hY (Nat.cast_nonneg _))
      calc
        _ ≤ b*(X/(d.absNorm:ℝ))+b*(Y/(d.absNorm:ℝ)) := le_add_of_nonneg_right hy
        _ = _ := by ring
    · have hh := (mem_idealBall _ _).mp hI |>.2
      apply hh.trans
      have hx : 0≤b*(X/(d.absNorm:ℝ)) := mul_nonneg hb (div_nonneg hX (Nat.cast_nonneg _))
      calc
        _ ≤ b*(X/(d.absNorm:ℝ))+b*(Y/(d.absNorm:ℝ)) := le_add_of_nonneg_left hx
        _ = _ := by ring
  apply hn.trans
  have hbase : 0≤b*(X+Y)/(d.absNorm:ℝ) :=
    div_nonneg (mul_nonneg hb (add_nonneg hX hY)) (Nat.cast_nonneg _)
  calc
    _ ≤ 128*(b*(X+Y)/(d.absNorm:ℝ)) := by linarith
    _ = _ := by ring

/-- Every member of the original pool is bounded, even when its actual
coefficient vanishes. The same coarse cap also counts the tuple pool. -/
theorem source_column_pool_norm (s : Source ι a b) (hb : 0≤b) (I : Id)
    (hI : I∈sourceColumns s) : (I.absNorm:ℝ)≤poolCap s := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
  have hvm := Fintype.mem_piFinset.mp hv
  have hleft := residual_plain_norm s.d.1 s.hd.1 b s.X₁ s.Y₁ hb
    (s.hL.trans_le s.hX₁).le (s.hL.trans_le s.hY₁).le (v (Sum.inr 0)) (hvm (Sum.inr 0))
  have hright := residual_plain_norm s.d.2 s.hd.2 b s.X₂ s.Y₂ hb
    (s.hL.trans_le s.hX₂).le (s.hL.trans_le s.hY₂).le (v (Sum.inr 1)) (hvm (Sum.inr 1))
  have hmarked : (∏i,(Ideal.absNorm (v (Sum.inl i)):ℝ))≤∏i,256*s.P i := by
    apply Finset.prod_le_prod₀ (fun i _=>Nat.cast_nonneg _) (fun i _=>?_)
    have hh := (s.hpn i (v (Sum.inl i)) (hvm (Sum.inl i))).2
    have hp := s.hP i
    linarith
  have hup : 0≤∏i,256*s.P i :=
    Finset.prod_nonneg (fun i _=>mul_nonneg (by norm_num) (zero_le_one.trans (s.hP i)))
  have hlup : 0≤128*b*(s.X₁+s.Y₁)/(s.d.1.absNorm:ℝ) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb)
      (add_nonneg (s.hL.trans_le s.hX₁).le (s.hL.trans_le s.hY₁).le)) (Nat.cast_nonneg _)
  have hh := mul_le_mul (mul_le_mul hmarked hleft (Nat.cast_nonneg _) hup) hright
    (Nat.cast_nonneg _) (mul_nonneg hup hlup)
  calc
    _ = (∏i,(Ideal.absNorm (v (Sum.inl i)):ℝ))*
        (Ideal.absNorm (v (Sum.inr 0)):ℝ)*(Ideal.absNorm (v (Sum.inr 1)):ℝ) := by
      simp only [finiteTupleProduct,map_prod,Nat.cast_prod,Fintype.prod_sum_type,Fin.prod_univ_two,
        map_mul,Nat.cast_mul]
      ring
    _ ≤ (∏i,256*s.P i)*(128*b*(s.X₁+s.Y₁)/(s.d.1.absNorm:ℝ))*
        (128*b*(s.X₂+s.Y₂)/(s.d.2.absNorm:ℝ)) := hh
    _ = _ := by unfold poolCap pairNorm; ring

theorem pool_norm_le_square (s : Source ι a b) (hb : 0≤b) : poolNorm s≤(poolCap s)^2 := by
  have hcard : ((sourceColumns s).card:ℝ)≤poolCap s := by
    apply le_trans _ (source_pool_card s hb)
    exact_mod_cast Finset.card_image_le
      (s:=Fintype.piFinset (tuplePools s)) (f:=finiteTupleProduct)
  calc
    _ ≤ ∑I∈sourceColumns s,poolCap s := Finset.sum_le_sum (source_column_pool_norm s hb)
    _ = ((sourceColumns s).card:ℝ)*poolCap s := by simp
    _ ≤ poolCap s*poolCap s := mul_le_mul_of_nonneg_right hcard (poolCap_nonneg s)
    _ = _ := (pow_two _).symm

theorem eventually_full_pool_norm (N : ℕ) (b L Pexp ε : ℝ) (hb : 0≤b) (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(ι : Type u) [Fintype ι],∀a : ℝ,∀s : Source ι a b,
      Fintype.card ι≤N → s.X₁≤Z^L → s.X₂≤Z^L → s.Y₁≤Z^L → s.Y₂≤Z^L →
      (∏i,s.P i)≤Z^Pexp → poolNorm s≤Z^(2*(2*L+Pexp+ε)) := by
  filter_upwards [eventually_source_caps N b L Pexp ε hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι instι a s hcard hX₁ hX₂ hY₁ hY₂ hP
  have hc := (hZ.2 ι a s hcard hX₁ hX₂ hY₁ hY₂ hP).1
  apply (pool_norm_le_square s hb).trans
  calc
    _ ≤ (Z^(2*L+Pexp+ε))^2 := pow_le_pow_left₀ (poolCap_nonneg s) hc 2
    _ = _ := by rw [←Real.rpow_mul_natCast (zero_lt_one.trans hZ.1).le]; congr 1; norm_num; ring

/-- The full conductor cap is supplied by original scale bounds. The
fixed threshold precedes all actual characters, common ideals and rows. -/
theorem eventually_conductor_budget (N : ℕ) (b L Pexp ε Bη BR BC BE M : ℝ)
    (hb : 0≤b) (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(ι : Type u) [Fintype ι],∀a : ℝ,∀s : Source ι a b,
      Fintype.card ι≤N → s.X₁≤Z^L → s.X₂≤Z^L → s.Y₁≤Z^L → s.Y₂≤Z^L →
      (∏i,s.P i)≤Z^Pexp → (s.R.absNorm:ℝ)≤Z^BR →
      ∀(η : Character)(C E : Id)(radius : ℝ),0≤radius →
      (η.modulus.absNorm:ℝ)≤Z^Bη → (C.absNorm:ℝ)≤Z^BC → (E.absNorm:ℝ)≤Z^BE →
      radius≤Z^M → conductorBudget s η C E radius≤Z^(Bη+BR+BC+BE+4*L+2*Pexp+M+3*ε) := by
  let Cfixed : ℝ := 4*(fixedFactor:ℝ)*(Ideal.span {fixedBadMask}).absNorm*
    (Ideal.span {(72:HeckeFamily.O)}).absNorm
  have hc : ∀ᶠZ : ℝ in atTop,Cfixed≤Z^ε :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) Cfixed
  filter_upwards [eventually_full_pool_norm N b L Pexp ε hb hε,hc] with Z hZ hfixed
  refine ⟨hZ.1,?_⟩
  intro ι instι a s hcard hX₁ hX₂ hY₁ hY₂ hP hR η C E radius hr hη hC hE hrad
  have hp := hZ.2 ι a s hcard hX₁ hX₂ hY₁ hY₂ hP
  have hp0 : 0≤poolNorm s := Finset.sum_nonneg (fun I _=>Nat.cast_nonneg _)
  have hz := zero_lt_one.trans hZ.1
  calc
    _ = Cfixed*(η.modulus.absNorm:ℝ)*s.R.absNorm*C.absNorm*E.absNorm*poolNorm s*radius := by
      unfold conductorBudget fixedConductorCost Cfixed
      ring
    _ ≤ Z^ε*Z^Bη*Z^BR*Z^BC*Z^BE*Z^(2*(2*L+Pexp+ε))*Z^M := by gcongr
    _ = _ := by
      repeat rw [←Real.rpow_add hz]
      congr 1
      ring

end
end Candidate.FourthPower.MixedPrincipalPoolCaps
