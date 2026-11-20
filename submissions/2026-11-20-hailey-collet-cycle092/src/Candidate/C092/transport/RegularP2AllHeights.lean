/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.RegularFramePhysicalReturnInterface
import Candidate.C092.transport.RegularFramePhysicalReturnSourceCaps
import Candidate.C092.transport.ActualLargePairHeight
import Candidate.C092.transport.ReferenceArmRadialEither
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularFramePhysicalReturn
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily CenteredMomentEnergyBands
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional
open QRH.Cycle092.WholeSlot QRH.Cycle092.StrongPair
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source
local notation "O" => HeckeFamily.O

def BoundedOrderedP2At (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (Hr : Subgroup (O⧸M)ˣ)
    (hHr : RayOrthogonality.globalUnits M ≤  Hr)
    (W : ℝ→ℂ) (n y mesh U : ℝ)
    (old base omega1 omega2 : Character) (Q : Ideal O)
    (degree : ℕ) (controls : Finset (ℕ×ℕ)) (C κ : ℝ) : Prop :=
  ∀ V : ℝ, 0 ≤  V → V ≤ 2 →
  ∀ (T : Finset Slot) (theta : Slot→RayQuotient.Characters M Hr)
    (w sigma freq : Slot→ℝ) (tOld t1 t2 height : ℝ),
    (∀i,0 ≤  w i) → (∀i,w i ≤  mesh) → (∀i,sigma i=33/50) →
    0 ≤  height → |tOld| ≤  height → (∀i,|freq i| ≤  height) →
    (∀i,|tOld+freq i-t1| ≤  height) → (∀i,|tOld+freq i-t2| ≤  height) →
    (∑i∈T,w i) ≤  sourceWidth n y-(u:ℝ) →
  ∀ (p : Profiles (1/4) (9/4)) (X1 X2 : ℝ),0< X1 → 0< X2 →
    X1 ≤  U^n → X2 ≤  U^y → 1  ≤  X2 → 1+|t1|+|t2|+height  ≤  U^κ →
  ∀ rows : Finset FreeRow,
    (∀z∈rows,initialKeep old (internalQ Q base) z.val) →
    (∀z∈rows,initialKeep (old.product omega1) (internalQ Q (base.product omega1)) z.val) →
    (∀z∈rows,initialKeep (old.product omega2) (internalQ Q (base.product omega2)) z.val) →
    (∀z∈rows,rowNorm z ≤  U^V) →
    (∀z∈rows,∀i∈T,‖originalMark M Hr hHr old base theta W U w sigma freq tOld i z‖=
      ‖originalMark M Hr hHr (old.product omega1) (base.product omega1) theta W U w sigma
        (fun i=> tOld+freq i-t1) t1 i z‖) →
    (∀z∈rows,∀i∈T,‖originalMark M Hr hHr old base theta W U w sigma freq tOld i z‖=
      ‖originalMark M Hr hHr (old.product omega2) (base.product omega2) theta W U w sigma
        (fun i=> tOld+freq i-t2) t2 i z‖) →
    finiteEnergyOn T rows (old.product omega1) (old.product omega2)
      (p.profile 0) (p.profile 1) t1 t2 X1 X2 (originalMark M Hr hHr old base theta W U w sigma freq tOld) ≤ 
      C*(p.control controls)^2*(1+|t1|+|t2|+height)^degree*U^(terminalFramePrice V)

private theorem profile_le (p:Profiles (1/4) (9/4)) {S T:Finset (ℕ×ℕ)} (hst:S⊆T) :
    p.control S ≤ p.control T := by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hst) _) (Seminorm.le_def.mp (Finset.sup_mono hst) _)
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

theorem full_ordered_from_bounded (Slot:Type) [Fintype Slot] [DecidableEq Slot]
    (M:Ideal O) [NeZero M] (Hr:Subgroup (O⧸M)ˣ) (hHr:RayOrthogonality.globalUnits M ≤ Hr)
    (W:ℝ→ℂ) (hW:Continuous W) (hs:Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (n y mesh κ:ℝ) (hκ:0<κ) (hβ:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hy0:sourceY0 ≤ y) (hy1:y ≤ sourceY) (hn0:y ≤ n) (hn1:n ≤ sourceRatio*y)
    (old base ω₁ ω₂:Character) (Q:Ideal O) (hQM:Q ≤ M)
    (hq₁:internalQ Q (base.product ω₁)≠0) (ht₁:internalQ Q (base.product ω₁)≠⊤)
    (h72₁:internalQ Q (base.product ω₁) ≤ Ideal.span {(72:O)})
    (hq₂:internalQ Q (base.product ω₂)≠0) (ht₂:internalQ Q (base.product ω₂)≠⊤)
    (h72₂:internalQ Q (base.product ω₂) ≤ Ideal.span {(72:O)})
    (bΦ:ℝ) (hbΦ:0<bΦ) (hΦ:Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ)
    (d₀:ℕ) (S₀:Finset (ℕ×ℕ)) (C₀:ℝ) (hC₀:0<C₀)
    (bounded:∀ᶠ U:ℝ in atTop,BoundedOrderedP2At Slot M Hr hHr W n y mesh U old base ω₁ ω₂ Q d₀ S₀ C₀ κ) :
    ∃ d:ℕ,∃ S:Finset (ℕ×ℕ),∃ C:ℝ,0<C ∧ ∀ᶠ U:ℝ in atTop,
      OrderedP2At Slot M Hr hHr W n y mesh U old base ω₁ ω₂ Q d S C := by
  obtain ⟨d₁,S₁,C₁,hC₁,hbig⟩:=ReferenceArmRadial.actual_large_height_subsets κ hκ Slot hβ M Hr hHr W hW hs bΦ hbΦ hΦ
    (old.product ω₁) (old.product ω₂) (base.product ω₁) (base.product ω₂) Q Q hQM hq₁ ht₁ h72₁ hQM hq₂ ht₂ h72₂
  obtain ⟨d₂,S₂,C₂,hC₂,hshort⟩:=ReferenceArmRadial.actual_reference_either_arm Slot hβ M Hr hHr W hW hs bΦ hbΦ hΦ
    (old.product ω₁) (old.product ω₂) (base.product ω₁) (base.product ω₂) Q Q hQM hq₁ ht₁ h72₁ hQM hq₂ ht₂ h72₂
  let S:=(S₀∪S₁)∪S₂
  let d:=d₀+d₁+d₂
  let C:=C₀+C₁+C₂*(2:ℝ)^d₂
  have hc2:0 ≤ C₂*(2:ℝ)^d₂:=by positivity
  have hC:0<C:=by dsimp [C];positivity
  refine ⟨d,S,C,hC,?_⟩
  filter_upwards [bounded,hbig,hshort] with U hb hhi hlo
  intro V hV hV2 T θ w σ v tOld t1 t2 height hw hwm hσ hheight ht hf hf₁ hf₂ hwidth p X1 X2 hX1 hX2 hcaps1 hcaps2 rows hko hk1 hk2 hrow hr1 hr2
  let Ht:=1+|t1|+|t2|+height
  have hHt:1 ≤ Ht:=by dsimp [Ht];linarith [abs_nonneg t1,abs_nonneg t2]
  have caps:=original_source_caps hy0 hy1 hn0 hn1
  have hwidth':=hwidth.trans caps.1
  have hx:X1 ≤ U:=hcaps1.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hhi.1.le caps.2.1)
  have hy:X2 ≤ U:=hcaps2.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hhi.1.le caps.2.2)
  have hσ₁:∀i∈T,(33/50:ℝ) ≤ σ i:=fun i _=>(hσ i).ge
  have hσ₂:∀i∈T,σ i ≤ (33/50:ℝ):=fun i _=>(hσ i).le
  have hfprice:V ≤ terminalFramePrice V:=by
    unfold terminalFramePrice terminalReserve
    have h:=le_max_left 0 ((QRH.SourceCertificate.H:ℝ)-V)
    norm_num [u,rho];linarith
  have upl {C':ℝ} {S':Finset (ℕ×ℕ)} {d':ℕ} (hC':0 ≤ C') (hC'':C' ≤ C)
      (hS':S'⊆S) (hd':d' ≤ d) :
      C'*(p.control S')^2*Ht^d'*U^(terminalFramePrice V) ≤ C*(p.control S)^2*Ht^d*U^(terminalFramePrice V) := by
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans hhi.1).le _)
    exact mul_le_mul (mul_le_mul hC'' (pow_le_pow_left₀ (p.control_nonneg _) (profile_le p hS') 2)
      (sq_nonneg _) hC.le) (pow_le_pow_right₀ hHt hd') (pow_nonneg (zero_le_one.trans hHt) _) (mul_nonneg hC.le (sq_nonneg _))
  by_cases hH:Ht ≤ U^κ
  · by_cases hX:1 ≤ X2
    · have h:=hb V hV hV2 T θ w σ v tOld t1 t2 height hw hwm hσ hheight ht hf hf₁ hf₂ hwidth p X1 X2 hX1 hX2 hcaps1 hcaps2 hX hH rows hko hk1 hk2 hrow hr1 hr2
      exact h.trans (upl hC₀.le (by dsimp [C];linarith) ((Finset.subset_union_left).trans Finset.subset_union_left) (by dsimp [d];omega))
    · have hss:X2 ≤ U^ReferenceArmRadial.shortCap:=(le_of_not_ge hX).trans
        (Real.one_le_rpow hlo.1.le (by norm_num [ReferenceArmRadial.shortCap]))
      have h:=hlo.2 V hV hV2 T θ θ w σ (fun i=>tOld+v i-t1) (fun i=>tOld+v i-t2)
        hσ₁ hσ₂ hwidth' p t1 t2 height X1 X2 hheight hX1 hX2 (Or.inr ⟨hss,hx⟩) rows _ hk1 hk2 hrow hr1 hr2
      have haux:1+|t1|+|t1|+|t2|+|t2|+height  ≤  2*Ht:=by dsimp [Ht];linarith
      have hh':=pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1+|t1|+|t1|+|t2|+|t2|+height) haux d₂
      rw [mul_pow] at hh'
      apply h.trans
      apply le_trans _ (upl (S':=S₂) (d':=d₂) hc2 (by dsimp [C];linarith) Finset.subset_union_right (by dsimp [d];omega))
      have tmp:=mul_le_mul_of_nonneg_left hh' (mul_nonneg hC₂.le (sq_nonneg (p.control S₂)))
      convert mul_le_mul_of_nonneg_right tmp (Real.rpow_nonneg (zero_lt_one.trans hlo.1).le (terminalFramePrice V)) using 1 <;> ring
  · have h:=hhi.2 V hV hV2 T θ w σ (fun i=>tOld+v i-t1) hσ₁ hσ₂ hwidth'
      p t1 t2 height X1 X2 hheight hX1 hX2 hx hy (le_of_not_ge hH) rows _ hk1 hk2 hrow hr1
    have hab:=Real.rpow_le_rpow_of_exponent_le hhi.1.le hfprice
    exact h.trans ((mul_le_mul_of_nonneg_left hab (by have hH0:=zero_le_one.trans hHt;positivity :
      0 ≤ C₁*(p.control S₁)^2*Ht^d₁)).trans (upl (S':=S₁) (d':=d₁) hC₁.le (by dsimp [C];linarith)
        (Finset.subset_union_right.trans Finset.subset_union_left) (by dsimp [d];omega)))

#print axioms full_ordered_from_bounded
end
end QRH.Cycle092.RegularFramePhysicalReturn
