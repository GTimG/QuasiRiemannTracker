/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The P.3 reference on the same finite regular rows: genuine short marked
fourth and genuine independently twisted long unmarked fourth. -/
import Candidate.C092.transport.ReferenceShortP3Fourth
import Candidate.C092.transport.StrongPairOrdinaryUnmarked
import Candidate.C092.transport.ReferenceShortP3Finite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace QRH.Cycle092.ReferenceShortP3
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open CenteredMomentDetectorPlainFiberSource CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open CenteredMomentExceptionalAmplitudePair
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair QRH.Cycle092.TinyCore
local notation "O" => HeckeFamily.O

theorem actual_reference_source (ι : Type) [Fintype ι] [DecidableEq ι]
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (H ε ξ M₀ bΦ : ℝ) (hH : 0 < H) (hε : 0 < ε) (hεH : ε ≤ H)
    (hξ : 0 < ξ) (hM₀ : 1 ≤ M₀) (hbΦ : 0 < bΦ)
    (hΦs : Function.support (radialMajorant : ℝ→ℂ) ⊆ Set.Iic bΦ)
    (η₁ η₂ η₀ : Character) (Q : Ideal O) (hQr : Q ≤ rayM)
    (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) :
    ∃ d : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ U : ℝ in atTop, 1 < U ∧
    ∀ (pool : ι → Finset (Ideal O)) (ν : ι → Ideal O → ℂ)
      (Wslot : ι → ℝ → ℂ) (P : ι → ℝ),
    (∀ i, ∀ I∈pool i, Prime I) → (∀ i, 0 < P i) →
    (∀ i I, ‖ν i I‖ ≤ 1) → (∀ i, Function.support (Wslot i) ⊆ Set.Icc (1:ℝ) 2) →
    (∀ i x, ‖Wslot i x‖ ≤ M₀) →
    ∀ (p : Profiles (1/4) (9/4)) (t₁ t₂ height X₁ X₂ : ℝ),
    0 ≤ height → 0 < X₁ → 0 < X₂ → X₂ ≤ U^H →
    X₁^2*(∏ i,P i)^2 ≤ U^(2:ℝ) →
    4*((X₁^2*(∏ i,P i)^2)^2/(U^H))*U^(ξ/2) < 1 →
    ∀ (s : Finset FreeRow) (mark : ι → FreeRow → ℂ),
    (∀ u∈s,initialKeep η₂ (internalQ Q η₀) u.val) →
    (∀ u∈s,rowNorm u ≤ U^H) →
    (∀ u∈s, ∀ i, ‖mark i u‖ =
      ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val (pool i)
        (fun I => ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) t₁ (P i)‖) →
    finiteEnergy s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
      C*(p.control S)^2*
        (1+|t₂|+height)^d*U^(H+ε) := by
  obtain ⟨Sd,St,Cd,Ct,hCd,hCt,hshort⟩ := short_fourth_source ι (1/4) (9/4) 2 ε ξ 0
    (by norm_num) (by norm_num) (by norm_num) hε hξ
  have hδ : 0 < ε/H := div_pos hε hH
  obtain ⟨d,S,Cl,hCl,hlong⟩ := freely_small_unmarked_fourth hβ rayM Hr hHr bΦ (ε/H)
    hbΦ hδ ((div_le_one hH).mpr hεH) hΦs η₂ η₀ Q hQr hQ0 hQt hQ72
  let Cs := (Cd*Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) radialMajorant+
    Ct*St.sup (schwartzSeminormFamily ℝ ℝ ℂ) radialMajorant)*M₀^(4*Fintype.card ι)
  let C := Cs+Cl*QuadraticInitialBound.diagonalControl radialMajorant+1
  have hCs : 0 ≤ Cs := by dsimp [Cs]; positivity
  have hd := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨d,S∪{(0,0)},C,hC,?_⟩
  have hl := (tendsto_rpow_atTop hH).eventually hlong
  filter_upwards [hshort,hl,eventually_gt_atTop (1:ℝ)] with U hshort hlong hU
  refine ⟨hU,?_⟩
  intro pool ν Wslot P hprime hP hν hWs hWb p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hX₂K hvol hcut
  intro s mark hk hy hm
  have hu : 0 < U := zero_lt_one.trans hU
  have hK : 1 ≤ U^H := Real.one_le_rpow hU.le hH.le
  have hKp : 0 < U^H := Real.rpow_pos_of_pos hu H
  have hKi : (U^H)⁻¹ ≤ U^(2:ℝ) := (inv_le_one_of_one_le₀ hK).trans (Real.one_le_rpow hU.le (by norm_num : (0:ℝ) ≤ 2))
  have hmajor : ∀ z∈s.image (fun u => u.val), 1 ≤
      (radialMajorant (‖eisEmbedding z‖^2/(U^H))).re := by
    intro z hz
    obtain ⟨u,hu',rfl⟩ := Finset.mem_image.mp hz
    rw [radialMajorant_one _ ⟨div_nonneg (sq_nonneg _) hKp.le,?_⟩]
    · norm_num
    · apply (div_le_one hKp).mpr
      simpa only [rowNorm,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] using hy u hu'
  have hs := hshort.2 η₁ t₁ pool ν Wslot P (fun _ => M₀) hprime hP (fun _ => hM₀)
    hν hWs hWb (p.profile 0) X₁ (U^H) (p.support 0) hX₁ hKp hvol hKi hcut
    radialMajorant (s.image (fun u => u.val)) (fun z => radialMajorant_nonneg _) hmajor
  rw [Finset.sum_image (fun x _ y _ hxy => Subtype.val_injective hxy)] at hs
  have hmarks (u : FreeRow) (hu' : u∈s) :
      (∏ i, ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val (pool i)
        (fun I => ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) t₁ (P i)‖^2) = ∏ i,‖mark i u‖^2 :=
    Finset.prod_congr rfl (fun i _ => congrArg (fun x : ℝ => x^2) (hm u hu' i).symm)
  have hreplace := Finset.sum_congr rfl (fun u hu' => congrArg
    (fun x : ℝ => (‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 0) t₁ X₁‖^2*x)^2)
    (hmarks u hu'))
  rw [hreplace] at hs
  have hlong' := hlong hK p 1 t₂ height X₂ hh hX₂ hX₂K s hk hy
  have hp : (U^H)^(1+ε/H) = U^(H+ε) := by
    rw [←Real.rpow_mul hu.le]
    congr 1
    field_simp
  rw [hp] at hlong'
  let G := C*(1+|t₂|+height)^d*U^(H+ε)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hs' : (∑ u∈s,(‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 0) t₁ X₁‖^2*
      ∏ i,‖mark i u‖^2)^2) ≤ G*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0))^4 := by
    have he := Real.one_le_rpow hU.le hε.le
    have hheight : 1 ≤ (1+|t₂|+height)^d := one_le_pow₀ (by linarith [abs_nonneg t₂])
    have hmexp : (M₀^Fintype.card ι)^4 = M₀^(4*Fintype.card ι) := by rw [←pow_mul]; congr 1; omega
    simp only [Finset.prod_const,Finset.card_univ,neg_zero,Real.rpow_zero,mul_one] at hs
    rw [hmexp] at hs
    have hcost :
        Cd*M₀^(4*Fintype.card ι)*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0))^4*
            Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) radialMajorant*U^H*U^ε+
        Ct*M₀^(4*Fintype.card ι)*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0))^4*
            St.sup (schwartzSeminormFamily ℝ ℝ ℂ) radialMajorant*U^H ≤
        Cs*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0))^4*U^(H+ε) := by
      calc
        _ ≤ Cd*M₀^(4*Fintype.card ι)*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0))^4*
            Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) radialMajorant*U^H*U^ε+
          (Ct*M₀^(4*Fintype.card ι)*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0))^4*
            St.sup (schwartzSeminormFamily ℝ ℝ ℂ) radialMajorant*U^H)*U^ε :=
          add_le_add le_rfl (le_mul_of_one_le_right (by positivity) he)
        _ = _ := by rw [Real.rpow_add hu]; dsimp [Cs]; ring
    apply (hs.trans hcost).trans
    have hc : Cs ≤ C := by dsimp [C]; linarith [mul_nonneg hCl.le hd]
    calc
      _ ≤ C*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0))^4*U^(H+ε) := by gcongr
      _ ≤ (C*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0))^4*U^(H+ε))*
          (1+|t₂|+height)^d := le_mul_of_one_le_right (by positivity) hheight
      _ = _ := by dsimp [G]; ring
  have hl' : (∑ u∈s,(‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 1) t₂ X₂‖^2*
      ∏ i∈(Finset.univ : Finset ι)\Finset.univ,‖mark i u‖^2)^2) ≤
      G*(sourceControl S (p.profile 1))^4 := by
    simp only [Finset.sdiff_self,Finset.prod_empty,mul_one,←pow_mul,show (2:ℕ)*2=4 from rfl]
    apply hlong'.trans
    dsimp [G,C]
    have hc : Cl*QuadraticInitialBound.diagonalControl radialMajorant ≤ Cs+Cl*QuadraticInitialBound.diagonalControl radialMajorant+1 := by linarith
    calc
      _ = (Cl*QuadraticInitialBound.diagonalControl radialMajorant)*(sourceControl S (p.profile 1))^4*(1+|t₂|+height)^d*U^(H+ε) := by ring
      _ ≤ (Cs+Cl*QuadraticInitialBound.diagonalControl radialMajorant+1)*
          (sourceControl S (p.profile 1))^4*(1+|t₂|+height)^d*U^(H+ε) := by gcongr
      _ = _ := by ring
  have hcs := finite_split_cauchy (Finset.univ : Finset ι) s η₁ η₂
    (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark
  have h := hcs.trans (common_cauchy_factor hG hs' hl')
  have hA : SchwartzMap.seminorm ℝ 0 0 (p.profile 0) ≤
      sourceControl (S∪{(0,0)}) (p.profile 0) := by
    exact Seminorm.le_def.mp (Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ)
      (Finset.mem_union_right S (by simp : (0,0)∈({(0,0)} : Finset (ℕ×ℕ))))) (p.profile 0)
  have hB : sourceControl S (p.profile 1) ≤ sourceControl (S∪{(0,0)}) (p.profile 1) :=
    Seminorm.le_def.mp (Finset.sup_mono (show S⊆S∪{(0,0)} from Finset.subset_union_left)) (p.profile 1)
  apply h.trans
  dsimp only [G,Profiles.control]
  have hsem : 0 ≤ SchwartzMap.seminorm ℝ 0 0 (p.profile 0) := apply_nonneg _ _
  have hctrl : 0 ≤ sourceControl S (p.profile 1) := sourceControl_nonneg _ _
  have hctrl₀ : 0 ≤ sourceControl (S∪{(0,0)}) (p.profile 0) := sourceControl_nonneg _ _
  have hctrl₁ : 0 ≤ sourceControl (S∪{(0,0)}) (p.profile 1) := sourceControl_nonneg _ _
  calc
    _ = C*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*sourceControl S (p.profile 1))^2*
        (1+|t₂|+height)^d*U^(H+ε) := by ring
    _ ≤ _ := by gcongr

#print axioms actual_reference_source
end
end QRH.Cycle092.ReferenceShortP3
