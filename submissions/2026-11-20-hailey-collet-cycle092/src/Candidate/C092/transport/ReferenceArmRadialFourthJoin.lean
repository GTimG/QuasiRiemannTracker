/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual first-Poisson marked short fourth at max(V,.993), and the independent
original unmarked long fourth at the true core radius V. -/
import Candidate.C092.transport.ReferenceArmRadialGeometry
import Candidate.C092.transport.ReferenceArmRadialCauchy
import Candidate.C092.transport.ReferenceArmRadialUnmarked
import Candidate.C092.transport.ReferenceShortP3Fourth
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace QRH.Cycle092.ReferenceArmRadial
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open CenteredMomentDetectorPlainFiberSource CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open CenteredMomentExceptionalAmplitudePair CenteredMomentEnergyBands
open QRH.Cycle092.TinyCore QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair QRH.Cycle092.ReferenceShortP3
local notation "O" => HeckeFamily.O

theorem two_radius_reference_source (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM≤ Hr)
    (epsilon xi M0 bPhi : ℝ) (hepsilon : 0< epsilon) (hxi : 0< xi)
    (hM0 : 1≤ M0) (hbPhi : 0< bPhi)
    (hPhi : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi)
    (eta1 eta2 base2 : Character) (Q2 : Ideal O) (hQray : Q2≤ rayM)
    (hQ0 : internalQ Q2 base2≠0) (hQt : internalQ Q2 base2≠⊤)
    (hQ72 : internalQ Q2 base2≤ Ideal.span {(72:O)}) :
    ∃ degree : ℕ,∃ controls : Finset (ℕ×ℕ),∃ C : ℝ,0< C ∧
    ∀ᶠ U : ℝ in atTop,1< U ∧ ∀V : ℝ,0≤ V → V≤2 →
    ∀ (pool : Slot→Finset (Ideal O)) (nu : Slot→Ideal O→ℂ)
      (Wslot : Slot→ℝ→ℂ) (P : Slot→ℝ),
      (∀i,∀I∈pool i,Prime I) → (∀i,0< P i) → (∀i I,‖nu i I‖≤1) →
      (∀i,Function.support (Wslot i)⊆Set.Icc (1:ℝ) 2) → (∀i x,‖Wslot i x‖≤ M0) →
    ∀ (p : Profiles (1/4) (9/4)) (t1 t2 height X1 X2 : ℝ),
      0≤ height → 0< X1 → 0< X2 → X2≤ U →
      X1^2*(∏i,P i)^2≤ U^(2:ℝ) →
      4*((X1^2*(∏i,P i)^2)^2/U^(max V markedRadius))*U^(xi/2)<1 →
    ∀ (rows : Finset FreeRow) (mark : Slot→FreeRow→ℂ),
      (∀u∈rows,initialKeep eta2 (internalQ Q2 base2) u.val) →
      (∀u∈rows,rowNorm u≤ U^V) →
      (∀u∈rows,∀i,‖mark i u‖=‖normalizedSlot eta1 (fixedBadMask*idealGenerator 1) 1 u.val
        (pool i) (fun I=> nu i I*Wslot i ((I.absNorm:ℝ)/P i)) t1 (P i)‖) →
      finiteEnergy rows eta1 eta2 (p.profile 0) (p.profile 1) t1 t2 X1 X2 mark ≤
        C*(p.control controls)^2*(1+|t2|+|t2|+height)^degree*
          U^((max V markedRadius+V)/2+epsilon) := by
  obtain ⟨Sd,St,Cd,Ct,hCd,hCt,hshort⟩ := short_fourth_source Slot (1/4) (9/4) 2 epsilon xi 0
    (by norm_num) (by norm_num) (by norm_num) hepsilon hxi
  obtain ⟨d,S,Cl,hCl,hlong⟩ := unmarked_fourth_all_radii hbeta rayM Hr hHr bPhi epsilon
    hepsilon hbPhi hPhi eta2 base2 Q2 hQray hQ0 hQt hQ72
  let Cs := (Cd*Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) radialMajorant+
    Ct*St.sup (schwartzSeminormFamily ℝ ℝ ℂ) radialMajorant)*M0^(4*Fintype.card Slot)
  let C0 := Cs+Cl*QuadraticInitialBound.diagonalControl radialMajorant+1
  have hCs : 0≤ Cs := by dsimp [Cs];positivity
  have hd := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  have hC01 : 1≤ C0 := by dsimp [C0];linarith [mul_nonneg hCl.le hd]
  refine ⟨2*d,S∪{(0,0)},C0^2,by positivity,?_⟩
  filter_upwards [hshort,hlong,eventually_gt_atTop (1:ℝ)] with U hshort hlong hU
  refine ⟨hU,?_⟩
  intro V hV hV2 pool nu Wslot P hprime hP hnu hWs hWb p t1 t2 height X1 X2
    hh hX1 hX2 hX2U hvol hcut rows mark hk hy hm
  have hu : 0< U := zero_lt_one.trans hU
  let r := max V markedRadius
  have hr : 0≤ r := hV.trans (le_max_left _ _)
  have hK : 1≤ U^r := Real.one_le_rpow hU.le hr
  have hKp : 0< U^r := Real.rpow_pos_of_pos hu _
  have hKi : (U^r)⁻¹≤ U^(2:ℝ) := (inv_le_one_of_one_le₀ hK).trans
    (Real.one_le_rpow hU.le (by norm_num : (0:ℝ)≤2))
  have hrows (u : FreeRow) (hu' : u∈rows) : rowNorm u≤ U^r :=
    (hy u hu').trans (Real.rpow_le_rpow_of_exponent_le hU.le (le_max_left _ _))
  have hmajor : ∀z∈rows.image (fun u=> u.val),1≤(radialMajorant (‖eisEmbedding z‖^2/U^r)).re := by
    intro z hz
    obtain ⟨u,hu',rfl⟩ := Finset.mem_image.mp hz
    rw [radialMajorant_one _ ⟨div_nonneg (sq_nonneg _) hKp.le,?_⟩]
    · norm_num
    · apply (div_le_one hKp).mpr
      simpa only [rowNorm,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] using hrows u hu'
  have hs := hshort.2 eta1 t1 pool nu Wslot P (fun _=> M0) hprime hP (fun _=> hM0)
    hnu hWs hWb (p.profile 0) X1 (U^r) (p.support 0) hX1 hKp hvol hKi hcut
    radialMajorant (rows.image (fun u=> u.val)) (fun _=> radialMajorant_nonneg _) hmajor
  rw [Finset.sum_image (fun x _ y _ hxy=> Subtype.val_injective hxy)] at hs
  have hreplace (u : FreeRow) (hu' : u∈rows) :
      (∏i,‖normalizedSlot eta1 (fixedBadMask*idealGenerator 1) 1 u.val (pool i)
        (fun I=> nu i I*Wslot i ((I.absNorm:ℝ)/P i)) t1 (P i)‖^2)=∏i,‖mark i u‖^2 :=
    Finset.prod_congr rfl (fun i _=> congrArg (fun x:ℝ=> x^2) (hm u hu' i).symm)
  have hsum := Finset.sum_congr rfl (fun u hu => congrArg (fun a:ℝ =>
    (‖original eta1 (fixedBadMask*idealGenerator 1) 1 u.val
    (p.profile 0) t1 X1‖^2*a)^2) (hreplace u hu))
  rw [hsum] at hs
  have hmexp : (M0^Fintype.card Slot)^4=M0^(4*Fintype.card Slot) := by
    rw [←pow_mul];congr 1;omega
  simp only [Finset.prod_const,Finset.card_univ,neg_zero,Real.rpow_zero,mul_one] at hs
  rw [hmexp] at hs
  have hs' : (∑u∈rows,(‖original eta1 (fixedBadMask*idealGenerator 1) 1 u.val
      (p.profile 0) t1 X1‖^2*∏i,‖mark i u‖^2)^2) ≤
      Cs*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0))^4*U^(r+epsilon) := by
    apply hs.trans
    have he := Real.one_le_rpow hU.le hepsilon.le
    have het := mul_le_mul_of_nonneg_left he (show 0≤ Ct*M0^(4*Fintype.card Slot)*
      (SchwartzMap.seminorm ℝ 0 0 (p.profile 0))^4*
      St.sup (schwartzSeminormFamily ℝ ℝ ℂ) radialMajorant*U^r by positivity)
    rw [Real.rpow_add hu]
    dsimp [Cs]
    nlinarith only [het]
  have hl := hlong.2 V hV hV2 p 1 t2 height X2 hh hX2 hX2U rows hk hy
  let Ht := (1+|t2|+|t2|+height)^d
  have hHt : 1≤ Ht := one_le_pow₀ (by linarith [abs_nonneg t2])
  have hC : 1≤ C0*Ht := le_trans hC01 (le_mul_of_one_le_right (zero_le_one.trans hC01) hHt)
  have hsC : Cs≤ C0*Ht := (by dsimp [C0];linarith [mul_nonneg hCl.le hd] : Cs≤ C0).trans
    (le_mul_of_one_le_right (zero_le_one.trans hC01) hHt)
  have hlC : Cl*QuadraticInitialBound.diagonalControl radialMajorant*Ht≤ C0*Ht :=
    mul_le_mul_of_nonneg_right (by dsimp [C0];linarith : Cl*QuadraticInitialBound.diagonalControl radialMajorant≤ C0)
      (zero_le_one.trans hHt)
  have he := independent_radius_cauchy rows eta1 eta2 (p.profile 0) (p.profile 1) t1 t2 X1 X2 mark
    hu hCs (by dsimp [Ht];positivity : 0≤ Cl*QuadraticInitialBound.diagonalControl radialMajorant*Ht)
    hC hsC hlC (apply_nonneg _ _) (sourceControl_nonneg _ _) hs'
    (by convert hl using 1 <;> dsimp [Ht] <;> ring)
  have hA : SchwartzMap.seminorm ℝ 0 0 (p.profile 0)≤ sourceControl (S∪{(0,0)}) (p.profile 0) :=
    Seminorm.le_def.mp (Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ)
      (Finset.mem_union_right S (by simp : (0,0)∈({(0,0)} : Finset (ℕ×ℕ))))) (p.profile 0)
  have hB := control_mono S (S∪{(0,0)}) Finset.subset_union_left (p.profile 1)
  apply he.trans
  have hpow : ((r+epsilon)+(V+epsilon))/2=(r+V)/2+epsilon := by ring
  rw [hpow]
  have hheight : Ht^2=(1+|t2|+|t2|+height)^(2*d) := by
    dsimp [Ht]
    rw [←pow_mul]
    congr 1
    omega
  rw [mul_pow,hheight]
  calc
    _ = C0^2*((SchwartzMap.seminorm ℝ 0 0 (p.profile 0))*sourceControl S (p.profile 1))^2*
      (1+|t2|+|t2|+height)^(2*d)*U^((r+V)/2+epsilon) := by ring
    _ ≤ _ := by
      dsimp [Profiles.control]
      have hn := apply_nonneg (SchwartzMap.seminorm ℝ 0 0) (p.profile 0)
      have hc := sourceControl_nonneg S (p.profile 1)
      gcongr
      exact sourceControl_nonneg _ _

end
end QRH.Cycle092.ReferenceArmRadial
#print axioms QRH.Cycle092.ReferenceArmRadial.two_radius_reference_source
