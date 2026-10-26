/- Exact native initial-source assembly at the actual recursive root ledger.
Original proofs (c)2026 Hailey Collet; root binding (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineAssembly
import Candidate.Research.RecursiveAffine.RootInitialHeight
import Candidate.Research.RecursiveAffine.RootSourceReduction

noncomputable local instance recursiveRootAssemblyLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle153RootInitialAssembly
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentSecondHeightFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentLogDyadic Cycle63InitialSource Cycle63Physical Cycle63Moment Cycle63InitialMass
open CenteredMomentFirstSourceReduction CenteredMomentSectorLocalization

private theorem root_comparisonFits_of_window {n₁ n₂ z : ℝ}
    (h : Cycle63.AffineLedger.PlainWindow n₁ n₂ z)(hz : 0≤z) :
    Cycle63FirstGeometry.ComparisonFits 1 (Cycle63.AffineLedger.comparisonLength n₁ n₂ z) n₁ n₂ z := by
  have hvol:=h.volume_le hz
  have h1:=Cycle63.AffineLedger.comparisonLength_nonneg n₁ n₂ z h
  have h2:=Cycle63.AffineLedger.comparisonLength_le n₁ n₂ z h
  have h3:=Cycle63.AffineLedger.long_factor n₁ n₂ z h
  have h4:=Cycle63.AffineLedger.daughter_fits n₁ n₂ z h
  exact ⟨h1,by linarith,by linarith,by linarith,by linarith⟩

variable {α : Type} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance rootInitialAssemblyFinite : Finite (O⧸rayM):=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (Hray : Subgroup (O⧸rayM)ˣ)(hHray : RayOrthogonality.globalUnits rayM≤Hray)

/-- The actual root ledger's literal native live budget. -/
def LiteralAffineGeometryBudget
    (W : ℝ→ℂ)(hW : Continuous W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η η₀ : Character)(Q : Ideal O)(bΦ mesh εmass τ ξ : ℝ) : Prop :=
  ∀Ψ : 𝓢(ℝ,ℂ), Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
    (∀x,0≤(Ψ x).re) →
  ∃externalDegree outerDegree windowDegree : ℕ,∃S : Finset (ℕ×ℕ),
  ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1<Z,
  ∀T : Finset α,∀θ : T→RayQuotient.Characters rayM Hray,
  ∀w σ freq : T→ℝ,∀t height : ℝ,
    (∀i,0≤w i) → (∀i,w i≤ mesh) →
    ∀hσlo : (∀i,(33/50:ℝ)≤σ i),∀hσhi : (∀i,σ i≤(33/50:ℝ)),
    0≤height → (∀i,|freq i|≤height) → 1+|t|+height≤Z^τ →
  ∀Φ : 𝓢(ℝ,ℂ),∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
  ∀hpΦ : ∀x,0≤(Φ x).re,∀p : Profiles (1/4) (9/4),∀X₁ X₂ : ℝ,
  ∀hX₁ : 0<X₁,∀hX₂ : 0<X₂,
    Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i) →
  let state:=fixedParentState η (internalQ Q η₀) Φ bΦ Z 1 hZ (by norm_num) hsΦ hpΦ;
  let inp:=affineInput rayM Hray hHray η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p (by norm_num)
    (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂;
  let E:=C*(p.control S)^2*(1+|t|+height)^externalDegree*Z^εmass;
  ∃H : ℤ×(Fin 5→ℤ)→ℝ,
    (∀key∈commonGeometryBins inp 1 1 Z Z ξ,0<H key) ∧
    ∀key∈commonGeometryBins inp 1 1 Z Z ξ,∀(reflected : Bool)(t' u : ℝ),
      geometryLiveBudget reflected inp 1 1 Z Z ξ 1 (Real.logb Z (volume inp))
        (zero_lt_one.trans hZ) key
        (fun q=>normPhase (coordinateBlock inp 1 1 Ψ Z Z ξ q)) (Fintype.card α) (9/4)
        (inp.t+2*Real.pi*(u-(if reflected then -t' else t')))≤
        ((if reflected then E/H key else E*H key)*(1+‖t'‖)^outerDegree)*
          (1+‖u‖)^(2*windowDegree)

/-- End-to-end width-one assembly for one fixed chosen character and ideal.
Only the actual live-budget estimate is pending. -/
theorem literal_geometry_initial_affine
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η η₀ : Character)(Q : Ideal O)(bΦ mesh ε τ ξ : ℝ)
    (hbΦ : 0<bΦ)(hmesh : 0< mesh)(hε : 0<ε)(hτ : 0<τ)(hξ : 0<ξ)
    (hmeshComparison : mesh≤Cycle63FirstActual.comparisonMesh 1 1 (ε/2))
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤(3/4:ℝ))
    (hQray : Q≤ rayM)(hQ0 : internalQ Q η₀≠0)(hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (hc : HasCompactSupport logAnnulus)(hsm : ContDiff ℝ ∞ logAnnulus)
    (hbudget : LiteralAffineGeometryBudget (α:=α) rayM Hray hHray W hW.continuous
      hWs η η₀ Q bΦ mesh (ε/4) τ ξ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,
      Cycle153EndpointMoment.InitialAffineAt (α:=α) rayM Hray hHray W 2 (1/4) (9/4) bΦ mesh
        (33/50) (33/50) 1 1 ε Z η η₀ Q degree S C := by
  let anchors : Fin 1→ Character:=fun _=>η
  obtain ⟨Ψ,hΨ,hΨpos,_,jr,Sr,hred⟩ := Cycle153RootSource.actual_initial_source_reduction_fixed_mesh
    (α:=α) rayM Hray hHray anchors W 1 2 (33/50) (33/50) (1/4) (9/4) bΦ
    1 1 (ε/2) ξ (by norm_num) hWs hW (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hbΦ (by norm_num) (by norm_num) (by positivity) hξ hbeta hκbeta
  obtain ⟨Cr,hCr,hred⟩:=hred η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨jb,jo,jw,Sb,Cb,hCb,hbud⟩:=hbudget Ψ hΨ hΨpos
  obtain ⟨Cm,hCm,hmass⟩:=uniform_geometry_mass (α:=α) Ψ jo jw ξ (ε/4) hξ.le
    (by positivity) hc hsm
  let Js:=max jr jb
  let Ss:=Sr∪Sb
  let Cs:=2*Cm*Cb+Cr
  have hCs : 0<Cs := by dsimp [Cs];positivity
  have hsmall : ∀ᶠ Z : ℝ in atTop,
      Cycle153RootPhysical.BoundedInitialAffineAt (α:=α) rayM Hray hHray W 2 (1/4) (9/4) bΦ mesh
        (33/50) (33/50) 1 1 ε τ Z η η₀ Q Js Ss Cs := by
    obtain hcaps := eventual_affine_polynomial_caps (α:=α) rayM Hray hHray W hW.continuous
      1 2 (33/50) (33/50) (1/4) (9/4) (by norm_num) hWs
      (by norm_num) (by norm_num) (by norm_num)
    filter_upwards [hred,hbud,hmass,hcaps,eventually_gt_atTop (1:ℝ)] with Z hr hb hm hcaps hZ
    intro T θ w σ freq t height hw hwm hσlo hσhi hh hv hheight M hM₁ hM₂ Φ hsΦ hpΦ
      p X₁ X₂ hX₁ hX₂ hlo₁ _hhi₁ hlo₂ _hhi₂ hslotlo hslothi hcell
    have hM : M=1 := le_antisymm hM₂ hM₁
    subst M
    simp only [mul_one] at hlo₁ hlo₂ hslotlo hslothi hcell
    have hsum : @Cycle63.AffineLedger.sumBottom recursiveRootAssemblyLedger ≤
        length Z X₁ + length Z X₂ := by
      change (81/100:ℝ) ≤ _
      have hl₁ : (81/200:ℝ) ≤ length Z X₁ := hlo₁
      have hl₂ : (81/200:ℝ) ≤ length Z X₂ := hlo₂
      linarith only [hl₁,hl₂]
    have hwin : Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i) :=
      ⟨hlo₁,hlo₂,hsum,hslotlo,hslothi,hcell⟩
    have hw0 : 0≤∑i,w i := Finset.sum_nonneg (fun i _=>hw i)
    have hvol := hwin.volume_le hw0
    let state:=fixedParentState η (internalQ Q η₀) Φ bΦ Z 1 hZ (by norm_num) hsΦ hpΦ
    let inp:=affineInput rayM Hray hHray η₀ θ W hW.continuous 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p (by norm_num)
      (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
    have hN : Fintype.card T≤Fintype.card α :=
      Fintype.card_le_of_injective (fun i:T=>i.val) Subtype.val_injective
    have hcap:=hcaps.2 T η₀ θ w σ freq (fun i=>⟨hσlo i,hσhi i⟩) bΦ state p
      t X₁ X₂ hX₁ hX₂ hw hwin
    obtain ⟨H,hH,hbound⟩:=hb hZ T θ w σ freq t height hw hwm hσlo hσhi hh hv hheight
      Φ hsΦ hpΦ p X₁ X₂ hX₁ hX₂ hwin
    have he : 0≤Cb*(p.control Sb)^2*(1+|t|+height)^jb*Z^(ε/4) := by positivity
    have hz₁ : inp.W₁ 0=0 := CenteredMomentDetectorPlainSource.support_zero
      (p.profile 0) (1/4) (9/4) (by norm_num) (p.support 0)
    have hz₂ : inp.W₂ 0=0 := CenteredMomentDetectorPlainSource.support_zero
      (p.profile 1) (1/4) (9/4) (by norm_num) (p.support 1)
    have hm' := hm hZ T inp (Fintype.card α) (1/4) (9/4)
      (Cb*(p.control Sb)^2*(1+|t|+height)^jb*Z^(ε/4)) (by norm_num) hN
      (by change (1/4:ℝ)≤1;norm_num) (by change (2:ℝ)≤9/4;norm_num)
      hz₁ hz₂
      (by simpa only [show (1:ℝ)+2=3 by norm_num] using hcap.2.2.2.1)
      (by simpa only [show (1:ℝ)+1=2 by norm_num] using hcap.2.2.1) he H hH hbound
    have hr' := hr.2 (0:Fin 1) T θ w σ freq t height hw
      (fun i=>(hwm i).trans hmeshComparison) hσlo hσhi hh hv
      1 (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) (by norm_num) (by norm_num) Φ hsΦ hpΦ p X₁ X₂ hX₁ hX₂
      (by change (81/200:ℝ)*1 ≤ _;rw [mul_one];exact hlo₁) (by change (81/200:ℝ)*1 ≤ _;rw [mul_one];exact hlo₂) hvol
      (by simpa only [mul_one] using hwin.slots_le) (root_comparisonFits_of_window hwin hw0) hZ (by norm_num)
    have hpcR := Cycle153RootPhysical.profile_control_mono p (Finset.subset_union_left (s₁ := Sr) (s₂ := Sb))
    have hpcB0 := p.control_nonneg Sb
    have hpcB := Cycle153RootPhysical.profile_control_mono p (Finset.subset_union_right (s₁ := Sr) (s₂ := Sb))
    have hbase : 1≤1+|t|+height := by linarith [abs_nonneg t]
    have hpowR : (1+|t|+height)^jr≤(1+|t|+height)^Js :=
      pow_le_pow_right₀ hbase (le_max_left jr jb)
    have hpowB : (1+|t|+height)^jb≤(1+|t|+height)^Js :=
      pow_le_pow_right₀ hbase (le_max_right jr jb)
    have hzpow : Z^(1+ε/2)≤Z^(1+ε) :=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    have hm'' : physicalMass inp 1 1 fixedBadMask 1 Ψ Z Z ξ/volume inp≤
        Cm*Cb*(p.control Ss)^2*(1+|t|+height)^Js*Z^(1+ε) := by
      apply hm'.trans
      calc
        _ = Cm*Cb*(p.control Sb)^2*(1+|t|+height)^jb*Z^(1+ε/2) := by
          calc
            _ = Cm*Cb*(p.control Sb)^2*(1+|t|+height)^jb*
                (Z^(ε/4)*Z^(1+ε/4)) := by ring
            _ = _ := by
              rw [←Real.rpow_add (zero_lt_one.trans hZ)]
              have heq : ε/4+(1+ε/4)=(1:ℝ)+ε/2 := by ring
              rw [heq]
        _ ≤ _ := by dsimp [Ss];gcongr
    change initialEnergy rayM Hray hHray W 2 Z 1 η η₀ Q T θ w σ freq t X₁ X₂
      (p.profile 0) (p.profile 1) Φ≤_
    change initialEnergy rayM Hray hHray W 2 Z 1 η η₀ Q T θ w σ freq t X₁ X₂
      (p.profile 0) (p.profile 1) Φ≤
      2*diagonalControl Φ*(physicalMass inp 1 1 fixedBadMask 1 Ψ (Z^(1:ℝ)) Z ξ/volume inp)+
      Cr*diagonalControl Φ*(p.control Sr)^2*(1+|t|+height)^jr*Z^(1+ε/2) at hr'
    apply hr'.trans
    have hd := diagonalControl_nonneg Φ
    have hpc0:=p.control_nonneg Sr
    calc
      _ ≤ 2*diagonalControl Φ*(Cm*Cb*(p.control Ss)^2*(1+|t|+height)^Js*Z^(1+ε))+
          Cr*diagonalControl Φ*(p.control Ss)^2*(1+|t|+height)^Js*Z^(1+ε) := by
        apply add_le_add
        · simpa only [Real.rpow_one] using mul_le_mul_of_nonneg_left hm'' (mul_nonneg (by norm_num) hd)
        · dsimp only [Ss]
          gcongr
      _ = _ := by dsimp [Cs];ring
  obtain ⟨jc,Sc,hcoarse⟩:=original_initial_coarse (α:=α) rayM Hray hHray W 1 2
    (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 1 (by norm_num) hWs hW
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbΦ hmesh.le
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbeta anchors
  obtain ⟨Cc,hCc,hcoarse⟩:=hcoarse η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨degree,hext⟩:=Cycle153RootPhysical.initial_height_extend (α := α) (Label := Fin 1) rayM Hray hHray W 2
    (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1
    (1+2*(Fintype.card α:ℝ)*mesh) ε τ hτ (by norm_num) (by norm_num) Js jc Ss Sc
  refine ⟨degree,Ss∪Sc,Cs+Cc,add_pos hCs hCc,?_⟩
  have hh:=hext anchors η₀ Q Cs Cc hCs.le hCc.le
    (hsmall.mono (fun _ h _=>h)) (hcoarse.mono (fun _ h=>h.2))
  exact hh.mono (fun _ h=>h (0:Fin 1))

end
end OAI.SevenEighths.Cycle153RootInitialAssembly
#print axioms OAI.SevenEighths.Cycle153RootInitialAssembly.literal_geometry_initial_affine
