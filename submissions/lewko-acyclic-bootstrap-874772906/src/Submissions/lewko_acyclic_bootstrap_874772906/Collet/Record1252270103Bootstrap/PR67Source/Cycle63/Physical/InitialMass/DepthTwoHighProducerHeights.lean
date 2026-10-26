import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.DepthTwoHighProducerCore
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryShiftedHeight
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The HIGH given of a parent of the second step from the transport form of its HIGH rows at small heights, the coarse
bound at all heights and a bound of the transport by the values of count-form records. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Cycle63MarkedPlain
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open MeasureTheory
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentNaturalFixedRaySource
open CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT Cycle63Moment
open CenteredMomentAmplificationChildInput
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
open CenteredMomentOriginalCommonHarmonic
open ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSecondHeightFamily Cycle63Moment.LowBranch HeckeDetectorZeros
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondExceptionalFamily
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptional
open CenteredMomentAllocatedRayDictionary CenteredMomentSecondInputCapacitySource
open Cycle63InitialSource CenteredMomentCommonRawScale QuadraticInitialBound CenteredMomentEnergyBands
open CenteredMomentLogDyadic
attribute [local instance] geometryAffineHighPaymentSumDecidable
attribute [local irreducible] Finset.univ

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

variable [Cycle63.AffineLedger] in
include M H hH in
/-- The HIGH given of a parent of the second step: the HIGH rows are bounded at small heights by the transport form of
the top theorem and at all heights by the coarse bound, the transport is bounded by values of the records of the two
orientations, and the degree of the heights is at least that of the extension of the small to the large heights. -/
theorem depth_two_high_given_of_values {ι : Type} [Fintype ι] [DecidableEq ι]
    (W : ℝ→ℂ) (_hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule) (η₀ : Character) (Q : Ideal O) (hQM : Q≤M)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) (δ Cs : ℝ) (Nbudget : ℕ) (qh : ℝ) (Sp SH : Finset (ℕ×ℕ))
    (K Kt Kc ε Kh cx : ℝ) (dh : ℕ) (Ψ : 𝓢(ℝ,ℂ))
    (hgδ : g.δ=δ) (hqq : qh=Cycle63.AffineLedger.q) (hSp : (0,0)∈Sp) (hSpSH : Sp⊆SH) (hKt : 0<Kt) (hKc : 0<Kc)
    (hdeg : (geometry_extend_shifted_height_bound (4+cx) 0 g.τ g.τ_pos 0).choose≤dh)
    (hKh : (2+4*Real.pi)^(geometry_extend_shifted_height_bound (4+cx) 0 g.τ g.τ_pos 0).choose*max Kt Kc≤Kh)
    (Z : ℝ) (hZ : 1<Z) (hT : 2<Z^g.τ) (s : Input ι) (p : Profiles (1/4) (9/4))
    (caps : GeometryAffineLowSourceGates s p Cs Z)
    (θ : ι→RayQuotient.Characters M H) (w σ freq : ι→ℝ) (hm : Matches M H hH s η₀ θ w σ freq W 2 Z)
    (R : Ideal O) (Mrow amp : ℝ) (hR : R≠0) (hRcap : (R.absNorm:ℝ)≤Z^(20:ℝ))
    (hMrow : 0≤Mrow) (hMrow1 : Mrow≤1) (hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤1+g.μ/16)
    (height mesh : ℝ) (hw : ∀j,0≤w j) (hwL : ∀j,w j≤Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))
    (hwr : ∀j,w j/31≤1) (hmesh : 0≤ mesh) (hwm : ∀j,w j≤ mesh) (hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
    (hheight : 0≤height) (hfreq : ∀j,|freq j|≤height) (hamp0 : 0≤amp) (hamp : |amp|≤4)
    (homega : |frequencyLoss Z 32 (g.μ/64)+g.μ/8|≤4)
    (htop : AffineHighTopInner (ι:=ι) M H hH η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1 one_ne_zero W hβlo g.e g.τ g.e_pos
      g.μ Cs 20 δ qh Nbudget Sp K Kt Q hQM hQ72 Z)
    (hcoarse : MainHighSelectedPhysicalCoarseSpec (α:=ι) (Fintype.card ι) 130 Cs (9/4) (9/4) (Real.log 2) 1 1
      (1/4) (9/4) δ (g.μ/64) 3 cx Kc Z)
    (Hval : Bool→ℝ) (hHval : ∀b,0≤Hval b)
    (hrec : ∀(reflected second : Bool)(bin : ℤ×(Fin 5→ℤ)),
      bin∈commonGeometryBins s R 1 (Z^Mrow) Z (g.μ/64) → ∀(t : ℝ)(χ₀ : RayCharacter)
        (hP : ∀j,(affineHighBlockDatum reflected s R 1 Z Mrow amp g.μ t hZ bin caps.zero₁ caps.zero₂ j).R*
          (if second then (affineHighBlockDatum reflected s R 1 Z Mrow amp g.μ t hZ bin caps.zero₁ caps.zero₂ j).D
            else (affineHighBlockDatum reflected s R 1 Z Mrow amp g.μ t hZ bin caps.zero₁ caps.zero₂ j).C)≠0)
        (hPN : ∀j,((((affineHighBlockDatum reflected s R 1 Z Mrow amp g.μ t hZ bin caps.zero₁ caps.zero₂ j).R*
          (if second then (affineHighBlockDatum reflected s R 1 Z Mrow amp g.μ t hZ bin caps.zero₁ caps.zero₂ j).D
            else (affineHighBlockDatum reflected s R 1 Z Mrow amp g.μ t hZ bin caps.zero₁ caps.zero₂ j).C)).absNorm:ℝ))≤
            Z^(28:ℝ)),
        affineHighUniversalTransport M H hH η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1 one_ne_zero reflected second s R
          1 Z Mrow amp g.μ t hZ bin caps.zero₁ caps.zero₂ χ₀ (internalQ Q η₀) hQ72 fixedBadMask
          fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _) (inf_le_left.trans hQM) inf_le_right g.e
          (Z^g.τ) g.e_pos hT hβlo hβhi hP hPN qh
          (g.μ/4+g.μ/4+(2*(g.μ/8)+δ+3*((Nbudget:ℝ)+2)*δ+130*δ+130*δ+3*((Nbudget:ℝ)+2)*(2*δ)))≤
          Z^(-(Mrow+3*g.δ+ε))*Hval (!reflected)) :
    GeometryAffineHighGiven (α:=ι) M H hH g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT (1/4) (9/4) s p R 1 Mrow amp Ψ
      caps.zero₁ caps.zero₂ SH dh height
      (Kh*(Z^(-(Mrow+3*g.δ-amp+ε))*(Hval true+Hval false)+1)) := by
  subst hqq hgδ
  obtain ⟨hext⟩ : Nonempty (∀Z v height t u E Cs Cc control : ℝ,
      1≤Z → 0≤height → 0≤Cs → 0≤Cc → 0≤ control →
      (2*(1+|v|+height+2*Real.pi*(|t|+|u|))≤Z^g.τ →
        E≤Cs*control*Z^(0:ℝ)*(2*(1+|v|+height+2*Real.pi*(|t|+|u|)))^0) →
      E≤Cc*control*Z^(4+cx) →
      E≤(2+4*Real.pi)^(geometry_extend_shifted_height_bound (4+cx) 0 g.τ g.τ_pos 0).choose*(Cs+Cc)*control*
        Z^(0:ℝ)*(1+|v|+height)^(geometry_extend_shifted_height_bound (4+cx) 0 g.τ g.τ_pos 0).choose*
        (1+|t|)^(geometry_extend_shifted_height_bound (4+cx) 0 g.τ g.τ_pos 0).choose*
        (1+|u|)^(geometry_extend_shifted_height_bound (4+cx) 0 g.τ g.τ_pos 0).choose) :=
    ⟨(geometry_extend_shifted_height_bound (4+cx) 0 g.τ g.τ_pos 0).choose_spec⟩
  generalize (geometry_extend_shifted_height_bound (4+cx) 0 g.τ g.τ_pos 0).choose=D at hext hdeg hKh
  intro reflected key hkey firstHeight χ₀
  unfold GeometryAffineMainCanonicalHighBound
  intro second t₀ u hKfirst rows ideal mass Label _ column hinj alloc hf firstIndex selected raw datum coefficient
    hP hPN canonical
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hside : 0≤geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key :=
    (geometry_high_factor_pos reflected _ key
      (geometrySupportConstant_pos (Fintype.card ι) 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))).le
  have hcSH := Profiles.control_nonneg p SH
  have hSpc : (p.control Sp)^2≤(p.control SH)^2 :=
    pow_le_pow_left₀ (Profiles.control_nonneg _ _) (CenteredMomentEnergyBandMonotonicity.profile_control_mono p hSpSH) 2
  have h00 : (p.control {(0,0)})^2≤(p.control SH)^2 :=
    pow_le_pow_left₀ (Profiles.control_nonneg _ _)
      (CenteredMomentEnergyBandMonotonicity.profile_control_mono p (by simpa using hSpSH hSp)) 2
  have hcontrol : 0≤(p.control SH)^2*geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key := mul_nonneg (sq_nonneg _) hside
  have hHv : 0≤Hval (!reflected) := hHval _
  have hCs₀ : 0≤Z^amp*Kt*(Z^(-(Mrow+3*g.δ+ε))*Hval (!reflected)) := by positivity
  refine le_trans (hext Z firstHeight height t₀ u _ (Z^amp*Kt*(Z^(-(Mrow+3*g.δ+ε))*Hval (!reflected))) Kc
    ((p.control SH)^2*geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key) hZ.le hheight hCs₀ hKc.le hcontrol ?_ ?_) ?_
  · -- the small heights: the top theorem and the records
    intro hh
    have hrange : |firstHeight|+height+2*Real.pi*(|u|+|t₀|)≤Z^g.τ := by
      have : 0≤2*Real.pi*(|t₀|+|u|) := by positivity
      nlinarith [abs_nonneg firstHeight]
    have htopZ := htop hZ s p caps θ w σ freq hm R 1 Mrow hR squarefree_one hRcap hMrow hMrow1 hfit
      height mesh hw hwL hwr hmesh hwm hσ hheight hfreq hT hβhi reflected second key firstHeight amp
      firstIndex hamp0 hamp homega hf hinj χ₀ fixedBadMask fixedBadMask_ne_zero (dvd_mul_right _ _)
      (dvd_mul_left _ _) Ψ t₀ u hrange hP hPN
    obtain ⟨hPU,hPNU,hbound⟩ := htopZ
    have hr := hrec reflected second key hkey firstHeight χ₀ hPU hPNU
    refine (hbound none).trans ?_
    dsimp only [Option.elim]
    rw [Real.rpow_zero, pow_zero, mul_one, mul_one]
    have h1 := mul_le_mul_of_nonneg_left hr (by positivity : 0≤Kt*(p.control Sp)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key)
    have h2 : Kt*(p.control Sp)^2*geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4))
        key*(Z^(-(Mrow+3*g.δ+ε))*Hval (!reflected))≤
        Kt*(p.control SH)^2*geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4))
        key*(Z^(-(Mrow+3*g.δ+ε))*Hval (!reflected)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSpc hKt.le) hside)
        (by positivity)
    calc _ ≤ Z^amp*(Kt*(p.control SH)^2*geometryHighFactor reflected
            (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*(Z^(-(Mrow+3*g.δ+ε))*Hval (!reflected))) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (Real.rpow_nonneg hZ0.le _)
      _ = _ := by ring
  · -- all heights: the coarse bound
    let highRows:=Finset.univ.filter (fun r : secondLiveRows (fun l=>(datum l).block)=>
      ((1+Cycle63.AffineLedger.q)/2)≤bufferValue g.e (mainPhysicalFamilySelector second datum canonical r))
    have hb:=hcoarse hZ (Label:=Label) reflected s R 1 Mrow amp (g.μ/8) firstHeight hKfirst squarefree_one
      caps.endpoints (by rw [caps.lower])
      (caps.sourceCap.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)))
      (caps.volumeLog.trans (by norm_num)) (by rw [abs_of_nonneg hMrow]; linarith) (hamp.trans (by norm_num))
      (homega.trans (by norm_num)) caps.controls caps.windows caps.plainScales caps.primeScales
      caps.poolCap caps.support₁ caps.support₂ caps.zero₁ caps.zero₂ hamp0 (by linarith [g.μ_pos])
      key firstIndex hinj hf (fun _=>χ₀) (fun _=>internalQ Q η₀) (fun _=>fixedBadMask)
      highRows second Ψ t₀ u p {(0,0)} (by simp) caps.profile₁ caps.profile₂
    change Z^(-amp)*(∑r∈highRows,∑L∈secondResidualIdeals (fun q=>(datum q).block) r.val,
      mainNormalizedPhysicalCost (Fintype.card ι) 1 (1/4) second datum coefficient t₀ u r.val L)≤
      Kc*(p.control {(0,0)})^2*geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*Z^cx at hb
    rw [geometry_main_high_physical_row_sum (Fintype.card ι) 1 (1/4) second datum coefficient t₀ u highRows] at hb
    have hh:=geometry_affine_high_unamplify Z amp cx _ (Kc*(p.control {(0,0)})^2*geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key) hZ0 hb
    refine hh.trans ?_
    have hz : Z^(amp+cx)≤Z^(4+cx) :=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [(abs_le.mp hamp).2])
    have hzc : 0≤Z^(amp+cx) := Real.rpow_nonneg hZ0.le _
    calc Kc*(p.control {(0,0)})^2*geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*Z^(amp+cx)
        ≤ Kc*(p.control SH)^2*geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*Z^(amp+cx) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h00 hKc.le) hside) hzc
      _ ≤ Kc*(p.control SH)^2*geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*Z^(4+cx) :=
          mul_le_mul_of_nonneg_left hz (by positivity)
      _ = _ := by ring
  · -- the constants and the degrees
    have hX0 : 0≤Z^(-(Mrow+3*g.δ-amp+ε)) := Real.rpow_nonneg hZ0.le _
    have hZa : Z^amp*Z^(-(Mrow+3*g.δ+ε))=Z^(-(Mrow+3*g.δ-amp+ε)) := by
      rw [← Real.rpow_add hZ0]; congr 1; ring
    have hHsum : Hval (!reflected)≤Hval true+Hval false := by
      cases reflected
      · simp only [Bool.not_false]; linarith [hHval false]
      · simp only [Bool.not_true]; linarith [hHval true]
    have hmax0 : 0≤ max Kt Kc := le_max_of_le_left hKt.le
    have hY : 0≤Z^(-(Mrow+3*g.δ-amp+ε))*(Hval true+Hval false) := mul_nonneg hX0 (add_nonneg (hHval _) (hHval _))
    have hpow : 0≤(2+4*Real.pi)^D := by positivity
    have hKh0 : 0≤Kh := le_trans (mul_nonneg hpow hmax0) hKh
    have h1 : Z^amp*Kt*(Z^(-(Mrow+3*g.δ+ε))*Hval (!reflected))=Kt*(Z^(-(Mrow+3*g.δ-amp+ε))*Hval (!reflected)) := by
      rw [← hZa]; ring
    have h2 : Kt*(Z^(-(Mrow+3*g.δ-amp+ε))*Hval (!reflected))+Kc≤ max Kt Kc*(Z^(-(Mrow+3*g.δ-amp+ε))*(Hval true+Hval false)+1) := by
      have e1 : Kt*(Z^(-(Mrow+3*g.δ-amp+ε))*Hval (!reflected))≤ max Kt Kc*(Z^(-(Mrow+3*g.δ-amp+ε))*(Hval true+Hval false)) :=
        mul_le_mul (le_max_left _ _) (mul_le_mul_of_nonneg_left hHsum hX0) (mul_nonneg hX0 (hHval _)) hmax0
      have e2 : Kc≤ max Kt Kc := le_max_right _ _
      linarith
    have hconst : (2+4*Real.pi)^D*(Z^amp*Kt*(Z^(-(Mrow+3*g.δ+ε))*Hval (!reflected))+Kc)≤
        Kh*(Z^(-(Mrow+3*g.δ-amp+ε))*(Hval true+Hval false)+1) := by
      rw [h1]
      calc (2+4*Real.pi)^D*(Kt*(Z^(-(Mrow+3*g.δ-amp+ε))*Hval (!reflected))+Kc)
          ≤ (2+4*Real.pi)^D*(max Kt Kc*(Z^(-(Mrow+3*g.δ-amp+ε))*(Hval true+Hval false)+1)) := mul_le_mul_of_nonneg_left h2 hpow
        _ = ((2+4*Real.pi)^D*max Kt Kc)*(Z^(-(Mrow+3*g.δ-amp+ε))*(Hval true+Hval false)+1) := by ring
        _ ≤ Kh*(Z^(-(Mrow+3*g.δ-amp+ε))*(Hval true+Hval false)+1) := mul_le_mul_of_nonneg_right hKh (by linarith)
    have ha1 : 1≤1+|firstHeight|+height := by linarith [abs_nonneg firstHeight]
    have hb1 : 1≤1+|t₀| := by linarith [abs_nonneg t₀]
    have hc1 : 1≤1+|u| := by linarith [abs_nonneg u]
    have hpa := pow_le_pow_right₀ ha1 hdeg
    have hpb := pow_le_pow_right₀ hb1 hdeg
    have hpc := pow_le_pow_right₀ hc1 hdeg
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_zero, mul_one]
    have hE : 0≤Kh*(Z^(-(Mrow+3*g.δ-amp+ε))*(Hval true+Hval false)+1) := mul_nonneg hKh0 (by linarith)
    calc _ = ((2+4*Real.pi)^D*(Z^amp*Kt*(Z^(-(Mrow+3*g.δ+ε))*Hval (!reflected))+Kc))*
            ((p.control SH)^2*geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key)*((1+|firstHeight|+height)^D*(1+|t₀|)^D*(1+|u|)^D) := by ring
      _ ≤ (Kh*(Z^(-(Mrow+3*g.δ-amp+ε))*(Hval true+Hval false)+1))*((p.control SH)^2*geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key)*
            ((1+|firstHeight|+height)^dh*(1+|t₀|)^dh*(1+|u|)^dh) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hconst hcontrol)
            (mul_le_mul (mul_le_mul hpa hpb (by positivity) (by positivity)) hpc (by positivity) (by positivity))
            (by positivity) (mul_nonneg hE hcontrol)
      _ = _ := by ring

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
