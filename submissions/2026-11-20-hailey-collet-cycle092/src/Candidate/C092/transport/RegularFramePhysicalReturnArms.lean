/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One early physical finite-energy supplier covers the actual original and
reference rectangles. Only the genuine original all-response P2 is assumed. -/
import Candidate.C092.transport.RegularFramePhysicalReturnOriginal
import Candidate.C092.transport.RegularFramePhysicalReturnReference
import Candidate.C092.transport.ReferenceShortP3Step
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularFramePhysicalReturn
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily CenteredMomentEnergyBands
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorPlainFiberSource
open QRH.Cycle092.WholeSlot QRH.Cycle092.StrongPair QRH.Cycle092.ReferenceShortP3
open QRH.Cycle092.ReferenceArmRadial
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source
local notation "O" => HeckeFamily.O

theorem physical_two_arm_source (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (M : Ideal O) [NeZero M] (Hr : Subgroup (O⧸M)ˣ) (hHr : RayOrthogonality.globalUnits M≤ Hr)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (n y mesh : ℝ) (hn : (1/3:ℝ)≤ n) (hy : (1/3:ℝ)≤ y)
    (hwidthCap : sourceWidth n y-(u:ℝ)≤ widthCap)
    (bPhi : ℝ) (hbPhi : 0< bPhi) (hPhi : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi)
    (old baseChar omega1 omega2 : Character) (Q : Ideal O)
    (hQM : Q≤ M) (hQ0 : internalQ Q baseChar≠0) (hQt : internalQ Q baseChar≠⊤)
    (hQ72 : internalQ Q baseChar≤ Ideal.span {(72:O)}) (hQ1 : Q≤ omega1.modulus) (hQ2 : Q≤ omega2.modulus)
    (Dp : ℕ) (Sp : Finset (ℕ×ℕ)) (Cp : ℝ) (hCp : 0< Cp)
    (hP2 : ∀ᶠ U : ℝ in atTop,OrderedP2At Slot M Hr hHr W n y mesh U old baseChar omega1 omega2 Q Dp Sp Cp) :
    ∃degree : ℕ,∃controls : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧
    ∀ᶠ U : ℝ in atTop,1< U ∧
    ∀V : ℝ,0≤ V → V≤2 → ∀ (T : Finset Slot) (theta : Slot→RayQuotient.Characters M Hr)
      (w sigma freq : Slot→ℝ) (tOld t1 t2 height : ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,sigma i=33/50) →
      0≤ height → (∀i,|freq i|≤ height) → (∑i∈T,w i)≤ sourceWidth n y-(u:ℝ) →
    ∀ (p : Profiles (1/4) (9/4)) (X1 X2 : ℝ),0< X1 → 0< X2 →
      ((X1≤3*U^n ∧ X2≤3*U^y) ∨
        (X1≤ U^shortCap ∧ X2≤ U) ∨ (X2≤ U^shortCap ∧ X1≤ U)) →
    ∀rows : Finset FreeRow,(∀z∈rows,initialKeep old (internalQ Q baseChar) z.val) →
      (∀z∈rows,rowNorm z≤ U^V) →
      finiteEnergyOn T rows (old.product omega1) (old.product omega2)
        (p.profile 0) (p.profile 1) t1 t2 X1 X2 (originalMark M Hr hHr old baseChar theta W U w sigma freq tOld)≤
      C*(p.control controls)^2*(1+|tOld|+2*|t1|+2*|t2|+height)^degree*U^(terminalFramePrice V) := by
  obtain ⟨Co,hCo,ho⟩ := physical_original_source Slot M Hr hHr W hW hWs n y mesh hn hy
    old baseChar omega1 omega2 Q Dp Sp Cp hCp hP2 hQ1 hQ2
  obtain ⟨Dr,Sr,Cr,hCr,hr⟩ := physical_reference_source Slot hbeta M Hr hHr W hW hWs bPhi hbPhi hPhi
    old baseChar omega1 omega2 Q hQM hQ0 hQt hQ72 hQ1 hQ2
  refine ⟨Dp+Dr,Sp∪Sr,Co+Cr,by positivity,?_⟩
  filter_upwards [ho,hr] with U ho hr
  refine ⟨ho.1,?_⟩
  intro V hV hV2 T theta w sigma freq tOld t1 t2 height hw hwm hsigma hh hfreq hwidth p X1 X2 hX1 hX2
    hrect rows hk hrow
  have hu : 0< U := zero_lt_one.trans ho.1
  have hb : 1≤1+|tOld|+2*|t1|+2*|t2|+height := by linarith [abs_nonneg tOld,abs_nonneg t1,abs_nonneg t2]
  rcases hrect with hrect|hrect
  · let height' := |tOld|+|t1|+|t2|+height
    have hf1 (i:Slot) : |tOld+freq i-t1|≤ height' := by
      dsimp [height'];linarith [abs_sub (tOld+freq i) t1,abs_add_le tOld (freq i),hfreq i,abs_nonneg t2]
    have hf2 (i:Slot) : |tOld+freq i-t2|≤ height' := by
      dsimp [height'];linarith [abs_sub (tOld+freq i) t2,abs_add_le tOld (freq i),hfreq i,abs_nonneg t1]
    have he := ho.2 V hV hV2 T theta w sigma freq tOld t1 t2 height' hw hwm hsigma (by dsimp [height'];positivity)
      (by dsimp [height'];linarith [abs_nonneg t1,abs_nonneg t2]) (fun i=>(hfreq i).trans (by dsimp [height'];linarith [abs_nonneg tOld,abs_nonneg t1,abs_nonneg t2])) hf1 hf2 hwidth
      p X1 X2 hX1 hX2 hrect.1 hrect.2 rows hk hrow
    have hc := pair_control_mono p (show Sp⊆Sp∪Sr from Finset.subset_union_left)
    have hp0 := p.control_nonneg Sp
    have hp1 := p.control_nonneg (Sp∪Sr)
    have hdeg : (1+|t1|+|t2|+height')^Dp≤(1+|tOld|+2*|t1|+2*|t2|+height)^(Dp+Dr) :=
      (pow_le_pow_left₀ (by dsimp [height'];positivity) (by dsimp [height'];linarith [abs_nonneg t1,abs_nonneg t2]) Dp).trans
        (pow_le_pow_right₀ hb (Nat.le_add_right Dp Dr))
    exact he.trans (by gcongr <;> first | positivity | linarith)
  · have he := hr.2 V hV hV2 T theta w sigma freq tOld t1 t2 height hw hsigma (hwidth.trans hwidthCap)
      p X1 X2 hh hX1 hX2 hrect rows hk hrow
    have hc := pair_control_mono p (show Sr⊆Sp∪Sr from Finset.subset_union_right)
    have hp0 := p.control_nonneg Sr
    have hp1 := p.control_nonneg (Sp∪Sr)
    have hdeg : (1+|t1|+|t1|+|t2|+|t2|+height)^Dr≤(1+|tOld|+2*|t1|+2*|t2|+height)^(Dp+Dr) :=
      (pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg tOld,abs_nonneg t1,abs_nonneg t2]) Dr).trans
        (pow_le_pow_right₀ hb (Nat.le_add_left Dr Dp))
    exact he.trans (by gcongr <;> first | positivity | linarith)

end
end QRH.Cycle092.RegularFramePhysicalReturn
#print axioms QRH.Cycle092.RegularFramePhysicalReturn.physical_two_arm_source
