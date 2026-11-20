/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One early physical finite-energy supplier covers the actual original and
reference rectangles. Only the genuine original all-response P2 is assumed. -/
import Candidate.C092.transport.RegularFramePhysicalReturnArms
import Candidate.C092.transport.RegularColoredTerminalLeafEventually
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

def PhysicalArmsAt (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (Hr : Subgroup (O⧸M)ˣ) (hHr : RayOrthogonality.globalUnits M≤ Hr)
    (W : ℝ→ℂ) (n y mesh U : ℝ) (old baseChar omega1 omega2 : Character) (Q : Ideal O)
    (degree : ℕ) (controls : Finset (ℕ×ℕ)) (C : ℝ) : Prop :=
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
      C*(p.control controls)^2*(1+|tOld|+2*|t1|+2*|t2|+height)^degree*U^(terminalFramePrice V)

theorem physicalArmsAt_mono {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (Hr : Subgroup (O⧸M)ˣ) (hHr : RayOrthogonality.globalUnits M≤ Hr)
    (W : ℝ→ℂ) (n y mesh U : ℝ) (hU : 1< U) (old baseChar omega1 omega2 : Character) (Q : Ideal O)
    {D D' : ℕ} {S S' : Finset (ℕ×ℕ)} {C C' : ℝ} (hD : D≤ D') (hS : S⊆S') (hC : C≤ C') (hC0 : 0≤ C)
    (src : PhysicalArmsAt Slot M Hr hHr W n y mesh U old baseChar omega1 omega2 Q D S C) :
    PhysicalArmsAt Slot M Hr hHr W n y mesh U old baseChar omega1 omega2 Q D' S' C' := by
  intro V hV hV2 T theta w sigma freq tOld t1 t2 height hw hwm hsigma hh hfreq hwidth p X1 X2 hX1 hX2
    hrect rows hk hrow
  have he := src V hV hV2 T theta w sigma freq tOld t1 t2 height hw hwm hsigma hh hfreq hwidth p X1 X2
    hX1 hX2 hrect rows hk hrow
  have hu : 0< U := zero_lt_one.trans hU
  have hb : 1≤1+|tOld|+2*|t1|+2*|t2|+height := by linarith [abs_nonneg tOld,abs_nonneg t1,abs_nonneg t2]
  have hp := pair_control_mono p hS
  have hn := p.control_nonneg S
  have hn' := p.control_nonneg S'
  have hd := pow_le_pow_right₀ hb hD
  have hC1 : 0≤C' := hC0.trans hC
  exact he.trans (by gcongr <;> first | positivity | assumption)

open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped

theorem finite_anchor_sources {L : ℝ} (theta : GData L)
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hPhi : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic theta.bΦ)
    (n y mesh : ℝ) (hn : (1/3:ℝ)≤ n) (hy : (1/3:ℝ)≤ y)
    (hwidthCap : sourceWidth n y-(u:ℝ)≤ widthCap)
    (eta omega1 omega2 : Character) (hQ1 : theta.Q≤ omega1.modulus) (hQ2 : theta.Q≤ omega2.modulus)
    (Dp : ℕ) (Sp : Finset (ℕ×ℕ)) (Cp : ℝ) (hCp : 0< Cp)
    (hP2 : ∀j : DictIdx,∀ᶠ U : ℝ in atTop,
      OrderedP2At (Fin theta.N) theta.rayM theta.Hray theta.hH theta.W n y mesh U
        (anchors eta j) theta.η₀ omega1 omega2 theta.Q Dp Sp Cp) :
    ∃D : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧
    ∀ᶠ U : ℝ in atTop,1< U ∧ ∀j : DictIdx,
      PhysicalArmsAt (Fin theta.N) theta.rayM theta.Hray theta.hH theta.W n y mesh U
        (anchors eta j) theta.η₀ omega1 omega2 theta.Q D S C := by
  have hx (j:DictIdx) : ∃D : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧
      ∀ᶠ U : ℝ in atTop,1< U ∧ PhysicalArmsAt (Fin theta.N) theta.rayM theta.Hray theta.hH theta.W n y mesh U
        (anchors eta j) theta.η₀ omega1 omega2 theta.Q D S C := by
    exact physical_two_arm_source (Fin theta.N) hbeta theta.rayM theta.Hray theta.hH theta.W theta.hW.continuous
      theta.hWs n y mesh hn hy hwidthCap theta.bΦ (by linarith [theta.hbΦ]) hPhi
      (anchors eta j) theta.η₀ omega1 omega2 theta.Q theta.hQ theta.hQ0 theta.hQt theta.hQ72 hQ1 hQ2
      Dp Sp Cp hCp (hP2 j)
  choose d S C hC hs using hx
  let D := ∑j:DictIdx,d j
  let controls := (Finset.univ:Finset DictIdx).biUnion S
  let K := 1+∑j:DictIdx,C j
  have hK : 0< K := by dsimp [K];have hh := Finset.sum_nonneg (fun j (_:j∈(Finset.univ:Finset DictIdx))=>(hC j).le);linarith
  refine ⟨D,controls,K,hK,?_⟩
  have he : ∀ᶠ U : ℝ in atTop,∀j:DictIdx,_ := Filter.eventually_all.mpr hs
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with U he hU
  refine ⟨hU,?_⟩
  intro j
  apply physicalArmsAt_mono theta.rayM theta.Hray theta.hH theta.W n y mesh U hU
    (anchors eta j) theta.η₀ omega1 omega2 theta.Q (S:=S j) (C:=C j)
    (Finset.single_le_sum (fun _ _=> Nat.zero_le _) (Finset.mem_univ j))
    (Finset.subset_biUnion_of_mem S (Finset.mem_univ j))
  · have hh := Finset.single_le_sum (s:=Finset.univ) (f:=C) (fun j _=>(hC j).le) (Finset.mem_univ j)
    dsimp [K];linarith
  · exact (hC j).le
  · exact (he j).2

end
end QRH.Cycle092.RegularFramePhysicalReturn
#print axioms QRH.Cycle092.RegularFramePhysicalReturn.physicalArmsAt_mono
