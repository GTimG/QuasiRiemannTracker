/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuinely exhausted prefix uses the native arbitrary-small unmarked pair.
Its positive source payment remains explicit; no epsilon is set to zero. -/
import Candidate.C092.transport.RegularFramePhysicalReturnSources
import Candidate.C092.transport.ExhaustedPairPriceAllRadii
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularFramePhysicalReturn
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily CenteredMomentEnergyBands
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
open QRH.Cycle092.WholeSlot QRH.Cycle092.StrongPair QRH.Cycle092.ExhaustedPairPrice
open QRH.Cycle092.FixedRayPair
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
local notation "O" => HeckeFamily.O

def EmptyAt (U delta : ℝ) (eta1 eta2 : Character) (Q1 Q2 : Ideal O)
    (degree : ℕ) (controls : Finset (ℕ×ℕ)) (C : ℝ) : Prop :=
  ∀V : ℝ,0≤ V → V≤2 → ∀ (p : Profiles (1/4) (9/4)) (t1 t2 X1 X2 : ℝ),
  0< X1 → 0< X2 → X1≤ U → X2≤ U → ∀rows : Finset FreeRow,
  (∀z∈rows,initialKeep eta1 Q1 z.val) → (∀z∈rows,initialKeep eta2 Q2 z.val) →
  (∀z∈rows,rowNorm z≤ U^V) →
  (∑z∈rows,‖QRH.Cycle092.OrdinaryColumn.original eta1 (fixedBadMask*idealGenerator 1) 1 z.val (p.profile 0) t1 X1‖^2*
    ‖QRH.Cycle092.OrdinaryColumn.original eta2 (fixedBadMask*idealGenerator 1) 1 z.val (p.profile 1) t2 X2‖^2)≤
    C*(p.control controls)^2*(1+|t1|+|t2|)^degree*U^(V+delta)

theorem emptyAt_mono {U delta : ℝ} (hU : 1< U) (eta1 eta2 : Character) (Q1 Q2 : Ideal O)
    {D D' : ℕ} {S S' : Finset (ℕ×ℕ)} {C C' : ℝ} (hD : D≤ D') (hS : S⊆S') (hC : C≤ C') (hC0 : 0≤ C)
    (src : EmptyAt U delta eta1 eta2 Q1 Q2 D S C) : EmptyAt U delta eta1 eta2 Q1 Q2 D' S' C' := by
  intro V hV hV2 p t1 t2 X1 X2 hx1 hx2 hc1 hc2 rows hk1 hk2 hy
  have he := src V hV hV2 p t1 t2 X1 X2 hx1 hx2 hc1 hc2 rows hk1 hk2 hy
  have hu : 0< U := zero_lt_one.trans hU
  have hCp : 0≤ C' := hC0.trans hC
  have hp := QRH.Cycle092.ReferenceShortP3.pair_control_mono p hS
  have hn := p.control_nonneg S
  have hn' := p.control_nonneg S'
  have hd := pow_le_pow_right₀ (show 1≤1+|t1|+|t2| by linarith [abs_nonneg t1,abs_nonneg t2]) hD
  exact he.trans (by gcongr)

theorem exhausted_anchor_sources {L : ℝ} (theta : GData L)
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hPhi : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic theta.bΦ)
    (eta omega1 omega2 : Character) (hQ1 : theta.Q≤ omega1.modulus) (hQ2 : theta.Q≤ omega2.modulus)
    (delta : ℝ) (hdelta : 0< delta) :
    ∃D : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀ᶠ U : ℝ in atTop,1< U ∧ ∀j : DictIdx,
      EmptyAt U delta ((anchors eta j).product omega1) ((anchors eta j).product omega2)
        (internalQ theta.Q (theta.η₀.product omega1)) (internalQ theta.Q (theta.η₀.product omega2)) D S C := by
  have hq1 := internalQ_product theta.Q theta.η₀ omega1 hQ1
  have hq2 := internalQ_product theta.Q theta.η₀ omega2 hQ2
  have hx (j:DictIdx) : ∃D : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀ᶠ U : ℝ in atTop,1< U ∧
      EmptyAt U delta ((anchors eta j).product omega1) ((anchors eta j).product omega2)
        (internalQ theta.Q (theta.η₀.product omega1)) (internalQ theta.Q (theta.η₀.product omega2)) D S C := by
    obtain ⟨D,S,C,hC,hs⟩ := exhausted_pair_all_radii hbeta theta.rayM theta.Hray theta.hH theta.bΦ 2 delta
      (by norm_num) hdelta (by linarith [theta.hbΦ]) hPhi
      ((anchors eta j).product omega1) ((anchors eta j).product omega2)
      (theta.η₀.product omega1) (theta.η₀.product omega2) theta.Q theta.Q
      theta.hQ (hq1 ▸ theta.hQ0) (hq1 ▸ theta.hQt) (hq1 ▸ theta.hQ72)
      theta.hQ (hq2 ▸ theta.hQ0) (hq2 ▸ theta.hQt) (hq2 ▸ theta.hQ72)
    have hd := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
    refine ⟨D,S,C*(QuadraticInitialBound.diagonalControl radialMajorant+1),by positivity,hs.mono ?_⟩
    intro U hU
    refine ⟨hU.1,?_⟩
    intro V hV hV2 p t1 t2 X1 X2 hx1 hx2 hc1 hc2 rows hk1 hk2 hy
    have he := hU.2 V hV hV2 p t1 t2 0 X1 X2 (by norm_num) hx1 hx2 hc1 hc2 rows hk1 hk2 hy
    simp only [add_zero] at he
    have hu : 0< U := zero_lt_one.trans hU.1
    exact he.trans (by gcongr <;> linarith)
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
  apply emptyAt_mono hU ((anchors eta j).product omega1) ((anchors eta j).product omega2) _ _
    (S:=S j) (C:=C j) (Finset.single_le_sum (fun _ _=> Nat.zero_le _) (Finset.mem_univ j))
    (Finset.subset_biUnion_of_mem S (Finset.mem_univ j))
  · have hh := Finset.single_le_sum (s:=Finset.univ) (f:=C) (fun j _=>(hC j).le) (Finset.mem_univ j)
    dsimp [K];linarith
  · exact (hC j).le
  · exact (he j).2

end
end QRH.Cycle092.RegularFramePhysicalReturn
#print axioms QRH.Cycle092.RegularFramePhysicalReturn.exhausted_anchor_sources
