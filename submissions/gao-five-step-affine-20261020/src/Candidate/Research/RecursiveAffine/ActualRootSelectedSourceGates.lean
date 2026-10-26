/- Bare-root source gates from the actual native first/second source.
Copyright (c) 2026 Zhongpai Gao. Native geometry by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ActualSelectedSourceGates
import Candidate.Research.RecursiveAffine.NativeRootPaidSource
import Candidate.Research.RecursiveAffine.NativeCoarseSource
import Candidate.Research.RecursiveAffine.NativeRootStep
import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighSourceCaps
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowNormalizedPayment

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 6000
namespace OAI.SevenEighths.Cycle153ActualRootSourceGates
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization CenteredMomentSourceLiveColumn
open CenteredMomentEnergyBands CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open Cycle153JointCount Cycle153RegionalLow Cycle153RootStep Cycle153LowPhysical
open Cycle153SourceSchedule Cycle153ActualSourceGates Cycle153.RegionalSchedule
open CenteredMomentEnergyInputParentCapacity CenteredMomentFiniteProfileExceptional

noncomputable local instance actualRootSourceLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger

variable {Current : Type} [Fintype Current] [DecidableEq Current]

/-- Literal root volume. The root plane is only a majorant and is never
identified with this actual source length. -/
theorem actual_root_raw_volume (Z : ℝ)(hZ : 1<Z)(s : Input Current)(w : Current→ℝ)
    (hscale : ∀i,s.P i=Z^(w i))
    (hwindow : Cycle63.AffineLedger.PlainWindow (length Z s.X₁) (length Z s.X₂) (∑i,w i)) :
    Real.logb Z (volume s)=length Z s.X₁+length Z s.X₂+∑i,w i :=by
  have h1:=Cycle63InitialSource.initial_scale_exact Z s.X₁ 1 hZ one_pos
    (by simpa only [mul_one] using hwindow.left_ge)
  have h2:=Cycle63InitialSource.initial_scale_exact Z s.X₂ 1 hZ one_pos
    (by simpa only [mul_one] using hwindow.right_ge)
  have he1 : Real.logb Z s.X₁=length Z s.X₁ :=by
    calc
      _=Real.logb Z (Z^(length Z s.X₁)):=congrArg (Real.logb Z) h1
      _=_:=Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
  have he2 : Real.logb Z s.X₂=length Z s.X₂ :=by
    calc
      _=Real.logb Z (Z^(length Z s.X₂)):=congrArg (Real.logb Z) h2
      _=_:=Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
  rw [input_volume_log,he1,he2]
  congr 1
  exact Finset.sum_congr rfl (fun i _=>by rw [hscale,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'])

/-- The package retains the actual same-bin mass and every actual selected
row. Unit and physical row scale are exactly1 at this bare root. -/
def ActualRootPaidGatePackage
    (Z : ℝ)(hZ : 1<Z)(budget : ℕ)(s : Input Current)(w : Current→ℝ)
    (p : Profiles (1/4) (9/4))(Cs : ℝ)(caps : GeometryAffineLowSourceGates s p Cs Z) : Prop :=
  ∀(R seed : Ideal O)(hseed : Squarefree seed)(reflected : Bool)(key : ℤ×(Fin 5→ℤ))
    (Psi : 𝓢(ℝ,ℂ)),
  ∃exponent sideLower : ℝ,
  let massLoss:=3*nativeDriverRate budget-sideLower
  let sideError:=actualSideError Z budget
  ∃hside : ∀l : FirstColumnIndex (geometryFirstSource s R seed (Z^(1:ℝ)) Z (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key),
    massLoss+lowLabelSide reflected Z (Real.logb Z (volume s))
      (geometryFirstLabel s R seed (Z^(1:ℝ)) Z (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key l) ≤ sideError,
    (∀l : FirstColumnIndex (geometryFirstSource s R seed (Z^(1:ℝ)) Z (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key),
      geometryFirstHighMass reflected s R seed Psi 1 Z (nativeMu/64) (nativeDriverRate budget)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key l ≤
        geometryHighFactor reflected (geometrySupportConstant budget 1 (1/4) (1/4)) key*Z^massLoss) ∧
  ∀(second : Bool)(firstHeight : ℝ){Label : Type}[Fintype Label]
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^(1:ℝ)) Z (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key),
    (∀l,frozenCoefficient (firstIndex l).2.val
      (geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val)
      R s.ν s.W s.P≠0)→
  ∀r : NativeLowRows reflected s R seed Z 1 (rootSourceAmp w) (nativeMu/64) (nativeMu/8)
      (9/4) firstHeight (Fintype.card Current) hZ key caps.zero₁ caps.zero₂ firstIndex,
  let node:=actualRootSelectedPaidNode Z hZ reflected second s R seed 1 (rootSourceAmp w)
    (nativeMu/64) (nativeMu/8) (nativeDriverRate budget) (9/4) firstHeight (Fintype.card Current)
    key caps.zero₁ caps.zero₂ firstIndex massLoss sideError (fun l=>hside (firstIndex l).1.val) r
  node.SourceGates ∧ node.FineSourceGates

/-- Native source radii, true root window, same-bin first mass and the
actual chosen μ/δ schedule construct the bare-root physical gates. -/
theorem eventual_actual_root_selected_paid_gates (etaSeed : Character)(budget : ℕ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ Real.logb Z (etaSeed.modulus.absNorm:ℝ) ≤ nativeMu/16 ∧
    ∀(hZ : 1<Z)(s : Input Current)(w : Current→ℝ)
      (p : Profiles (1/4) (9/4))(Cs : ℝ)(caps : GeometryAffineLowSourceGates s p Cs Z),
      Fintype.card Current ≤ budget→(∀i,0 ≤ w i)→(∀i,s.P i=Z^(w i))→
      Cycle63.AffineLedger.PlainWindow (length Z s.X₁) (length Z s.X₂) (∑i,w i)→
      ActualRootPaidGatePackage Z hZ budget s w p Cs caps :=by
  have hmu0:=div_pos nativeMu_pos (by norm_num : (0:ℝ)<8)
  have hmu1 : nativeMu/8 ≤ 1 :=by norm_num [nativeMu,primitiveError]
  have hcaps:=eventual_actual_geometry_main_high_source_caps budget (9/4) (9/4) (nativeMu/8)
    (by norm_num) (by norm_num) hmu0 hmu1
  have hanchor:=Cycle63Moment.fixed_anchor_width_uniform (fun _ : Unit=>etaSeed) 1 (nativeMu/16)
    one_pos (div_pos nativeMu_pos (by norm_num))
  filter_upwards [hcaps,eventually_actual_source_small budget,hanchor] with Z hc hs ha
  refine ⟨hc.1,?_,?_⟩
  · have hh:=ha.2 () 1 le_rfl
    simpa only [mul_one] using hh
  intro hZ s w p Cs caps hcard hw hscale hwindow
  unfold ActualRootPaidGatePackage
  intro R seed hseed reflected key Psi
  have hsmall:=hs.2 1 (by norm_num)
  rw [Real.rpow_one] at hsmall
  have hlog:=actual_root_raw_volume Z hZ s w hscale hwindow
  have hlog0 : 0 ≤ Real.logb Z (volume s) :=by
    rw [hlog]
    have h1:=Cycle63.AffineLedger.windowBottom_pos.trans_le hwindow.left_ge
    have h2:=Cycle63.AffineLedger.windowBottom_pos.trans_le hwindow.right_ge
    have hh : 0 ≤ ∑i,w i:=Finset.sum_nonneg (fun i _=>hw i)
    linarith only [h1,h2,hh]
  have hcell:=Cycle63.AffineLedger.originalCell_mem ⟨hwindow.slots_ge,hwindow.slots_le⟩
  have hamp0 : 0 ≤ rootSourceAmp w :=(Cycle63.AffineLedger.amp_pos
    (Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1)).le
  have hamp1 : rootSourceAmp w ≤ 1 :=(Cycle63.AffineLedger.amp_bounds
    (Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1)).2.trans Cycle63.AffineLedger.amplifierCap_le_one
  obtain ⟨exponent,sideLower,hbin,hfirst⟩:=actual_root_selected_paid_source Z hZ reflected budget 1 (1/4)
    (by norm_num) (by norm_num) s R seed Psi 1 (nativeMu/64) 3 (nativeDriverRate budget)
    hcard (by rw [caps.lower]) hseed caps.zero₁ caps.zero₂ caps.sourceCap
    (nativeDriverRate_budgets budget).1.le caps.support₁ caps.support₂ key
  refine ⟨exponent,sideLower,?_⟩
  intro massLoss sideError
  let hside : ∀l : FirstColumnIndex (geometryFirstSource s R seed (Z^(1:ℝ)) Z (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key),
      massLoss+lowLabelSide reflected Z (Real.logb Z (volume s))
        (geometryFirstLabel s R seed (Z^(1:ℝ)) Z (nativeMu/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key l) ≤ sideError :=fun l=>(hfirst l).2.2
  refine ⟨hside,fun l=>(hfirst l).2.1,?_⟩
  intro second firstHeight Label _ firstIndex hf r node
  have hfirstCaps:=actual_main_low_first_source_gates reflected s R seed (Z^(1:ℝ)) Z (nativeMu/64) 3
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hseed caps.zero₁ caps.zero₂ caps.sourceCap key firstIndex r.val.1
  let original:=mainLowSelectedOriginal reflected s R seed Z 1 (rootSourceAmp w) (nativeMu/64) (nativeMu/8)
    (9/4) firstHeight (Fintype.card Current) hZ key caps.zero₁ caps.zero₂ firstIndex r
  have hvolume3 : volume s ≤ Z^(3:ℝ) :=
    caps.volume.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))
  have hsecondCaps:=hc.2 reflected s R seed 1 (rootSourceAmp w) (nativeMu/64) (nativeMu/8)
    firstHeight hZ hcard caps.endpoints hseed caps.zero₁ caps.zero₂ caps.sourceCap hvolume3
    key 1 1 1 original.val (hf r.val.1)
  have hC : (node.C.absNorm:ℝ) ≤ Z^(4:ℝ) :=hsecondCaps.2.2.1
  have hD : (node.D.absNorm:ℝ) ≤ Z^(4:ℝ) :=hsecondCaps.2.2.2
  have hown : ((if second then node.D else node.C).absNorm:ℝ) ≤ Z^(130:ℝ) :=by
    apply le_trans (by cases second <;> assumption)
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)
  have htiny : (1/(10:ℝ)^15) ≤ 1/4 :=by norm_num
  constructor
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [node,actualRootSelectedPaidNode] using (le_rfl : (1:ℝ) ≤ 1)
    · simpa only [node,actualRootSelectedPaidNode] using (by norm_num : (0:ℝ) ≤ 1)
    · simpa only [node,actualRootSelectedPaidNode] using (le_rfl : (1:ℝ) ≤ 1)
    · simpa only [node,actualRootSelectedPaidNode] using hlog0
    · simpa only [node,actualRootSelectedPaidNode] using
        (abs_le.mp caps.volumeLog).2.trans (by norm_num : (3:ℝ) ≤ 4)
    · simpa only [node,actualRootSelectedPaidNode] using hamp0
    · simpa only [node,actualRootSelectedPaidNode] using hamp1
    · simpa only [node,actualRootSelectedPaidNode,Real.rpow_one] using hsmall.1
    · simpa only [node,actualRootSelectedPaidNode,Real.rpow_one] using hsmall.2.1.trans htiny
    · simpa only [node,actualRootSelectedPaidNode] using hsmall.2.2.1
    · simpa only [node,actualRootSelectedPaidNode] using hsmall.2.2.2.1.trans htiny
    · simpa only [node,actualRootSelectedPaidNode] using hsmall.2.2.2.2.trans htiny
    · simpa only [node,actualRootSelectedPaidNode,Real.rpow_one] using
        And.intro hfirstCaps.2.2.2.2.2.1 hfirstCaps.2.2.2.2.2.2.1
    · simpa only [node,actualRootSelectedPaidNode,Real.rpow_one] using hown
  · have he : (1:ℝ)/10^15=1/1000000000000000 :=by norm_num
    refine ⟨?_,?_,?_⟩
    · simpa only [node,actualRootSelectedPaidNode,Real.rpow_one,he] using hsmall.2.1
    · simpa only [node,actualRootSelectedPaidNode,he] using hsmall.2.2.2.1
    · simpa only [node,actualRootSelectedPaidNode,he] using hsmall.2.2.2.2

end
end OAI.SevenEighths.Cycle153ActualRootSourceGates
#print axioms OAI.SevenEighths.Cycle153ActualRootSourceGates.eventual_actual_root_selected_paid_gates
