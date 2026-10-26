/- The actual native OLD source is joined to the same literal selected LOW forest.
Copyright (c) 2026 Zhongpai Gao. Native estimates by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootSelectedForest
import Candidate.Research.RecursiveAffine.NativeSelectedRootSourceOld

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open Cycle63FinalCapacity CenteredMomentSectorLocalization Cycle153SourceReturn Cycle153LowPhysical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSecondPhysicalBlock CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstAmplificationChoice CenteredMomentFirstDiscardedEnergy
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentLogDyadic CenteredMomentWholeDivisorShell
open CenteredMomentOriginalCommonHarmonic CenteredMomentAmplifiedRetainedRadius
open CenteredMomentCanonicalFirst CenteredMomentFirstExceptionalPrefactor
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

/-- The first mass, native OLD allowance and actual selected forest use
one literal carrier. Its OLD bound is produced by the original native
source theorem. The AtState row scale and amplifier cancel only in the
explicit power identity; no reciprocal or selected mass is discarded. -/
theorem eventual_actual_selected_source_with_old
    (Nbudget : ℕ)(supply ap epsV Bcap epsLabels U epsFirst : ℝ)
    (hsupply : 0<supply)(hap : 0<ap)(hV : 0<epsV)(hB : 0 ≤ Bcap)
    (hLabels : 0<epsLabels)(hU : 0 ≤ U)(hFirst : 0<epsFirst) :
    ∃Kold : ℝ,0<Kold ∧ ∀ᶠZ : ℝ in atTop,2 ≤ Z ∧
    ∀{M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M  ≤  H}
    {Depth : Type} [Fintype Depth] {junction : Depth→ℝ} {Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}
    {OwnBase : Type} {ownBase : Character→OwnBase→Character}
    {eta : Character} {Bnorm T qOwn : ℝ} {root : O}
    {Label : Type} [Fintype Label]
    (reflected second : Bool) (s : Input alpha) (R : Ideal O)
    (Mrow amp xi reserve eps b firstHeight : ℝ) (N : ℕ) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ)) (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
    (firstIndex : Label → GeometryLowFirstIndex reflected s R (1:Ideal O) (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (units : FirstSourceLabel→O)
    (own : ReturnedPartAt M H hH qOwn ownBase eta Z Bnorm T root)
    (driverDelta driverError common pad loss shellLoss slotLoss q mesh
      Cg fixed physical : ℝ)
    (hCg : 0  ≤  Cg) (hfixed : 0  ≤  fixed) (hphysical : 0  ≤  physical)
    (Psi : 𝓢(ℝ,ℂ))(Bmass epsMass : ℝ),
    let first := fun l => geometryFirstLabel s R (1:Ideal O) (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val
    let Rows := NativeLowRows reflected s R (1:Ideal O) Z Mrow amp xi reserve b firstHeight N
      hZ key hz1 hz2 firstIndex
    let label := fun r : Rows => actualSecondSupportedLabel _ _ _ _ _ _ _ r.val.2
      (actual_main_low_selected_inactive reflected s R (1:Ideal O) Z Mrow amp xi reserve b firstHeight N
        hZ key hz1 hz2 firstIndex r)
    let childRoot := fun r : Rows =>
      childMultiplier (!reflected) root units ⟨first r.val.1,⟨(label r).1,(label r).2.val⟩⟩
    let childSrc := fun l => geometryLowFirstChild reflected s R (1:Ideal O) (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstHeight (firstIndex l)
    let radius := fun r : Rows => firstMainRadius reflected (Z^Mrow) (volume s) Z xi
      (3*amp) reserve (first r.val.1)
    let nominal := fun r : Rows => secondNominal 1 Z amp (frequencyLoss Z 32 xi+reserve)
      (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
      (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
      (label r).1.1 (label r).1.2 (label r).2.val
    let ownNorm := fun r : Rows => ((if second then (label r).1.2 else (label r).1.1).absNorm : ℝ)
    let pay0 := fun r : Rows => Z^(-amp)*(radius r/volume (childSrc r.val.1))*
      (normalizer (label r).1.1 (label r).1.2 (label r).2.val*(ownNorm r)^(shellLoss-1))*
      Z^(nominal r+amp+common+pad)
    let payExponent := fun r : Rows => lowGeometryExponent reflected Z (Real.logb Z (volume s))
      (first r.val.1)+(common+pad)+(1-Mrow)+epsV+Bcap*shellLoss
    let mass := fun l=>geometryFirstHighMass reflected s R 1 Psi Mrow Z xi epsMass
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val
    let allowance := fun r : Rows=>lowAllowance Z
      (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
      (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
      (label r).1.1 (label r).1.2 (if second then (label r).1.2 else (label r).1.1)
    let outer := Mrow+3*driverDelta-amp+driverError
    let fees := fun _ : Rows => loss+3*driverDelta+driverError+epsV+Bcap*shellLoss+
      pad+slotLoss+q*mesh
    ∀(w : alpha→ℝ)(deleted : Rows→Finset alpha)
      (children : (r : Rows)→DepthReturnedFamily M H hH junction Base base eta Z Bnorm T (childRoot r))
      (oldExponent columnEnergy : Rows→ℝ),
    (∀r : Rows,Supported (label r).1.1) → (∀r : Rows,Supported (label r).1.2) →
    (∀r : Rows,0  ≤  mass r.val.1) → (∀r : Rows,0 < volume (childSrc r.val.1)) → (∀r : Rows,0  ≤  radius r) →
    (∀r : Rows,oldExponent r  ≤  nominal r+amp+common+allowance r) →
    (∀r : Rows,pay0 r  ≤  Z^(payExponent r)/ownNorm r) →
    (∀r : Rows,mass r.val.1  ≤  physical*Z^loss) →
    (∀r : Rows,columnEnergy r  ≤  Cg*fixed*(ownNorm r)^(shellLoss-1)*
      (Z^(oldExponent r)+Z^(slotLoss+q*((∑i∈deleted r,w i)+mesh))*(children r).value)*Z^pad) →
    Fintype.card alpha ≤  Nbudget → supply ≤  s.lower →
    (∀i I,I∈s.pools i→(I.absNorm:ℝ) ≤  Z^U) →
    sourceRadius s ≤  Z^Bmass → Bmass+1 ≤  Bcap → 0 ≤  epsMass → 0 ≤  shellLoss →
    (∀x,s.W₁ x≠0→ap ≤  x) → (∀x,s.W₂ x≠0→ap ≤  x) →
    (∀l,frozenCoefficient (firstIndex l).2.val
      (geometryColumnIdeal reflected s R 1 (Z^Mrow) Z xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val) R s.ν s.W s.P≠0) →
    Function.Injective (fun l=>(geometryFirstLabel s R 1 (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val,(firstIndex l).1.val.2.1.val)) →
    (∀l,sourceRadius (geometryLowFirstChild reflected s R 1 (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstHeight (firstIndex l)) ≤  Z^Bcap) →
    ∀box : Finset (Fin 4→ℤ),
    (∀r : NativeLowRows reflected s R 1 Z Mrow amp xi reserve b firstHeight N hZ key hz1 hz2 firstIndex,
      actualSecondDyad
        (geometryLowFirstChild reflected s R 1 (Z^Mrow) Z xi
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstHeight (firstIndex r.val.1))
        (R*geometryColumnIdeal reflected s R 1 (Z^Mrow) Z xi
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex r.val.1).1.val)
        (firstIndex r.val.1).1.val.2.1.val
        (firstMainRadius reflected (Z^Mrow) (volume s) Z xi (3*amp) reserve
          (geometryFirstLabel s R 1 (Z^Mrow) Z xi (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
            key (firstIndex r.val.1).1.val))
        (firstMainFourierScale reflected (Z^Mrow) (volume s) Z xi (3*amp) reserve b
          N (geometryFirstLabel s R 1 (Z^Mrow) Z xi
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex r.val.1).1.val)) Z xi r.val.2∈box) →
    let F := attach_native_low_rows reflected second s R (1:Ideal O) Z Mrow amp xi reserve eps b firstHeight N
      hZ key hz1 hz2 firstIndex units own w deleted q fees children
    Z^outer*(∑r : Rows,(mass r.val.1/volume (childSrc r.val.1)*radius r*
      normalizer (label r).1.1 (label r).1.2 (label r).2.val)*columnEnergy r)  ≤
      Kold*Cg*fixed*geometryHighFactor reflected (geometrySupportConstant Nbudget supply ap ap) key*
        (box.card:ℝ)*Z^(1+3*driverDelta+driverError+Bmass*epsMass+common+pad+
          epsV+Bcap*shellLoss+epsLabels+epsFirst)+Cg*fixed*physical*F.value := by
  obtain ⟨Kold,hKold,hSource⟩:=eventual_actual_selected_root_source_with_old (alpha:=alpha)
    Nbudget supply ap epsV Bcap epsLabels U epsFirst hsupply hap hV hB hLabels hU hFirst
  refine ⟨Kold,hKold,?_⟩
  filter_upwards [hSource] with Z hZold
  refine ⟨hZold.1,?_⟩
  intro M _ H hH Depth _ junction Base base OwnBase ownBase eta Bnorm T qOwn root Label _
    reflected second s R Mrow amp xi reserve eps b firstHeight N hZ key hz1 hz2 firstIndex units own
    driverDelta driverError common pad loss shellLoss slotLoss q mesh Cg fixed physical hCg hfixed hphysical
    Psi Bmass epsMass first Rows label childRoot childSrc radius nominal ownNorm pay0 payExponent mass allowance outer fees
    w deleted children oldExponent columnEnergy hC hD hmass hvolume hradius hOldExp hpay hmasscap hcolumn
    hN hlower hpool hsource hBstrong hMass hShell hs1 hs2 hf hinj hchildsource box hbox F
  let RootF:=attach_native_root_low_rows reflected second s R 1 Z Mrow amp xi reserve eps b firstHeight N
    hZ key hz1 hz2 firstIndex units w deleted q fees children
  have hroot:=hZold.2 reflected second s R Mrow amp xi reserve eps b firstHeight N hZ key hz1 hz2 firstIndex units
    driverDelta driverError common pad loss shellLoss slotLoss q mesh Cg fixed physical hCg hfixed hphysical
    Psi Bmass epsMass w deleted children oldExponent columnEnergy hC hD hmass hvolume hradius hOldExp hpay hmasscap hcolumn
    hN hlower hpool hsource hBstrong hMass hShell hs1 hs2 hf hinj hchildsource box hbox
  have hvalue : F.value=own.value+RootF.value := by
    change (attach_native_low_rows reflected second s R 1 Z Mrow amp xi reserve eps b firstHeight N
      hZ key hz1 hz2 firstIndex units own w deleted q fees children).value=own.value+
      (attach_native_root_low_rows reflected second s R 1 Z Mrow amp xi reserve eps b firstHeight N
        hZ key hz1 hz2 firstIndex units w deleted q fees children).value
    rw [attach_native_low_rows_value,attach_native_root_low_rows_value]
  have htail : RootF.value≤F.value := by
    rw [hvalue]
    exact le_add_of_nonneg_left (own.value_nonneg (zero_lt_one.trans hZ).le)
  exact hroot.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left htail
    (mul_nonneg (mul_nonneg hCg hfixed) hphysical)))

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.eventual_actual_selected_source_with_old
