/- Copyright (c) 2026 Hailey Collet; whole-forest assembly (c) 2026 Zhongpai Gao.
Released under Apache 2.0. The physical row normalization is unchanged. -/
import Candidate.Research.RecursiveAffine.NativeSelectedForest

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open Cycle63FinalCapacity CenteredMomentSectorLocalization Cycle153SourceReturn
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSecondPhysicalBlock CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

/-- Assemble the literal root LOW rows without an artificial own-HIGH
prefix. Root own HIGH is paid by its separate marked provider. The actual
LOW carrier is exactly the dependent sum of root rows and child prefixes.
All native physical row normalization remains literal. The column estimate is supplied by the actual common and
column operator applied to the strictly deeper source. The native first
mass payment and reciprocal normalizer produce the raw edge, with the
AtState outer scale, deletion charge, and driver errors each inserted
exactly once. No returned-count or sharp price estimate is a premise. -/
theorem actual_selected_root_low_rows_forest
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M ≤ H}
    {Depth : Type} [Fintype Depth] {junction : Depth→ℝ} {Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}
    {eta : Character} {Bnorm T : ℝ} {root : O}
    {Label : Type} [Fintype Label]
    (reflected second : Bool) (s : Input alpha) (R seed : Ideal O)
    (Z Mrow amp xi reserve eps b firstHeight : ℝ) (N : ℕ) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ)) (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
    (firstIndex : Label → GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (units : FirstSourceLabel→O)
    (driverDelta driverError common pad loss epsV normCap shellLoss slotLoss q mesh
      Cg fixed physical : ℝ)
    (hCg : 0 ≤ Cg) (hfixed : 0 ≤ fixed) (hphysical : 0 ≤ physical) :
    let first := fun l => geometryFirstLabel s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val
    let Rows := NativeLowRows reflected s R seed Z Mrow amp xi reserve b firstHeight N
      hZ key hz1 hz2 firstIndex
    let label := fun r : Rows => actualSecondSupportedLabel _ _ _ _ _ _ _ r.val.2
      (actual_main_low_selected_inactive reflected s R seed Z Mrow amp xi reserve b firstHeight N
        hZ key hz1 hz2 firstIndex r)
    let childRoot := fun r : Rows =>
      childMultiplier (!reflected) root units ⟨first r.val.1,⟨(label r).1,(label r).2.val⟩⟩
    let childSrc := fun l => geometryLowFirstChild reflected s R seed (Z^Mrow) Z xi
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
      (first r.val.1)+(common+pad)+(1-Mrow)+epsV+normCap*shellLoss
    let outer := Mrow+3*driverDelta-amp+driverError
    let fees := fun _ : Rows => loss+3*driverDelta+driverError+epsV+normCap*shellLoss+
      pad+slotLoss+q*mesh
    ∀(w : alpha→ℝ)(deleted : Rows→Finset alpha)
      (children : (r : Rows)→DepthReturnedFamily M H hH junction Base base eta Z Bnorm T (childRoot r))
      (mass : Label→ℝ)(oldExponent allowance columnEnergy : Rows→ℝ),
    (∀r : Rows,Supported (label r).1.1) → (∀r : Rows,Supported (label r).1.2) →
    (∀r : Rows,0 ≤ mass r.val.1) → (∀r : Rows,0 < volume (childSrc r.val.1)) → (∀r : Rows,0 ≤ radius r) →
    (∀r : Rows,oldExponent r ≤ nominal r+amp+common+allowance r) →
    (∀r : Rows,pay0 r ≤ Z^(payExponent r)/ownNorm r) →
    (∀r : Rows,mass r.val.1 ≤ physical*Z^loss) →
    (∀r : Rows,columnEnergy r ≤ Cg*fixed*(ownNorm r)^(shellLoss-1)*
      (Z^(oldExponent r)+Z^(slotLoss+q*((∑i∈deleted r,w i)+mesh))*(children r).value)*Z^pad) →
    let F := attach_native_root_low_rows reflected second s R seed Z Mrow amp xi reserve eps b firstHeight N
      hZ key hz1 hz2 firstIndex units w deleted q fees children
    Z^outer*(∑r : Rows,(mass r.val.1/volume (childSrc r.val.1)*radius r*
      normalizer (label r).1.1 (label r).1.2 (label r).2.val)*columnEnergy r) ≤
      Z^outer*(∑r : Rows,Cg*fixed*(mass r.val.1*Z^amp)*(pay0 r*Z^(allowance r)))+
        Cg*fixed*physical*F.value := by
  intro first Rows label childRoot childSrc radius nominal ownNorm pay0 payExponent outer fees
    w deleted children mass oldExponent allowance columnEnergy hC hD hmass hvolume hradius hOld hpay hmasscap
    hcolumn F
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  let localExponent := fun r : Rows => loss+amp+epsV+normCap*shellLoss+pad+slotLoss+
    actualHighCoordinates reflected (!reflected) second (first r.val.1)
      (label r).1.1 (label r).1.2 (label r).2.val Z Mrow
      (Real.logb Z (volume s)) amp xi reserve eps 0+q*((∑i∈deleted r,w i)+mesh)
  let rawEdge := fun r : Rows => Z^(Mrow+
    actualHighCoordinates reflected (!reflected) second (first r.val.1)
      (label r).1.1 (label r).1.2 (label r).2.val Z Mrow
      (Real.logb Z (volume s)) amp xi reserve eps 0+q*(∑i∈deleted r,w i)+fees r)
  have hrow : ∀r : Rows,(mass r.val.1/volume (childSrc r.val.1)*radius r*
      normalizer (label r).1.1 (label r).1.2 (label r).2.val)*columnEnergy r ≤
      Cg*fixed*(mass r.val.1*Z^amp)*(pay0 r*Z^(allowance r))+
      Cg*fixed*physical*(Z^(localExponent r)*(children r).value) := by
    intro r
    exact actual_joined_column_forest reflected second (!reflected) (first r.val.1) (label r)
      Z Mrow (Real.logb Z (volume s)) amp xi reserve eps 1 common pad loss epsV normCap
      shellLoss slotLoss q (∑i∈deleted r,w i) mesh (mass r.val.1) (volume (childSrc r.val.1))
      (radius r) Cg fixed physical (oldExponent r) (allowance r) (columnEnergy r)
      hZ (hC r) (hD r) (children r) hCg hfixed (hmass r) (hvolume r) (hradius r) hphysical
      (hOld r) (hpay r) (hmasscap r) (hcolumn r)
  have hsum := Finset.sum_le_sum (fun r (_ : r∈(Finset.univ : Finset Rows)) => hrow r)
  rw [Finset.sum_add_distrib] at hsum
  have hedge : ∀r : Rows,Z^outer*Z^(localExponent r)=rawEdge r := by
    intro r
    rw [←Real.rpow_add hZ0]
    congr 1
    dsimp only [outer,localExponent,rawEdge,fees]
    ring
  have hraw : Z^outer*(∑r : Rows,Cg*fixed*physical*(Z^(localExponent r)*(children r).value)) =
      Cg*fixed*physical*(∑r : Rows,rawEdge r*(children r).value) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    calc
      _ = Cg*fixed*physical*((Z^outer*Z^(localExponent r))*(children r).value) := by ring
      _ = _ := by rw [hedge]
  have hvalue : F.value=∑r : Rows,rawEdge r*(children r).value := by
    exact attach_native_root_low_rows_value reflected second s R seed Z Mrow amp xi reserve eps b firstHeight N
      hZ key hz1 hz2 firstIndex units w deleted q fees children
  have htail : (∑r : Rows,rawEdge r*(children r).value) ≤ F.value := by
    rw [hvalue]
  calc
    _ ≤ Z^outer*((∑r : Rows,Cg*fixed*(mass r.val.1*Z^amp)*(pay0 r*Z^(allowance r)))+
        ∑r : Rows,Cg*fixed*physical*(Z^(localExponent r)*(children r).value)) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hZ0.le _)
    _ = Z^outer*(∑r : Rows,Cg*fixed*(mass r.val.1*Z^amp)*(pay0 r*Z^(allowance r)))+
        Cg*fixed*physical*(∑r : Rows,rawEdge r*(children r).value) := by rw [mul_add,hraw]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left htail
      (mul_nonneg (mul_nonneg hCg hfixed) hphysical))

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_selected_root_low_rows_forest
