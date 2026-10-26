/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowPayment
import Candidate.Cycle63.Physical.InitialMass.SecondHighCoordinates
import Candidate.Research.RecursiveAffine.ActualFamilyRebase
import Candidate.Cycle63.Physical.InitialMass.DepthTwoReturnedCount
import Candidate.Cycle63.Physical.InitialMass.SecondLabelDisintegration

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily Cycle63Moment Cycle63InitialMass Cycle153SourceReturn
open CanonicalQuadraticSieve ActualEisensteinCubic IdealMobiusDivisorSum
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentSectorLocalization CenteredMomentEnergyState
open CenteredMomentSecondHeightFamily

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

/-- The actual continuing source carrier. Common/residual maximizing
allocations and deleted subsets are functions of these physical row keys;
they are not appended as independent counting coordinates. -/
abbrev NativeLowRows {Label : Type} [Fintype Label]
    (reflected : Bool) (s : Input alpha) (R seed : Ideal O)
    (Z Mrow amp xi reserve b firstHeight : ℝ) (N : ℕ) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ)) (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
    (firstIndex : Label → GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) :=
  ↥(mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp xi reserve b firstHeight N
    hZ key hz1 hz2 firstIndex)

/-- Attach actual selected source rows, using their literal global
multiplier and historical first missing radical. Raw AtState scales enter
the edge weights exactly once; the terminal HIGH records remain absolute.
This is the concrete row-carrier construction used by the depth induction.
The source-energy estimate and arithmetic-price certificate are separate
properties of the children, not assumptions manufactured by this definition. -/
def attach_native_low_rows
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M ≤ H}
    {Depth : Type} [Fintype Depth] {junction : Depth→ℝ} {Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}
    {OwnBase : Type} {ownBase : Character→OwnBase→Character}
    {eta : Character} {Bnorm T qOwn : ℝ} {root : O}
    {Label : Type} [Fintype Label]
    (reflected second : Bool) (s : Input alpha) (R seed : Ideal O)
    (Z Mrow amp xi reserve eps b firstHeight : ℝ) (N : ℕ) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ)) (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
    (firstIndex : Label → GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (units : FirstSourceLabel→O)
    (own : ReturnedPartAt M H hH qOwn ownBase eta Z Bnorm T root) :
    let first := fun l => geometryFirstLabel s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val
    let Rows := NativeLowRows reflected s R seed Z Mrow amp xi reserve b firstHeight N
      hZ key hz1 hz2 firstIndex
    let label := fun r : Rows => actualSecondArithmeticLabel _ _ _ _ _ _ _ r.val.2
    let childRoot := fun r : Rows =>
      childMultiplier (!reflected) root units ⟨first r.val.1,label r⟩
    ∀ (w : alpha→ℝ) (deleted : Rows→Finset alpha) (q : ℝ) (fees : Rows→ℝ),
    ((r : Rows)→DepthReturnedFamily M H hH junction Base base eta Z Bnorm T (childRoot r)) →
    DepthReturnedFamily M H hH (fun d : Option Depth=>match d with | none=>qOwn | some j=>junction j)
      (fun d : Option Depth=>match d with | none=>OwnBase | some j=>Base j)
      (fun d=>match d with | none=>ownBase | some j=>base j) eta Z Bnorm T root := by
  intro first Rows label childRoot w deleted q fees children
  let edge := fun r : Rows => Z^(Mrow+
    actualHighCoordinates reflected (!reflected) second (first r.val.1)
      (label r).1.1 (label r).1.2 (label r).2 Z Mrow
      (Real.logb Z (volume s)) amp xi reserve eps 0+
      q*(∑i∈deleted r,w i)+fees r)
  let missing := fun r : Rows => Real.logb Z ((firstSourceMissing (!reflected) (first r.val.1)).absNorm:ℝ)
  have hroot : ∀r : Rows,root∣childRoot r := by
    intro r
    refine ⟨units (first r.val.1)*
      primeSubsetGenerator (fun P : CommonIndex (first r.val.1).1.1 (first r.val.1).1.2 => P.val)
        (first r.val.1).2.val * firstSourceNumerator (!reflected) (first r.val.1)*
        (commonFrequencyGenerator (label r).1.1 (label r).1.2*
          nonunitFrequencyGenerator (label r).1.1 (label r).1.2 (label r).2), ?_⟩
    dsimp only [childRoot,childMultiplier]
    ring
  have hmissing : ∀r : Rows,0 ≤ missing r := by
    intro r
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (firstSourceMissing_ne_zero (!reflected) (first r.val.1)))
  exact DepthReturnedFamily.attach own 1 zero_le_one childRoot hroot children edge missing
    (fun _=>Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hmissing

/-- The root LOW forest contains only genuinely continuing physical
rows. Root own HIGH is paid separately. The depth carrier is exactly the
sum of the SAME child prefixes; no artificial Option/own prefix is added. -/
def attach_native_root_low_rows
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
    (units : FirstSourceLabel→O) :
    let first := fun l => geometryFirstLabel s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val
    let Rows := NativeLowRows reflected s R seed Z Mrow amp xi reserve b firstHeight N
      hZ key hz1 hz2 firstIndex
    let label := fun r : Rows => actualSecondArithmeticLabel _ _ _ _ _ _ _ r.val.2
    let childRoot := fun r : Rows =>
      childMultiplier (!reflected) root units ⟨first r.val.1,label r⟩
    ∀(w : alpha→ℝ)(deleted : Rows→Finset alpha)(q : ℝ)(fees : Rows→ℝ),
    ((r : Rows)→DepthReturnedFamily M H hH junction Base base eta Z Bnorm T (childRoot r)) →
    DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root := by
  intro first Rows label childRoot w deleted q fees children
  let edge := fun r : Rows => Z^(Mrow+
    actualHighCoordinates reflected (!reflected) second (first r.val.1)
      (label r).1.1 (label r).1.2 (label r).2 Z Mrow
      (Real.logb Z (volume s)) amp xi reserve eps 0+
      q*(∑i∈deleted r,w i)+fees r)
  let missing := fun r : Rows=>Real.logb Z ((firstSourceMissing (!reflected) (first r.val.1)).absNorm:ℝ)
  have hroot : ∀r : Rows,root∣childRoot r := by
    intro r
    refine ⟨units (first r.val.1)*
      primeSubsetGenerator (fun P : CommonIndex (first r.val.1).1.1 (first r.val.1).1.2=>P.val)
        (first r.val.1).2.val*firstSourceNumerator (!reflected) (first r.val.1)*
        (commonFrequencyGenerator (label r).1.1 (label r).1.2*
          nonunitFrequencyGenerator (label r).1.1 (label r).1.2 (label r).2),?_⟩
    dsimp only [childRoot,childMultiplier]
    ring
  have hmissing : ∀r : Rows,0 ≤ missing r := by
    intro r
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (firstSourceMissing_ne_zero (!reflected) (first r.val.1)))
  exact {
    Prefix := fun d=>Σr : Rows,(children r).Prefix d
    prefixFintype := fun _=>inferInstance
    multiplier := fun d p=>(children p.1).multiplier d p.2
    root_divides := fun d p=>(hroot p.1).trans ((children p.1).root_divides d p.2)
    historyMissing := fun d p=>missing p.1+(children p.1).historyMissing d p.2
    historyMissing_nonneg := fun d p=>add_nonneg (hmissing p.1) ((children p.1).historyMissing_nonneg d p.2)
    part := fun d p=>(children p.1).part d p.2
    weight := fun d p=>edge p.1*(children p.1).weight d p.2
    weight_nonneg := fun d p=>mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      ((children p.1).weight_nonneg d p.2) }

set_option maxHeartbeats 650000 in
theorem attach_native_root_low_rows_value
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
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)(units : FirstSourceLabel→O) :
    let first := fun l=>geometryFirstLabel s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val
    let Rows := NativeLowRows reflected s R seed Z Mrow amp xi reserve b firstHeight N hZ key hz1 hz2 firstIndex
    let label := fun r : Rows=>actualSecondArithmeticLabel _ _ _ _ _ _ _ r.val.2
    let childRoot := fun r : Rows=>childMultiplier (!reflected) root units ⟨first r.val.1,label r⟩
    ∀(w : alpha→ℝ)(deleted : Rows→Finset alpha)(q : ℝ)(fees : Rows→ℝ)
      (children : (r : Rows)→DepthReturnedFamily M H hH junction Base base eta Z Bnorm T (childRoot r)),
    (attach_native_root_low_rows reflected second s R seed Z Mrow amp xi reserve eps b firstHeight N hZ
      key hz1 hz2 firstIndex units w deleted q fees children).value=
      ∑r : Rows,Z^(Mrow+actualHighCoordinates reflected (!reflected) second (first r.val.1)
        (label r).1.1 (label r).1.2 (label r).2 Z Mrow (Real.logb Z (volume s)) amp xi reserve eps 0+
          q*(∑i∈deleted r,w i)+fees r)*(children r).value := by
  intro first Rows label childRoot w deleted q fees children
  unfold DepthReturnedFamily.value attach_native_root_low_rows
  simp only [Fintype.sum_sigma]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  dsimp only [first,label]
  ring

/-- Exact actual own-HIGH plus continuing LOW return identity. -/
theorem attach_native_low_rows_value
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M ≤ H}
    {Depth : Type} [Fintype Depth] {junction : Depth→ℝ} {Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}
    {OwnBase : Type} {ownBase : Character→OwnBase→Character}
    {eta : Character} {Bnorm T qOwn : ℝ} {root : O}
    {Label : Type} [Fintype Label]
    (reflected second : Bool) (s : Input alpha) (R seed : Ideal O)
    (Z Mrow amp xi reserve eps b firstHeight : ℝ) (N : ℕ) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ)) (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
    (firstIndex : Label → GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (units : FirstSourceLabel→O)
    (own : ReturnedPartAt M H hH qOwn ownBase eta Z Bnorm T root) :
    let first := fun l => geometryFirstLabel s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val
    let Rows := NativeLowRows reflected s R seed Z Mrow amp xi reserve b firstHeight N
      hZ key hz1 hz2 firstIndex
    let label := fun r : Rows => actualSecondArithmeticLabel _ _ _ _ _ _ _ r.val.2
    let childRoot := fun r : Rows =>
      childMultiplier (!reflected) root units ⟨first r.val.1,label r⟩
    ∀ (w : alpha→ℝ) (deleted : Rows→Finset alpha) (q : ℝ) (fees : Rows→ℝ),
    ∀ children : ((r : Rows)→DepthReturnedFamily M H hH junction Base base eta Z Bnorm T (childRoot r)),
    (attach_native_low_rows reflected second s R seed Z Mrow amp xi reserve eps b firstHeight N
      hZ key hz1 hz2 firstIndex units own w deleted q fees children).value =
      own.value + ∑r : Rows,
        Z^(Mrow+actualHighCoordinates reflected (!reflected) second (first r.val.1)
          (label r).1.1 (label r).1.2 (label r).2 Z Mrow
          (Real.logb Z (volume s)) amp xi reserve eps 0+q*(∑i∈deleted r,w i)+fees r)*
          (children r).value := by
  intro first Rows label childRoot w deleted q fees children
  dsimp only [attach_native_low_rows]
  rw [DepthReturnedFamily.value_attach]
  simp only [one_mul]
  rfl

/-- A deliberately coarse uniform envelope for a literal raw source edge.
The native source box, actual surviving original slots and fixed fee cap
suffice; the sharp endpoint certificate is not used. This is the input to
the whole-source forest's rough supremum bound. -/
theorem native_low_raw_edge_coarse
    (reflected second : Bool) (first : FirstSourceLabel)
    (C2 D2 : Ideal O) (inactive : Finset (CommonIndex C2 D2))
    (Z Mrow A amp xi reserve eps q fee : ℝ) (hZ : 1<Z)
    (w : alpha→ℝ) (deleted : Finset alpha)
    (hMrow : Mrow ≤ 1)
    (hbox : |actualHighCoordinates reflected (!reflected) second first C2 D2 inactive
      Z Mrow A amp xi reserve eps 0| ≤ 149)
    (hw : ∀i,0 ≤ w i) (hslots : (∑i,w i) ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hfee : fee ≤ 1) :
    Z^(Mrow+actualHighCoordinates reflected (!reflected) second first C2 D2 inactive
      Z Mrow A amp xi reserve eps 0+q*(∑i∈deleted,w i)+fee) ≤ Z^(152:ℝ) := by
  have hd0 : 0 ≤ ∑i∈deleted,w i := Finset.sum_nonneg (fun i _=>hw i)
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ deleted)
    (fun i _ _=>hw i)
  change (∑i∈deleted,w i) ≤ (∑i,w i) at hsub
  have hd1 : (∑i∈deleted,w i) ≤ 1 := hsub.trans hslots
  have hpay := mul_le_mul_of_nonneg_right hq1 hd0
  have hx := (abs_le.mp hbox).2
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  nlinarith only [hMrow,hpay,hd1,hfee,hx]

/-- The literal attached forest has a uniform coarse path-weight bound.
The induction hypothesis concerns only already constructed daughter
forests; the current edge is bounded from the actual native coordinate
box and original slots. In particular, intermediate raw row scales are
retained in the product rather than silently normalized away. -/
theorem native_attached_low_weight_bound
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M ≤ H}
    {Depth : Type} [Fintype Depth] {junction : Depth→ℝ} {Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}
    {OwnBase : Type} {ownBase : Character→OwnBase→Character}
    {eta : Character} {Bnorm T qOwn : ℝ} {root : O}
    {Label : Type} [Fintype Label]
    (reflected second : Bool) (s : Input alpha) (R seed : Ideal O)
    (Z Mrow amp xi reserve eps b firstHeight : ℝ) (N : ℕ) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ)) (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
    (firstIndex : Label → GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (units : FirstSourceLabel→O)
    (own : ReturnedPartAt M H hH qOwn ownBase eta Z Bnorm T root) :
    let first := fun l => geometryFirstLabel s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val
    let Rows := NativeLowRows reflected s R seed Z Mrow amp xi reserve b firstHeight N
      hZ key hz1 hz2 firstIndex
    let label := fun r : Rows => actualSecondArithmeticLabel _ _ _ _ _ _ _ r.val.2
    let childRoot := fun r : Rows =>
      childMultiplier (!reflected) root units ⟨first r.val.1,label r⟩
    ∀ (w : alpha→ℝ) (deleted : Rows→Finset alpha) (q : ℝ) (fees : Rows→ℝ),
    ∀ children : ((r : Rows)→DepthReturnedFamily M H hH junction Base base eta Z Bnorm T (childRoot r)),
    ∀ cap : Depth→ℝ,
    Mrow ≤ 1 → (∀i,0 ≤ w i) → (∑i,w i) ≤ 1 → 0 ≤ q → q ≤ 1 →
    (∀r,fees r ≤ 1) →
    (∀r,|actualHighCoordinates reflected (!reflected) second (first r.val.1)
      (label r).1.1 (label r).1.2 (label r).2 Z Mrow
      (Real.logb Z (volume s)) amp xi reserve eps 0| ≤ 149) →
    (∀r d p,(children r).weight d p ≤ Z^(cap d)) →
    let F := attach_native_low_rows reflected second s R seed Z Mrow amp xi reserve eps b firstHeight N
      hZ key hz1 hz2 firstIndex units own w deleted q fees children
    ∀(d : Option Depth)(p : F.Prefix d),F.weight d p ≤
      Real.rpow Z (Option.rec (motive := fun _ : Option Depth => ℝ) 0 (fun j=>152+cap j) d) := by
  intro first Rows label childRoot w deleted q fees children cap hMrow hw hslots hq0 hq1 hfees hbox hchildren F d p
  cases d with
  | none =>
    change (1:ℝ) ≤ Z^(0:ℝ)
    simp only [Real.rpow_zero,le_refl]
  | some j =>
    change Z^(Mrow+actualHighCoordinates reflected (!reflected) second (first p.1.val.1)
      (label p.1).1.1 (label p.1).1.2 (label p.1).2 Z Mrow
      (Real.logb Z (volume s)) amp xi reserve eps 0+
      q*(∑i∈deleted p.1,w i)+fees p.1)*(children p.1).weight j p.2 ≤ Z^(152+cap j)
    rw [Real.rpow_add (zero_lt_one.trans hZ) 152 (cap j)]
    apply mul_le_mul
      (native_low_raw_edge_coarse reflected second (first p.1.val.1) (label p.1).1.1
        (label p.1).1.2 (label p.1).2 Z Mrow (Real.logb Z (volume s)) amp xi reserve eps q
        (fees p.1) hZ w (deleted p.1) hMrow (hbox p.1) hw hslots hq0 hq1 (hfees p.1))
      (hchildren p.1 j p.2) ((children p.1).weight_nonneg j p.2)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)

/-- A coarse bound for the LITERAL raw edge after native source-side
cancellation. The first mass loss need not be small: it is included in
the shifted outside coordinate, and subtracted from the remaining fee.
The original unshifted edge is kept unchanged in the forest. -/
theorem native_low_raw_edge_shifted_coarse
    (reflected second : Bool) (first : FirstSourceLabel)
    (C2 D2 : Ideal O) (inactive : Finset (CommonIndex C2 D2))
    (Z Mrow A amp xi reserve eps q fee massLoss : ℝ) (hZ : 1<Z)
    (w : alpha→ℝ) (deleted : Finset alpha)
    (hMrow : Mrow ≤ 1)
    (hshift : actualHighCoordinates reflected (!reflected) second first C2 D2 inactive
      Z Mrow A amp xi reserve eps 0+massLoss ≤ 200)
    (hw : ∀i,0 ≤ w i) (hslots : (∑i,w i) ≤ 1)
    (hq1 : q ≤ 1) (hfee : fee-massLoss ≤ 1) :
    Z^(Mrow+actualHighCoordinates reflected (!reflected) second first C2 D2 inactive
      Z Mrow A amp xi reserve eps 0+q*(∑i∈deleted,w i)+fee) ≤ Z^(204:ℝ) := by
  have hd0 : 0 ≤ ∑i∈deleted,w i := Finset.sum_nonneg (fun i _=>hw i)
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ deleted)
    (fun i _ _=>hw i)
  change (∑i∈deleted,w i) ≤ (∑i,w i) at hsub
  have hd1 : (∑i∈deleted,w i) ≤ 1 := hsub.trans hslots
  have hpay := mul_le_mul_of_nonneg_right hq1 hd0
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith only [hMrow,hshift,hd1,hpay,hfee]

/-- Uniform path weights for the actual attached source forest, using the
source-proved shifted coordinate rather than an unlicensed small raw
mass loss. Native missing radicals, multipliers, and actual records are
unchanged. At four continuing LOW edges this gives the rough exponent
816 used only for the source-wide supremum, not the sharp record price. -/
theorem native_attached_low_shifted_weight_bound
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M ≤ H}
    {Depth : Type} [Fintype Depth] {junction : Depth→ℝ} {Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}
    {OwnBase : Type} {ownBase : Character→OwnBase→Character}
    {eta : Character} {Bnorm T qOwn : ℝ} {root : O}
    {Label : Type} [Fintype Label]
    (reflected second : Bool) (s : Input alpha) (R seed : Ideal O)
    (Z Mrow amp xi reserve eps b firstHeight : ℝ) (N : ℕ) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ)) (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
    (firstIndex : Label → GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (units : FirstSourceLabel→O)
    (own : ReturnedPartAt M H hH qOwn ownBase eta Z Bnorm T root) :
    let first := fun l => geometryFirstLabel s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val
    let Rows := NativeLowRows reflected s R seed Z Mrow amp xi reserve b firstHeight N
      hZ key hz1 hz2 firstIndex
    let label := fun r : Rows => actualSecondArithmeticLabel _ _ _ _ _ _ _ r.val.2
    let childRoot := fun r : Rows =>
      childMultiplier (!reflected) root units ⟨first r.val.1,label r⟩
    ∀ (w : alpha→ℝ) (deleted : Rows→Finset alpha) (q : ℝ) (fees massLoss : Rows→ℝ),
    ∀ children : ((r : Rows)→DepthReturnedFamily M H hH junction Base base eta Z Bnorm T (childRoot r)),
    ∀ cap : Depth→ℝ,
    Mrow ≤ 1 → (∀i,0 ≤ w i) → (∑i,w i) ≤ 1 → q ≤ 1 →
    (∀r : Rows,fees r-massLoss r ≤ 1) →
    (∀r : Rows,actualHighCoordinates reflected (!reflected) second (first r.val.1)
      (label r).1.1 (label r).1.2 (label r).2 Z Mrow
      (Real.logb Z (volume s)) amp xi reserve eps 0+massLoss r ≤ 200) →
    (∀r d p,(children r).weight d p ≤ Z^(cap d)) →
    let F := attach_native_low_rows reflected second s R seed Z Mrow amp xi reserve eps b firstHeight N
      hZ key hz1 hz2 firstIndex units own w deleted q fees children
    ∀(d : Option Depth)(p : F.Prefix d),F.weight d p ≤
      Real.rpow Z (Option.rec (motive := fun _ : Option Depth => ℝ) 0 (fun j=>204+cap j) d) := by
  intro first Rows label childRoot w deleted q fees massLoss children cap hMrow hw hslots hq1 hfees hshift
    hchildren F d p
  cases d with
  | none =>
    change (1:ℝ) ≤ Z^(0:ℝ)
    simp only [Real.rpow_zero,le_refl]
  | some j =>
    change Z^(Mrow+actualHighCoordinates reflected (!reflected) second (first p.1.val.1)
      (label p.1).1.1 (label p.1).1.2 (label p.1).2 Z Mrow
      (Real.logb Z (volume s)) amp xi reserve eps 0+
      q*(∑i∈deleted p.1,w i)+fees p.1)*(children p.1).weight j p.2 ≤ Z^(204+cap j)
    rw [Real.rpow_add (zero_lt_one.trans hZ) 204 (cap j)]
    apply mul_le_mul
      (native_low_raw_edge_shifted_coarse reflected second (first p.1.val.1) (label p.1).1.1
        (label p.1).1.2 (label p.1).2 Z Mrow (Real.logb Z (volume s)) amp xi reserve eps q
        (fees p.1) (massLoss p.1) hZ w (deleted p.1) hMrow (hshift p.1) hw hslots hq1 (hfees p.1))
      (hchildren p.1 j p.2) ((children p.1).weight_nonneg j p.2)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.attach_native_low_rows_value
#print axioms OAI.SevenEighths.Cycle153RegionalLow.attach_native_root_low_rows_value

#print axioms OAI.SevenEighths.Cycle153RegionalLow.native_low_raw_edge_coarse

#print axioms OAI.SevenEighths.Cycle153RegionalLow.native_attached_low_weight_bound

#print axioms OAI.SevenEighths.Cycle153RegionalLow.native_low_raw_edge_shifted_coarse
#print axioms OAI.SevenEighths.Cycle153RegionalLow.native_attached_low_shifted_weight_bound
