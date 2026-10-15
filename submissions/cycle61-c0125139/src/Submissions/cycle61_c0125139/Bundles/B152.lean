/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B099
import Submissions.cycle61_c0125139.Bundles.B107
import Submissions.cycle61_c0125139.Bundles.B114
import Submissions.cycle61_c0125139.Bundles.B151

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryZeroPartition; sha256 171b5c12b0c57486f73177735e39a12213f4f715e6e9ee13498c808904949921 -/
section
                                        
                                       

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter Set HeckeFamily HeckeDetectorZeros LocalMoment
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open ConcreteTraceCRT Cycle61Moment Cycle61Moment.LowBranch
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The actual whole family includes the plain character and all relative rays. -/
def geometryRowFamily {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ)
    (η₀ : Character) (z : O) (hz : st.radial.keep z) : WholeSourceIndex M H→ Character :=
  wholeSourceFamily M H hH η₀
    (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture)

theorem geometry_row_family_nonprincipal {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ)
    (η₀ : Character) (hQM : st.fixedModulus≤ M) (hQη : st.fixedModulus≤η₀.modulus)
    (z : O) (hz : st.radial.keep z) :
    ∀j,(geometryRowFamily M H hH st η₀ z hz j).residue≠1 :=
  whole_source_family_nonprincipal M H hH st η₀ hQM hQη z hz
    (naturalRow st.character z (st.row_ne_zero z hz))

def geometryRowMaximum {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ)
    (η₀ : Character) (hQM : st.fixedModulus≤ M) (hQη : st.fixedModulus≤η₀.modulus)
    (z : O) (hz : st.radial.keep z) (T : ℝ) : ℝ :=
  zeroMaximum (geometryRowFamily M H hH st η₀ z hz)
    (geometry_row_family_nonprincipal M H hH st η₀ hQM hQη z hz) T

/-- Literal bin admission includes the zero-profile branch of the full row set. -/
def GeometryZeroBin {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ)
    (η₀ : Character) (hQM : st.fixedModulus≤ M) (hQη : st.fixedModulus≤η₀.modulus)
    (z : O) (hz : st.radial.keep z) (e T : ℝ) (p : BufferIndex e) : Prop :=
    1≤ p.1.val ∧ p.1.val≤ bufferCount e ∧
      let β:=bufferValue e p
      51/100≤β ∧ β≤7/8 ∧
      β≤ geometryRowMaximum M H hH st η₀ hQM hQη z hz ((3*p.1.val:ℕ)*T) ∧
      geometryRowMaximum M H hH st η₀ hQM hQη z hz ((3*p.1.val:ℕ)*T)<β+e ∧
      β≤ geometryRowMaximum M H hH st η₀ hQM hQη z hz (3*(p.1.val+1:ℕ)*T) ∧
      geometryRowMaximum M H hH st η₀ hQM hQη z hz (3*(p.1.val+1:ℕ)*T)<β+2*e ∧
      (β<21/25 → ∀_hs : st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)≠0,
        ActualLow M H hH st η₀ hQM hQη (21/25) e (3*(p.1.val+1:ℕ)*T) z) ∧
      (st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)=0 ∨
        ActualLow M H hH st η₀ hQM hQη (21/25) e (3*(p.1.val+1:ℕ)*T) z ∨ 21/25≤β)

/-- Every retained nonexceptional row has an actual buffered bin. Radial
zero terms remain explicit; all supported low rows enter ActualLow. -/
theorem actual_geometry_zero_partition {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ)
    (η₀ : Character) (hQM : st.fixedModulus≤ M) (hQη : st.fixedModulus≤η₀.modulus)
    (z : O) (hz : st.radial.keep z) (e T : ℝ) (he : 0< e) (hT : 2< T)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
    ∃p : BufferIndex e,GeometryZeroBin M H hH st η₀ hQM hQη z hz e T p := by
  let χ:=geometryRowFamily M H hH st η₀ z hz
  let hn:=geometry_row_family_nonprincipal M H hH st η₀ hQM hQη z hz
  obtain ⟨i,k,hi,hin,hone,hcurrent,hround,hnext,_⟩ :=
    exists_actual_buffered_bin χ hn T e hT he (bufferCount e)
      (bufferCount_spec e he).1 (bufferCount_spec e he).2
  have hk : k≤ bufferGridCount e := by
    have hkr : (k:ℝ)≤1/e := (le_div_iff₀ he).mpr (by nlinarith)
    exact_mod_cast hkr.trans (Nat.le_ceil (1/e))
  let p : BufferIndex e := (⟨i,by omega⟩,⟨k,by omega⟩)
  have hβ : bufferValue e p≤7/8 :=
    hcurrent.trans ((zeroMaximum_le_beta χ hn hβlo _).trans hβhi)
  have hmon : zeroMaximum χ hn ((3*i:ℕ)*T)≤ zeroMaximum χ hn (3*(i+1:ℕ)*T) := by
    apply zeroMaximum_mono
    push_cast
    nlinarith
  have hlow (hb : bufferValue e p<21/25)
      (hs : st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)≠0) :
      ActualLow M H hH st η₀ hQM hQη (21/25) e (3*(p.1.val+1:ℕ)*T) z := by
    apply whole_source_upper_actual_low M H hH st η₀ hQM hQη z hz _ _ _ hs
    change zeroMaximum χ hn (3*(i+1:ℕ)*T)<21/25+2*e
    dsimp [bufferValue,p] at hb
    linarith
  refine ⟨p,hi,hin,?_,hβ,?_,?_,?_,?_,hlow,?_⟩
  · dsimp [bufferValue,p]; nlinarith [Nat.cast_nonneg (α:=ℝ) k]
  · simpa only [geometryRowMaximum,bufferValue,p,Nat.cast_mul,Nat.cast_ofNat] using hcurrent
  · simpa only [geometryRowMaximum,bufferValue,p,Nat.cast_mul,Nat.cast_ofNat] using hround
  · have hm := hmon
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hm
    exact hcurrent.trans hm
  · exact hnext
  · by_cases hs : st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)=0
    · exact Or.inl hs
    · rcases lt_or_ge (bufferValue e p) (21/25:ℝ) with hb|hb
      · exact Or.inr (Or.inl (hlow hb hs))
      · exact Or.inr (Or.inr hb)

section Family
variable {κ : Type*} (rows : Finset κ)
variable {Z Bmask bΦ : ℝ} (st : rows→ NaturalState Z Bmask bΦ) (η₀ : Character)
variable (hQM : ∀u,(st u).fixedModulus≤ M) (hQη : ∀u,(st u).fixedModulus≤η₀.modulus)
variable (z : rows→ O) (hz : ∀u,(st u).radial.keep (z u))
variable (e T : ℝ) (he : 0< e) (hT : 2< T)
variable (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)

/-- One actual choice retains the complete finite physical row coordinate. -/
def geometryZeroSelector : rows→ BufferIndex e := fun u=>Classical.choose
  (actual_geometry_zero_partition M H hH (st u) η₀ (hQM u) (hQη u) (z u) (hz u) e T he hT hβlo hβhi)

theorem geometry_zero_selector_spec : ∀u,
    GeometryZeroBin M H hH (st u) η₀ (hQM u) (hQη u) (z u) (hz u) e T
      (geometryZeroSelector M H hH rows st η₀ hQM hQη z hz e T he hT hβlo hβhi u) :=
  fun u=>Classical.choose_spec
    (actual_geometry_zero_partition M H hH (st u) η₀ (hQM u) (hQη u) (z u) (hz u) e T he hT hβlo hβhi)
end Family

/-- A finite family retains every original label in its selected zero bins. -/
theorem geometry_zero_fiber_reassembly {κ : Type*}
    (rows : Finset κ) (e : ℝ) (select : rows→ BufferIndex e) (weight : rows→ℝ) :
    (∑u : rows,weight u)=∑p : BufferIndex e,
      ∑u∈rows.attach.filter (fun u=>select u=p),weight u := by
  simpa only [Finset.attach_eq_univ] using
    (Finset.sum_fiberwise_of_maps_to (s:=rows.attach) (t:=Finset.univ)
      (fun (u : rows) (_ : u∈rows.attach)=>
        (show select u∈Finset.univ from Finset.mem_univ _)) weight).symm

/-- The strict low cut and the inclusive high cut cover the entire grid. -/
theorem geometry_zero_low_high_reassembly (e : ℝ) (weight : BufferIndex e→ℝ) :
    (∑p,weight p)=
      (∑p∈Finset.univ.filter (fun p=>bufferValue e p<21/25),weight p)+
      (∑p∈Finset.univ.filter (fun p=>21/25≤ bufferValue e p),weight p) := by
  simpa only [not_lt] using
    (Finset.sum_filter_add_sum_filter_not (s:=Finset.univ)
      (p:=fun p=>bufferValue e p<21/25) (f:=weight)).symm

/-- Small outer heights satisfy both column gates in every selected bin. -/
theorem geometry_small_outer_height (T t height : ℝ) (i : ℕ) (freq : ℝ)
    (hT : 0≤ T) (hh : 0≤ height) (hsmall : |t|+height≤ T) (hf : |freq|≤ height) :
    |t+freq|+T/2≤(3*i+2:ℕ)*T ∧ |t|+T/2≤(3*i+2:ℕ)*T := by
  have habs:=abs_add_le t freq
  have hn : (0:ℝ)≤(i:ℝ) := Nat.cast_nonneg _
  push_cast
  constructor <;> nlinarith [mul_nonneg hn hT]

/-- Separate small base bounds also pay the combined low gate. -/
theorem geometry_small_base_height (T t height : ℝ) (i : ℕ) (freq : ℝ)
    (hT : 0≤ T) (hi : 1 ≤ i)
    (ht : |t|≤ T) (hheight : height≤ T) (hf : |freq|≤ height) :
    |t|+height+T/2≤(3*i+2:ℕ)*T ∧
    |t+freq|+T/2≤(3*i+2:ℕ)*T ∧ |t|+T/2≤(3*i+2:ℕ)*T := by
  have hiR : (1:ℝ)≤(i:ℝ) := by exact_mod_cast hi
  have habs:=abs_add_le t freq
  have hmul:=mul_le_mul_of_nonneg_right hiR hT
  push_cast
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The fixed buffered index set fits the analytic truncated height range
at a threshold chosen before every moving natural state and row. -/
theorem eventually_geometry_zero_heights (e τ : ℝ) (hτ : 0<τ) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ 2< Z^τ ∧
      ∀p : BufferIndex e,(p.1.val:ℝ)≤ Z^τ := by
  filter_upwards [(tendsto_rpow_atTop hτ).eventually
      (eventually_gt_atTop (max (2:ℝ) (bufferCount e:ℝ))),eventually_gt_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,(lt_of_le_of_lt (le_max_left _ _) hz),?_⟩
  intro p
  have hp : p.1.val≤ bufferCount e := by omega
  exact (by exact_mod_cast hp : (p.1.val:ℝ)≤ bufferCount e).trans
    (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hz))

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryRowFamily
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_row_family_nonprincipal
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryRowMaximum
#print axioms OAI.SevenEighths.Cycle61InitialMass.GeometryZeroBin
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_zero_partition
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryZeroSelector
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_zero_selector_spec
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_zero_fiber_reassembly
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_zero_low_high_reassembly
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_small_outer_height
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_small_base_height
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventually_geometry_zero_heights

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryZeroPartition -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainBudget; sha256 4015382ea4959f0ce4f7fc3a030f61e66ef365113b54f9de20da1827f90faecf -/
section
                                                     
                                                         
                                                      

set_option autoImplicit false
set_option maxHeartbeats 250000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle61Moment CenteredMomentLogDyadic CenteredMomentCommonPairedSource
open CenteredMomentRankinRadical CenteredMomentSecondCanonicalScalar
open HeckeDetectorZeros LocalMoment
open Cycle61FinalLow
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle61FinalProfiles
local notation "O" => HeckeFamily.O
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]
local instance geometryMainBudgetSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _
attribute [local irreducible] geometryLowActualChain geometryLowActualGeometry geometryLowSecondDatum


variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Complete low columns on literal first and second source coordinates.
The selected second common allocation is fixed before the retained row sum. -/
def actual_geometry_main_low_columns
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) :=
  let hbase := actual_geometry_low_family_columns.{u,v} (α:=α) M H hH
    W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell
  let degree := Classical.choose hbase
  let hdegree := Classical.choose_spec hbase
  let Sp := Classical.choose hdegree
  let hcolumn := Classical.choose_spec hdegree
  (degree,Sp,fun η₀ Q hQM hQ0 hQt hQ72=>
    let hc := hcolumn η₀ Q hQM hQ0 hQt hQ72
    let Cg := Classical.choose hc
    let hg := Classical.choose_spec hc
    (Cg,PLift.up (And.intro hg.1 (Filter.Eventually.mono hg.2 (fun Z hz=>
      And.intro hz.1
      (fun (hZ : 1< Z) (s : Input α) (θ : α→ RayQuotient.Characters M H)
        (w σ freq : α→ℝ) (heightV height mesh aLow : ℝ) (i : ℕ)
        hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
        hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh (Mrow reserve ξ : ℝ) hMmin hω hξ hMcap'
        hzslot haff (reflected : Bool) (R seed : Ideal O) (bin : ℤ×(Fin 5→ℤ))
        (t Mprice Aprice : ℝ)
        (sourceWeight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
        {Label : Type v} [Fintype Label] [DecidableEq Label]
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)=>
        let cell := Cycle61.Arithmetic.cellUpper
          (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
        let amp := Mrow*Cycle61.Arithmetic.amp cell
        fun (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
        (n : (l : Label)→ GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l))=>
        let datum := fun l=>geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l) hw₁ hw₂ (n l)
        let firstChild := fun l=>geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
        fun (second : Label→ Bool)
          (B₂ : (l : Label)→ actualAllocations (firstChild l).pools
            (if second l then (datum l).D else (datum l).C))
          (r : (l : Label)→ secondLiveRows (fun _:Unit=>(datum l).block))
          (hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
            (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            R s.ν s.W s.P≠0)
          (hf₂ : ∀l,frozenCoefficient (B₂ l).val
            (if second l then (datum l).D else (datum l).C) (datum l).R
            (firstChild l).ν (firstChild l).W (firstChild l).P≠0)=>
        let q : Label→ Chain s := fun l=>geometryLowActualChain reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l) hw₁ hw₂ (n l) (second l) (B₂ l)
        let g : (l : Label)→ LiveMainGeometry s (q l) Z Mrow amp
          (frequencyLoss Z 32 ξ+reserve) ξ bs (Fintype.card α) := fun l=>geometryLowActualGeometry reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l) hw₁ hw₂ (n l) (second l) (B₂ l) (r l) (hf₁ l) (hf₂ l)
        let hfields := fun l=>actual_geometry_low_admission_fields reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l) hw₁ hw₂ (n l) (second l) (B₂ l) (r l) (hf₁ l) (hf₂ l)
        hz.2 hZ s θ w σ freq heightV height mesh aLow i hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
          hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow (frequencyLoss Z 32 ξ+reserve) ξ
          hMmin hω hξ hMcap' hzslot haff reflected R seed bin t Mprice Aprice sourceWeight firstIndex q
          (fun l=>(hfields l).1) (fun l=>(hfields l).2.1) (fun l=>(hfields l).2.2.1)
          (fun l=>(hfields l).2.2.2.1) (fun l=>(hfields l).2.2.2.2.1) g
          (fun l=>(hfields l).2.2.2.2.2.2.1)
          (fun l=>(hfields l).2.2.2.2.2.2.2.1)
          (fun l=>(hfields l).2.2.2.2.2.2.2.2.1)))))))


/-- The genuine detector supplies the low gate on every nonzero radial term
in a selected low bin. -/
theorem actual_geometry_main_low_fiber_admission {κ : Type*}
    (rows : Finset κ) {Z Bmask bΦ : ℝ} (st : rows→ NaturalState Z Bmask bΦ)
    (η₀ : Character) (hQM : ∀u,(st u).fixedModulus≤ M)
    (hQη : ∀u,(st u).fixedModulus≤η₀.modulus)
    (z : rows→ O) (hz : ∀u,(st u).radial.keep (z u))
    (e T : ℝ) (he : 0< e) (hT : 2< T)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (p : BufferIndex e) (hp : bufferValue e p<21/25) :
    ∀u∈rows.attach.filter (fun u=>
      geometryZeroSelector M H hH rows st η₀ hQM hQη z hz e T he hT hβlo hβhi u=p ∧
      (st u).radial.profile (‖eisEmbedding (z u)‖^2/(st u).radial.scale)≠0),
      (st u).radial.keep (z u) ∧
        ActualLow M H hH (st u) η₀ (hQM u) (hQη u)
          (21/25) e (3*(p.1.val+1:ℕ)*T) (z u) := by
  intro u hu
  obtain ⟨_,hu⟩ := Finset.mem_filter.mp hu
  have h := geometry_zero_selector_spec M H hH rows st η₀ hQM hQη z hz e T he hT hβlo hβhi u
  rw [hu.1] at h
  obtain ⟨_,_,_,_,_,_,_,_,hlow,_⟩ := h
  exact ⟨hz u,hlow hp hu.2⟩

/-- Removing radial zero terms preserves every weighted source coordinate;
no estimate or label cardinality is used. -/
theorem actual_geometry_main_low_fiber_zero_terms {κ : Type*}
    (rows : Finset κ) {Z Bmask bΦ : ℝ} (st : rows→ NaturalState Z Bmask bΦ)
    (z : rows→ O) (e : ℝ) (select : rows→ BufferIndex e) (p : BufferIndex e)
    (weight cost : rows→ℝ) (hw : ∀u,0≤ weight u)
    (hmajorant : ∀u,weight u≤
      ((st u).radial.profile (‖eisEmbedding (z u)‖^2/(st u).radial.scale)).re) :
    (∑u∈rows.attach.filter (fun u=>select u=p),weight u*cost u)=
      ∑u∈rows.attach.filter (fun u=>select u=p ∧
        (st u).radial.profile (‖eisEmbedding (z u)‖^2/(st u).radial.scale)≠0),
        weight u*cost u := by
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hs : select u=p
  · by_cases hzero : (st u).radial.profile (‖eisEmbedding (z u)‖^2/(st u).radial.scale)=0
    · have hm := hmajorant u
      rw [hzero] at hm
      have hwzero : weight u=0 := le_antisymm (by simpa using hm) (hw u)
      simp [hs,hzero,hwzero]
    · simp [hs,hzero]
  · simp [hs]

/-- Scalar payment only asks for allocations on the actual finite supported labels. -/
theorem eventual_actual_geometry_low_supported_payment (N : ℕ) (lo εv B ε : ℝ)
    (hlo : 0< lo) (hev : 0<εv) (hB : 0≤ B) (hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ∀{ι : Type}[Fintype ι](s : Input ι),Fintype.card ι≤ N → lo≤ s.lower →
      ∀(reflected second : Bool)(T p exponent error εcommon M a ξ reserve : ℝ),
      0≤εcommon → 1≤ T → p≤ B → ∀seed : Ideal O,Squarefree seed → seed≠0 →
      ∀labels : Finset FirstSourceLabel,
      (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
      (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
      (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
      (∀l∈labels,(l.1.1.absNorm:ℝ)≤ Z^B ∧ (l.1.2.absNorm:ℝ)≤ Z^B) →
      (∀l∈labels,((commonRadical l.1.1 l.1.2).absNorm:ℝ)≤ Z^p) →
      (∀l∈labels,lowGeometryExponent reflected Z (Real.logb Z (volume s)) l≤ exponent) →
      ∀(Ds : FirstSourceLabel→ Finset (Ideal O))
        (children : FirstSourceLabel→ Ideal O→ Finset FirstSourceLabel),
      (∀l∈labels,∀D∈Ds l,Squarefree D) →
      (∀l∈labels,∀D∈Ds l,T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,Supported v.1.1 ∧ Supported v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,primeSupport v.1.1=primeSupport v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,D∣v.1.1 ∧ D∣v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,(v.1.1.absNorm:ℝ)≤ Z^B ∧ (v.1.2.absNorm:ℝ)≤ Z^B) →
      ∀Rfirst : Ideal O,
      ∀alloc : (l : labels)→(D : Ds l.val)→(v : children l.val D.val)→
        actualAllocations s.pools (if reflected then l.val.1.2 else l.val.1.1),
      ∀(χ : (l : labels)→(D : Ds l.val)→ children l.val D.val→ Character)
        (t : (l : labels)→(D : Ds l.val)→ children l.val D.val→ℝ),
      (∀(l : labels)(D : Ds l.val)(v : children l.val D.val),
        frozenCoefficient (alloc l D v).val (if reflected then l.val.1.2 else l.val.1.1)
          Rfirst s.ν s.W s.P≠0) →
      (∑l : labels,∑D : Ds l.val,∑v : children l.val D.val,
        Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l.val/
          volume (child s (if reflected then l.val.1.2 else l.val.1.1) Rfirst
            (alloc l D v) (χ l D v) (t l D v)))*
          (normalizer v.val.1.1 v.val.1.2 v.val.2.val*
            ((if second then v.val.1.2 else v.val.1.1).absNorm:ℝ)^(εcommon-1))*
          Z^(Cycle61FinalCapacity.secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
            (if reflected then l.val.1.2 else l.val.1.1) (if reflected then l.val.1.1 else l.val.1.2)
            v.val.1.1 v.val.1.2 v.val.2.val+a+error))≤
        K*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed.absNorm:ℝ) := by
  obtain ⟨K,hK,hlabels⟩ := actual_low_full_label_budget B ε hB hε
  refine ⟨K,hK,?_⟩
  filter_upwards [eventual_actual_child_low_mass_payment N lo εv hlo hev,
    eventually_ge_atTop (2:ℝ)] with Z hz hZ2
  refine ⟨hZ2,?_⟩
  intro ι _ s hcard hlow reflected second T p exponent error εcommon M a ξ reserve
    hecommon hT hp seed hs hs0 labels hsup heq hseed hnorm hrad hgeom
    Ds children hDs hdyad hsup₂ heq₂ hseed₂ hnorm₂ Rfirst alloc χ t halloc
  have hbudget := hlabels reflected second Z T (Real.logb Z (volume s)) p exponent
    (error+εv+B*εcommon) hZ2 hT hp seed hs hs0 labels hsup heq hseed hnorm hrad hgeom
    Ds children hDs hdyad hsup₂ heq₂ hseed₂ hnorm₂
  have hexp : p+exponent+(error+εv+B*εcommon)+ε=p+exponent+error+εv+B*εcommon+ε := by ring
  rw [hexp] at hbudget
  have hbudget' :
      (∑l : labels,∑D : Ds l.val,∑v : children l.val D.val,
        Z^(lowGeometryExponent reflected Z (Real.logb Z (volume s)) l.val+
          error+εv+B*εcommon)/((if second then v.val.1.2 else v.val.1.1).absNorm:ℝ))≤
        K*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed.absNorm:ℝ) := by
    let F := fun (l v : FirstSourceLabel)=>
      Z^(lowGeometryExponent reflected Z (Real.logb Z (volume s)) l+
        error+εv+B*εcommon)/((if second then v.1.2 else v.1.1).absNorm:ℝ)
    have hsum : (∑l : labels,∑D : Ds l.val,∑v : children l.val D.val,F l.val v.val)=
        ∑l∈labels,∑D∈Ds l,∑v∈children l D,F l v := by
      rw [Finset.sum_coe_sort labels (fun l=>∑D : Ds l,∑v : children l D.val,F l v.val)]
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.sum_coe_sort (Ds l) (fun D=>∑v : children l D,F l v.val)]
      apply Finset.sum_congr rfl
      intro D hD
      exact Finset.sum_coe_sort (children l D) (fun v=>F l v)
    change (∑l : labels,∑D : Ds l.val,∑v : children l.val D.val,F l.val v.val)≤ _
    rw [hsum]
    simpa only [F,add_assoc] using hbudget
  apply le_trans _ hbudget'
  apply Finset.sum_le_sum
  intro l _
  apply Finset.sum_le_sum
  intro D _
  apply Finset.sum_le_sum
  intro v _
  have hh := hz.2 s hcard hlow reflected second l.val (hsup l.val l.property).1
    (hsup l.val l.property).2 (heq l.val l.property) Rfirst (alloc l D v) (χ l D v) (t l D v)
    (halloc l D v) v.val.1.1 v.val.1.2
    (hsup₂ l.val l.property D.val D.property v.val v.property).1
    (hsup₂ l.val l.property D.val D.property v.val v.property).2 v.val.2.val
    M a ξ reserve error εcommon B hecommon (by
      cases second
      · exact (hnorm₂ l.val l.property D.val D.property v.val v.property).1
      · exact (hnorm₂ l.val l.property D.val D.property v.val v.property).2)
  simpa only [add_assoc] using hh

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_low_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_low_supported_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_low_fiber_admission
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_low_fiber_zero_terms

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainBudget -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondBalanced; sha256 14957628039389786503e992e38113ad5586ace43b34260170c346a162151313 -/
section
                                                         

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonicalScalar CenteredMomentSmooth CenteredMomentCauchy
open CenteredMomentLogDyadic CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentCommonWindowColumn CenteredMomentSectorLocalization
open Cycle61Moment RayFourExpansion
local notation "O" => HeckeFamily.O

/-- Reciprocal reweighting changes the two Cauchy energies without changing
any summand of the physical kernel. The balance may depend on the live row. -/
def secondBalancedLeft {Label : Type*} (s : Label→ SecondBlockSource) (w : Label→ℂ)
    (balance : SecondRow s→ℝ) (q : SecondSector s) (i : (s q.1).LeftIndex) : ℂ :=
  (balance ⟨q.1,q.2.2⟩:ℂ)⁻¹*secondJointLeft s w q i

def secondBalancedRight {Label : Type*} (s : Label→ SecondBlockSource)
    (balance : SecondRow s→ℝ) (q : SecondSector s) (i : (s q.1).RightIndex) : ℂ :=
  (balance ⟨q.1,q.2.2⟩:ℂ)*secondJointRight s q i

def secondBalancedEnergyPair {Label : Type*} [Fintype Label]
    (s : Label→ SecondBlockSource) (w : Label→ℂ) (balance : SecondRow s→ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (∑q∈secondActiveSectors s,
    ‖leftColumn Finset.univ (secondBalancedLeft s w balance q) logAnnulus (secondLeftLog (s q.1)) t‖^2)*
  Real.sqrt (∑q∈secondActiveSectors s,
    ‖rightColumn Finset.univ (secondBalancedRight s balance q) logAnnulus (secondRightLog (s q.1)) t‖^2)

theorem actual_second_balanced_expression {Label : Type*} [Fintype Label]
    (s : Label→ SecondBlockSource) (w : Label→ℂ) (balance : SecondRow s→ℝ)
    (hne : ∀r,w r.1≠0 → balance r≠0) (W : 𝓢(ℝ,ℂ)) :
    (∑l,w l*(s l).value W)=
      ∑q∈secondActiveSectors s,secondJointWeight s q*
        ∑i : (s q.1).LeftIndex,∑j : (s q.1).RightIndex,
          (secondBalancedLeft s w balance q i*star (secondBalancedRight s balance q j))*
            wholeKernel W (fun _=>logAnnulus) (s q.1).ratio (s q.1).rho
              ((s q.1).x q.2.2.2.2.val) (secondLeftLog (s q.1) i) (secondRightLog (s q.1) j) := by
  rw [actual_second_batch_active_expression]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hw : w q.1=0
  · simp only [secondBalancedLeft,secondJointLeft,hw,zero_mul,mul_zero,Finset.sum_const_zero]
  have hb : (balance ⟨q.1,q.2.2⟩:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hne _ hw)
  simp only [secondBalancedLeft,secondBalancedRight,star_mul,Complex.star_def,Complex.conj_ofReal]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  field_simp

theorem actual_second_balanced_contraction (W : 𝓢(ℝ,ℂ)) (A J : ℕ) :
    ∃C : ℝ,0≤ C ∧ ∀{Label : Type*}[Fintype Label][DecidableEq Label]
      (s : Label→ SecondBlockSource) (w : Label→ℂ) (balance : SecondRow s→ℝ),
      (∀r,w r.1≠0 → balance r≠0) → ∀r : ℝ,0< r → (∀l,(s l).ratio=r) → ∀E : ℝ,0≤ E →
      (∀t : ℝ,secondBalancedEnergyPair s w balance t≤ E*(1+‖t‖)^J) →
        (1+r)^A*‖∑l,w l*(s l).value W‖≤ C*E := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_dependent_row_estimate W (fun _=>logAnnulus)
    (fun _=>Real.log 4) (fun _=>Real.log_nonneg (by norm_num))
    (fun _ _ hn=>CenteredMomentSecondIdealBlockBound.logAnnulus_enclosure _ hn) A J
  refine ⟨C,hC,?_⟩
  intro Label _ _ s w balance hne r hr heq E hE he
  rw [actual_second_balanced_expression s w balance hne]
  simp_rw [heq]
  exact hbound r hr (Label:=Label) (κ:=SecondSector s)
    (α:=fun l=>(s l).LeftIndex) (β:=fun l=>(s l).RightIndex)
    (secondActiveSectors s) (fun q=>q.1) (secondBalancedLeft s w balance) (secondBalancedRight s balance)
    (fun l=>secondLeftLog (s l)) (fun l=>secondRightLog (s l))
    (fun q=>(s q.1).rho) (fun q=>(s q.1).x q.2.2.2.2.val) (secondJointWeight s)
    (fun q _=>canonical_sector_signed_weight_norm _ _ (actual_second_row_weight_norm _ _))
    (fun _ _=>logAnnulus_norm _) (fun _ _=>logAnnulus_norm _) E hE he

/-- The reweighted Cauchy pair is still the pair of full joint physical
window sums, with reciprocal factors on the two sides of each row. -/
theorem actual_second_balanced_row_energy {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→ SecondInputDatum α) (w : Label→ℂ)
    (balance : SecondRow (fun l=>(d l).block)→ℝ) (t : ℝ) :
    secondBalancedEnergyPair (fun l=>(d l).block) w balance t=
      Real.sqrt (∑r∈secondLiveRows (fun l=>(d l).block),
        ∑L∈secondResidualIdeals (fun l=>(d l).block) r,
          ‖(balance r:ℂ)⁻¹*secondRowLeftWindow d w t r L‖^2)*
      Real.sqrt (∑r∈secondLiveRows (fun l=>(d l).block),
        ∑L∈secondResidualIdeals (fun l=>(d l).block) r,
          ‖(balance r:ℂ)*secondRowRightWindow d t r L‖^2) := by
  have hl (q : SecondSector (fun l=>(d l).block)) :
      leftColumn Finset.univ (secondBalancedLeft (fun l=>(d l).block) w balance q)
        logAnnulus (secondLeftLog (d q.1).block) t=
      (balance ⟨q.1,q.2.2⟩:ℂ)⁻¹ * leftColumn Finset.univ
        (secondJointLeft (fun l=>(d l).block) w q) logAnnulus (secondLeftLog (d q.1).block) t := by
    simp only [leftColumn,secondBalancedLeft,Finset.mul_sum,mul_assoc]
  have hr (q : SecondSector (fun l=>(d l).block)) :
      rightColumn Finset.univ (secondBalancedRight (fun l=>(d l).block) balance q)
        logAnnulus (secondRightLog (d q.1).block) t=
      (balance ⟨q.1,q.2.2⟩:ℂ) * rightColumn Finset.univ
        (secondJointRight (fun l=>(d l).block) q) logAnnulus (secondRightLog (d q.1).block) t := by
    simp only [rightColumn,secondBalancedRight,star_mul,Complex.star_def,
      Complex.conj_ofReal,Finset.mul_sum,mul_assoc,mul_left_comm]
  unfold secondBalancedEnergyPair
  simp_rw [hl,hr,actual_second_family_left_column,actual_second_family_right_column]
  congr 1 <;> congr 1
  · rw [actual_second_rows_regroup]
    apply Finset.sum_congr rfl
    intro r hr
    exact actual_second_residual_sum (fun l=>(d l).block) r
      (fun L=>‖(balance r:ℂ)⁻¹*secondRowLeftWindow d w t r L‖^2)
  · rw [actual_second_rows_regroup]
    apply Finset.sum_congr rfl
    intro r hr
    rw [←actual_second_residual_sum]
    apply Finset.sum_congr rfl
    intro L hL
    simp only [secondRowSector,secondFamilyRightScalar,secondRowRightWindow,
      secondRowRightScalar,norm_mul,norm_star]
    rfl

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_balanced_expression
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_balanced_contraction

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_balanced_row_energy

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondBalanced -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondBalancedScalar; sha256 f453d447c1dd915dbd489ececf5d612f04e470c6cfbcff9c8f18672010e417a2 -/
section
                                                  

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondPhysicalBlock
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentFirstScale
open CenteredMomentCommonWindowColumn CenteredMomentLogDyadic

lemma second_outside_pos (s : SecondBlockSource) : 0< s.outside := by
  have hC := norm_pos s.C s.hC.1
  have hD := norm_pos s.D s.hD.1
  have hK := s.K_pos
  have hX := dyadicScale_pos (s.dyad 2)
  have hY := dyadicScale_pos (s.dyad 3)
  have hN := normalizer_pos s.C s.D s.hC s.inactive
  unfold SecondBlockSource.outside outerScalar
  positivity

def secondGeometricBalance {Label : Type*} (s : Label→ SecondBlockSource)
    (w : Label→ℂ) (r : SecondRow s) : ℝ := Real.sqrt (‖w r.1‖*(s r.1).outside)

theorem second_geometric_balance_nonzero {Label : Type*}
    (s : Label→ SecondBlockSource) (w : Label→ℂ) (r : SecondRow s)
    (hw : w r.1≠0) : secondGeometricBalance s w r≠0 :=
  (Real.sqrt_pos.mpr (mul_pos (norm_pos_iff.mpr hw) (second_outside_pos _))).ne'

/-- Both balanced column scalars have the same squared norm, including
zero-weight rows. The full outside factor is therefore paid once. -/
theorem actual_second_balanced_scalar_norms {α Label : Type*}
    [Fintype α] [DecidableEq α]
    (d : Label→ SecondInputDatum α) (w : Label→ℂ)
    (r : SecondRow (fun l=>(d l).block)) :
    ‖(secondGeometricBalance (fun l=>(d l).block) w r:ℂ)⁻¹*secondRowLeftScalar d w r‖^2=
      ‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData ∧
    ‖(secondGeometricBalance (fun l=>(d l).block) w r:ℂ)*secondRowRightScalar d r‖^2=
      ‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData := by
  have ho := second_outside_pos (d r.1).block
  have hv := volume_pos (d r.1).input.toData
  have hx : 0≤‖w r.1‖*(d r.1).block.outside := mul_nonneg (norm_nonneg _) ho.le
  have hs := Real.sq_sqrt hx
  have ht := Real.sq_sqrt hv.le
  simp only [secondGeometricBalance,secondRowLeftScalar,secondRowRightScalar,
    norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos ho,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,inv_pow,hs,ht]
  constructor
  · by_cases hw : w r.1=0
    · simp [hw]
    · have hn : 0<‖w r.1‖ := norm_pos_iff.mpr hw
      field_simp
  · trivial

/-- After balancing, the two full window sums have the same literal scalar
weight. In particular, neither side squares the original outside factor. -/
theorem actual_second_geometric_row_energy {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→ SecondInputDatum α) (w : Label→ℂ) (t : ℝ) :
    secondBalancedEnergyPair (fun l=>(d l).block) w
      (secondGeometricBalance (fun l=>(d l).block) w) t=
    Real.sqrt (∑r∈secondLiveRows (fun l=>(d l).block),
      ∑L∈secondResidualIdeals (fun l=>(d l).block) r,
        (‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData)*
        ‖windowColumn (d r.1).input (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed L
          ((d r.1).τ r.2.1) (d r.1).input.t t (dyadicScale ((d r.1).dyad 2))
          logAnnulus r.2.2.2.val‖^2)*
    Real.sqrt (∑r∈secondLiveRows (fun l=>(d l).block),
      ∑L∈secondResidualIdeals (fun l=>(d l).block) r,
        (‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData)*
        ‖windowColumn (d r.1).input (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed L
          ((d r.1).τ r.2.2.1⁻¹) (d r.1).input.t (-t) (dyadicScale ((d r.1).dyad 3))
          (fun x=>star (logAnnulus x)) (-r.2.2.2.val)‖^2) := by
  rw [actual_second_balanced_row_energy]
  congr 1 <;> congr 1
  · apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro L hL
    rw [secondRowLeftWindow,←mul_assoc,norm_mul,mul_pow,
      (actual_second_balanced_scalar_norms d w r).1]
  · apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro L hL
    rw [secondRowRightWindow,←mul_assoc,norm_mul,mul_pow,
      (actual_second_balanced_scalar_norms d w r).2]

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_outside_pos
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_geometric_balance_nonzero
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_balanced_scalar_norms

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_geometric_row_energy

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondBalancedScalar -/
