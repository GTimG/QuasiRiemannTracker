/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B000
import Submissions.cycle61_c0125139.Bundles.B003
import Submissions.cycle61_c0125139.Bundles.B008
import Submissions.cycle61_c0125139.Bundles.B020
import Submissions.cycle61_c0125139.Bundles.B022
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblySource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersSlotLengths

/- BEGIN ORIGINAL Cycle61.Assembly.Count.Geometry; sha256 8747f4a92708b8cfc8f83b020f3fe634d3eee5aaf4897fd4300fe28335ea0a2c -/
section
                                
                                       

namespace Cycle61.Assembly.Count
noncomputable section
open Arithmetic

/-- The new exact slot total supplies the generic whole-slot detector selector. -/
theorem count_slot_supply : (7/37:ℝ)*(7/8)≤ell := by norm_num [ell]
/-- The manuscript's weaker inverse capacity is also supplied at the largest row norm. -/
theorem manuscript_slot_supply : (4/21:ℝ)*(7/8)≤ell := by norm_num [ell]
theorem ell_pos : 0<ell := by norm_num [ell]

theorem relative_slot_supply {N : ℕ} (length : Fin N→ℝ)
    (hsum : ∑j,length j=ell) {d : ℝ} (hd : 0<d) (hdmax : d≤7/8) :
    7/37≤∑j,length j/d := by
  rw [←Finset.sum_div,hsum]
  apply (le_div_iff₀ hd).mpr
  have hm:=mul_le_mul_of_nonneg_left hdmax (show (0:ℝ)≤7/37 by norm_num)
  linarith [count_slot_supply]
end
end Cycle61.Assembly.Count

end
/- END ORIGINAL Cycle61.Assembly.Count.Geometry -/

/- BEGIN ORIGINAL Cycle61.Assembly.Count.Data; sha256 30fb653194741337f0ef824a6fe55b97c382767d56cb83c8bf49ccce616c7d6c -/
section
                                      
                                        
                                                               

namespace OAI.SevenEighths.Cycle61DetectorCount
noncomputable section
open scoped Classical BigOperators ContDiff
open HeckeFamily HeckeInverseAmplification ProbePhysical

/-- Actual small prime-slot lengths at the new rational total. All scalar
parameters are fixed before the live character, row height and amplitude class. -/
structure Data where
  N : ℕ
  length : Fin N→ℝ
  t : ℝ
  ε : ℝ
  e : ℝ
  witnessKappa : ℝ
  cost : ℝ
  momentKappa : ℝ
  t_pos : 0<t
  epsilon_pos : 0<ε
  epsilon_small : ε≤1/1000
  e_pos : 0<e
  e_small : e<1/1000
  witnessKappa_pos : 0<witnessKappa
  witnessKappa_small : witnessKappa≤1
  cost_pos : 0<cost
  momentKappa_lo : 7/10≤momentKappa
  momentKappa_hi : momentKappa≤3/4
  slots_pos : ∀j,0<length j
  slots_small : ∀j,length j≤(1/200)*t
  slots_sum : ∑j,length j=Cycle61.Arithmetic.ell
  detector_budget : 12*e*((22:ℝ)+2)+8*witnessKappa+2*cost≤ε/2

/-- Source exclusions and a genuine common physical window; no probe theorem
or endpoint is stored in this structure. -/
structure SourceData where
  S : Finset (Ideal O)
  exclusions : SourceExclusions S
  maximal : ∀P∈S,P.IsMaximal
  w : ℝ→ℝ
  smooth : ContDiff ℝ ∞ w
  compact : HasCompactSupport w
  support : Function.support w⊆Set.Ioo 1 2
  positive_support : tsupport w⊆Set.Ioi 0
  bounded : ∀x,0≤w x ∧ w x≤1
  nonzero : w≠0

def SourceData.modulus (F : SourceData) : Ideal O := ∏P∈F.S,P
instance (F : SourceData) : NeZero F.modulus :=
  ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
instance (F : SourceData) : Finite (O⧸F.modulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne F.modulus)

theorem fresh_count_parameters (D : Data) (F : SourceData) :
    Nonempty (Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t) := by
  exact Cycle25ProbeHighRowFamily.exists_count_parameters F.modulus ⊤ le_top F.S F.w
    F.smooth F.compact F.positive_support (fun x=>(F.bounded x).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support
    (fun x=>(F.bounded x).2) D.t D.t_pos
end
end OAI.SevenEighths.Cycle61DetectorCount

end
/- END ORIGINAL Cycle61.Assembly.Count.Data -/

/- BEGIN ORIGINAL Cycle61.Assembly.Count.BaselineGeometry; sha256 206ae66a6d421e10ced2ff5e9b1a3da621ad1dcb73f16aa65709ae0e36736fc6 -/
section
                                  
                                  
                            
                                                        

namespace OAI.SevenEighths.Cycle61DetectorCount
noncomputable section
open scoped Classical BigOperators

/-- Smallness and distinctness used by the original physical prime dictionary. -/
structure BaselineData extends Data where
  t_small : t≤1/100000000
  slots_injective : Function.Injective length

def BaselineData.toMomentData (D : BaselineData) : Cycle25.Weighted.MomentData where
  N:=D.N
  ell:=D.length
  t:=D.t
  ε:=D.ε
  e:=D.e
  t_pos:=D.t_pos
  t_small:=D.t_small
  slots_injective:=D.slots_injective
  slots_bounds:=fun j=>⟨D.slots_pos j,by linarith [D.slots_small j,D.t_small]⟩
  epsilon_pos:=D.epsilon_pos
  epsilon_small:=D.epsilon_small
  e_pos:=D.e_pos

/-- Rescale a distinct prime-slot partition to the exact new rational total. -/
theorem exists_distinct_fine_slots {cap : ℝ} (hc : 0<cap) :
    ∃N:ℕ,∃length:Fin N→ℝ,Function.Injective length ∧
      (∀j,0<length j ∧ length j≤cap) ∧ ∑j,length j=Cycle61.Arithmetic.ell := by
  have he:=Cycle61.Assembly.Count.ell_pos
  obtain ⟨N,hN,old,hinj,hbound,hsum⟩:=Parameters.exists_distinct_slot_lengths
    (cap/(6*Cycle61.Arithmetic.ell)) (by positivity)
  refine ⟨N,fun j=>6*Cycle61.Arithmetic.ell*old j,?_,?_,?_⟩
  · intro j k hjk
    exact hinj ((mul_right_inj' (show 6*Cycle61.Arithmetic.ell≠0 by positivity)).mp hjk)
  · intro j
    refine ⟨mul_pos (by positivity) (hbound j).1,?_⟩
    have hb:old j*(6*Cycle61.Arithmetic.ell)<cap:=
      (lt_div_iff₀ (show (0:ℝ)<6*Cycle61.Arithmetic.ell by positivity)).mp (hbound j).2
    nlinarith
  · rw [←Finset.mul_sum,hsum]
    ring

theorem exists_baseline_data_common_mesh {κ σ : ℝ} (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hσ : 0<σ) (mesh : ℝ→ℝ) (hmeshPos : ∀t,0<t→0<mesh t) :
    ∃D:BaselineData,D.momentKappa=κ ∧ 159*D.ε+609*D.t≤σ ∧
      (∀j,D.length j≤Cycle25.sourceMesh D.t/200) ∧ (∀j,D.length j≤mesh D.t/200) := by
  let ε : ℝ:=min (σ/400) (1/200000)
  have hep : 0<ε:=lt_min (by positivity) (by norm_num)
  have heσ : ε≤σ/400:=min_le_left _ _
  have hes : ε≤1/200000:=min_le_right _ _
  let t : ℝ:=ε/2000
  have ht : 0<t:=by positivity
  have hmesh:=Cycle25.sourceMesh_pos ht
  obtain ⟨N,length,hinj,hbound,hsum⟩:=exists_distinct_fine_slots
    (cap:=min ((1/200)*t) (min (Cycle25.sourceMesh t/200) (mesh t/200)))
      (lt_min (by positivity) (lt_min (by positivity) (by have:=hmeshPos t ht;positivity)))
  let D : BaselineData := {
    N:=N,length:=length,t:=t,ε:=ε,e:=ε/10000,
    witnessKappa:=ε/1000,cost:=ε/1000,momentKappa:=κ,
    t_pos:=ht,t_small:=by dsimp [t];linarith,
    epsilon_pos:=hep,epsilon_small:=by linarith,
    e_pos:=by positivity,e_small:=by linarith,witnessKappa_pos:=by positivity,
    witnessKappa_small:=by linarith,cost_pos:=by positivity,
    momentKappa_lo:=hk,momentKappa_hi:=hk1,slots_injective:=hinj,
    slots_pos:=fun j=>(hbound j).1,
    slots_small:=fun j=>(hbound j).2.trans (min_le_left _ _),
    slots_sum:=hsum,detector_budget:=by linarith }
  refine ⟨D,rfl,?_,?_⟩
  · dsimp [D,t];linarith
  · constructor
    · intro j;exact (hbound j).2.trans ((min_le_right _ _).trans (min_le_left _ _))
    · intro j;exact (hbound j).2.trans ((min_le_right _ _).trans (min_le_right _ _))
/-- Baseline-only specialization of the common-mesh constructor. -/
theorem exists_baseline_data_fine {κ σ : ℝ} (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hσ : 0<σ) : ∃D:BaselineData,D.momentKappa=κ ∧
      159*D.ε+609*D.t≤σ ∧ ∀j,D.length j≤Cycle25.sourceMesh D.t/200 := by
  obtain ⟨D,hκ,he,hfine,_⟩:=exists_baseline_data_common_mesh hk hk1 hσ
    Cycle25.sourceMesh (fun _ ht=>Cycle25.sourceMesh_pos ht)
  exact ⟨D,hκ,he,hfine⟩

end
end OAI.SevenEighths.Cycle61DetectorCount

end
/- END ORIGINAL Cycle61.Assembly.Count.BaselineGeometry -/

/- BEGIN ORIGINAL Cycle61.Assembly.Count.MomentGates; sha256 de450e95b26f8fcfaa5bc28eb957c0e85f379f9d7437bcae5bdd94e38c3fb43d -/
section
                                                                   
                                  
                                               

namespace OAI.SevenEighths.Cycle61DetectorCount
noncomputable section
open scoped Classical BigOperators
open HeckeFamily ProbePhysical ProbeHighRowFamily HeckeInverseAmplification
open HeckeDetectorRawFiber HeckeDetectorBatch

/-- Actual physical detector fiber moments on the new slot lengths. This is
an integration input, not an endpoint or a claimed affine moment theorem. -/
def SourceMomentBound (D : Data) (F : SourceData)
    (counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t)
    (η : Character) (Z τ C height : ℝ) : Prop :=
  ∀rows : Finset FreeRow,∀d a : ℝ,(1/200:ℝ)≤d→d≤7/8→51/100<a→a≤7/8→
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-D.t))→
    ∀i : ℕ,∀z : ℂ,z.re=17/50→|z.im|≤height→
    Cycle25ProbeHighRowFamily.SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η
      rows D.length (fun _ y=>(F.w y:ℂ)) Z d a D.ε τ (7/8) 2 D.t D.t i z
      D.momentKappa counts.c counts.k C height D.t

lemma SourceMomentBound.mono_constant {D : Data} {F : SourceData}
    {counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t}
    {η : Character} {Z τ C C' height : ℝ}
    (hZ : 0≤Z) (h : SourceMomentBound D F counts η Z τ C height)
    (hC : C≤C') : SourceMomentBound D F counts η Z τ C' height := by
  intro rows d a hd hd' ha ha' hrows i z hz hzh q B hsub hdata hrev hslots hwidth
    hprof hupp hext hmesh hbin hfam bin j J K hne
  have hm := h rows d a hd hd' ha ha' hrows i z hz hzh q B hsub hdata hrev hslots
    hwidth hprof hupp hext hmesh hbin hfam bin j J K hne
  refine ⟨ProbeFinalAssembly.moments_mono_constant (Real.rpow_nonneg hZ _) hm.original hC,?_⟩
  intro selected hsel hcap j k hj s hs t ht
  exact (hm.plain_marked selected hsel hcap j k hj s hs t ht).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Real.rpow_nonneg hZ _) _))

/-- The exact genuine physical gates needed by the optimized detector count.
The original fields contain MI/raw and unmarked plain estimates; the marked
plain gate uses 2m+6κz≤1. The original 3/4 marked gate is deduced. -/
def FiberFields {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (κplain c inverseKappa C height εm : ℝ) : Prop :=
  Cycle25DetectorRawFiber.BaseMoments F c inverseKappa C height εm ∧
    Cycle25DetectorRawFiber.MarkedPlainMoment F κplain C height εm

theorem moments_of_physical_fields {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {κplain c inverseKappa C height εm : ℝ} (hk : κplain≤3/4)
    (h : FiberFields F κplain c inverseKappa C height εm) :
    Cycle25DetectorRawFiber.Moments F κplain c inverseKappa C height εm :=
  Cycle25DetectorRawFiber.Moments.of_fields F hk h.1 h.2
end
end OAI.SevenEighths.Cycle61DetectorCount

end
/- END ORIGINAL Cycle61.Assembly.Count.MomentGates -/
