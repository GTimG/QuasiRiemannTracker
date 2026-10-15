/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B001
import Submissions.cycle61_c0125139.Bundles.B002
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorMomentData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCountParameters
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblySource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseRawReference
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseRawUniform
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersFixedSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersHighData

/- BEGIN ORIGINAL Cycle25.Assembly.Count.Parameters; sha256 56d3cc62a8de51e0089b351a98959a3ea4ed905db08cb426c9f7f12d751b1197 -/
section
                                      
                                      



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.Cycle25ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount

structure CountParameters (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (εm : ℝ) where
  c : ℝ
  k : ℝ
  c_pos : 0<c
  c_one : c≤1
  k_pos : 0<k
  balanced : ∃K₀ : ℝ,0≤K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε T allowance κplain ν C height q : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/1000 →
      7/10≤κplain → κplain≤3/4 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀{Label Slot : Type} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) (q/(2*a-1)) κplain) T allowance i),
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain c k C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(rowCount (2*a-1) (q/(2*a-1)) κplain+
          159*ε+εm+B.mesh+7*ν)

theorem exists_count_parameters
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    Nonempty (CountParameters M H εm) := by
  obtain ⟨c,k,K,hc,hc1,hk,hK,hcount⟩ := balanced_adaptive_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  exact ⟨⟨c,k,hc,hc1,hk,⟨K,hK,hcount⟩⟩⟩

end SevenEighths.Cycle25ProbeHighRowFamily
end
end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.Parameters -/

/- BEGIN ORIGINAL Cycle25.Assembly.MomentData; sha256 be25b9527e3b5824d2c91385d7a73c4c4e8ed05d456bfb15c97f80feb4161d2f -/
section
                                                     
namespace Cycle25.Weighted
structure MomentData where
  N : ℕ
  ell : Fin N → ℝ
  t : ℝ
  ε : ℝ
  e : ℝ
  t_pos : 0 < t
  t_small : t ≤ 1/100000000
  slots_injective : Function.Injective ell
  slots_bounds : ∀j, 0 < ell j ∧ ell j ≤ 1
  epsilon_pos : 0 < ε
  epsilon_small : ε ≤ 1/1000
  e_pos : 0 < e
end Cycle25.Weighted

/- Adapted unchanged from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/

end
/- END ORIGINAL Cycle25.Assembly.MomentData -/

/- BEGIN ORIGINAL Cycle25.Assembly.SourceData; sha256 0e328009308adda7bf0345d415ae604181bcfd8c0e022af29ae84516a8d8c3d7 -/
section
                                                             
                                  
                                                        
                                                               
                                                                        
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.Cycle25ProbeFinalAssembly
open ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
local notation "O" => HeckeFamily.O

structure WeightedSourceData (D : Cycle25.Weighted.MomentData) where
  S : Finset (Ideal O)
  exclusions : SourceExclusions S
  maximal : ∀P∈S,P.IsMaximal
  first : FirstTail (4*D.e) S
  w : ℝ→ℝ
  W : SchwartzMap ℝ ℂ
  smooth : ContDiff ℝ ∞ w
  compact : HasCompactSupport w
  support : Function.support w⊆Set.Ioo 1 2
  positive_support : tsupport w⊆Set.Ioi 0
  bounded : ∀x,0 ≤ w x ∧ w x ≤ 1
  nonzero : w≠0
  complex_eq : ∀x,W x=(w x:ℂ)
  complex_nonzero : W≠0
  complex_support : Function.support W⊆Set.Icc 1 2
  real : ∀x,(W x).im=0
  nonnegative : ∀x,0 ≤ (W x).re

theorem weighted_exists_source_data (D : Cycle25.Weighted.MomentData) : Nonempty (WeightedSourceData D) := by
  obtain ⟨S,_,hS,hfirst,hmax⟩ := exists_fixed_source D.e D.e_pos ∅ (by simp)
  obtain ⟨w,W,hw,hc,hs,hp,hb,hn,he,hWn,hWs,hr,hWpos⟩ := exists_fixed_probe_window
  exact ⟨⟨S,hS,hmax,hfirst,w,W,hw,hc,hs,hp,hb,hn,he,hWn,hWs,hr,hWpos⟩⟩

def WeightedSourceData.modulus {D : Cycle25.Weighted.MomentData} (F : WeightedSourceData D) : Ideal O := ∏P∈F.S,P

instance {D : Cycle25.Weighted.MomentData} (F : WeightedSourceData D) : NeZero F.modulus :=
  ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩

instance {D : Cycle25.Weighted.MomentData} (F : WeightedSourceData D) : Finite (O ⧸ F.modulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne F.modulus)

theorem weighted_source_count_parameters {D : Cycle25.Weighted.MomentData} (F : WeightedSourceData D) :
    Nonempty (CountParameters F.modulus ⊤ D.t) := by
  exact exists_count_parameters F.modulus ⊤ le_top F.S F.w F.smooth F.compact
    F.positive_support (fun x=>(F.bounded x).1) F.nonzero 1 2 1 (by norm_num) (by norm_num)
    (by norm_num) F.support (fun x=>(F.bounded x).2) D.t D.t_pos

end SevenEighths.Cycle25ProbeFinalAssembly
end
end OAI

/- Actual source data adapted unchanged from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
The legacy count-parameter existence helper is not a Cycle25 count estimate. -/

end
/- END ORIGINAL Cycle25.Assembly.SourceData -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.InverseRawField; sha256 c4a5b60b1dd4ce344a4c52e73e963fa95d231d296f0a3c71f8d08ee607c1d15f -/
section
                                  
                                                                 
                                                               
                                        
                                                              

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.Cycle25ProbeDetectorInverseRawField
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open HeckeDetectorInverseFiberCount DetectorDictionaryInverseClippedUniform
open ProbeHighRowFamily ProbeFinalAssembly Cycle25ProbeHighRowFamily

private theorem raw_mono (data:RowData)(W:ℝ→ℂ)(c κ A B:ℝ)
    (hAB:A≤B)(h:RawMoment data W c κ A):RawMoment data W c κ B:=by
  intro H D hH hD hcap rows hrows
  apply (h H D hH hD hcap rows hrows).trans
  gcongr

theorem fixed_raw_profiles (c κ:ℝ)(hc:0<c)(hκ:0<κ):
    ∃J:ℕ,∀data:RowData,∃C:ℝ,0<C ∧
      ∀reverse:Bool,∀n:ℕ,n≤2→∀U:ℝ,0<U→∀tstar r:ℝ,
      ∀s∈Set.Icc (0:ℝ) 1,∀height t:ℝ,0≤height→t∈Set.Icc (-height) height→
      let W:=twistProfile (logTest (orientedProfile reverse (inverseTest U tstar r)) n) s t;
      RawMoment data W c κ (C*(1+height)^J) ∧
      RawMoment data (scaleProfile W) c κ (C*(1+height)^J):=by
  obtain ⟨J,hreference⟩:=DetectorDictionaryInverseRawReference.raw_reference_moment
    referenceWindow (1/18) (13/4) c κ (by norm_num) (by norm_num)
    (fun x hx=>referenceWindow_support (subset_tsupport _ hx)) hc hκ
  obtain ⟨K,C,hC,hfamily⟩:=DetectorDictionaryInverseRawUniform.raw_pair_height_uniform J
  refine ⟨K,?_⟩
  intro data
  obtain ⟨A,hA,href⟩:=hreference data
  exact ⟨A*C,mul_pos hA hC,hfamily data c κ A hA.le href⟩

variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

theorem source_batch_inverse_raw
    (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(εm:ℝ)(counts:Cycle25ProbeHighRowFamily.CountParameters M H εm):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0<C ∧
    ∀{Slot:Type*}{U a ε tstar T allowance:ℝ}{i:ℕ},0<U→
    ∀(B:Batch M H (Sum Bool (RayQuotient.Characters M H)) Slot U a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S hS η→
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤height→∀n:ℕ,n≤2→∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let F:=B.fiber bin label left right hne;
      let W:=twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t;
      RawMoment F.rowData W counts.c
        counts.k (C*(1+height)^J) ∧
      RawMoment F.rowData (scaleProfile W) counts.c
        counts.k (C*(1+height)^J):=by
  obtain ⟨J,hraw⟩:=fixed_raw_profiles counts.c counts.k counts.c_pos counts.k_pos
  refine ⟨J,?_⟩
  intro η
  let data:=sourceMomentData M H hH S hS η
  choose C hC hb using (fun label=>hraw (data label))
  let Csum:ℝ:=1+∑label,C label
  have hsum:0≤∑label,C label:=Finset.sum_nonneg (fun j _=>(hC j).le)
  have hCs:0<Csum:=by dsimp [Csum];linarith
  have hClabel (label):C label≤Csum:=by
    have he:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hC j).le) (Finset.mem_univ label)
    dsimp [Csum];linarith
  refine ⟨Csum,hCs,?_⟩
  intro Slot U a ε tstar T allowance i hU B hdata bin label left right hne height hheight n hn s hs t ht F W
  have hd:F.rowData=data label:=by change B.data label=data label;rw [hdata]
  have hp:=hb label F.reverse n hn U hU tstar F.r s hs height t hheight ht
  have hconstant:C label*(1+height)^J≤Csum*(1+height)^J:=
    mul_le_mul_of_nonneg_right (hClabel label) (by positivity)
  rw [hd]
  exact ⟨raw_mono _ _ _ _ _ _ hconstant hp.1,raw_mono _ _ _ _ _ _ hconstant hp.2⟩
end SevenEighths.Cycle25ProbeDetectorInverseRawField
end
end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.InverseRawField -/
