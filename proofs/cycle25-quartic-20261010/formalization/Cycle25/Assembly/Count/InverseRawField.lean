import Cycle25.Assembly.SourceData
import OAI.NumberTheory.DirichletL.Dictionary.InverseRawReference
import OAI.NumberTheory.DirichletL.Dictionary.InverseRawUniform
import Cycle25.Assembly.Count.Parameters
import OAI.NumberTheory.DirichletL.Detector.DetectorMomentData

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
