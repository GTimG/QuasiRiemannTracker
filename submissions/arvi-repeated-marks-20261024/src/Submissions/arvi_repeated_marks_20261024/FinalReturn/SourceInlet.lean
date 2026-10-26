/- Repeated marks: fork of Collet's final-stage module SourceInlet (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
import Submissions.arvi_repeated_marks_20261024.FinalReturn.ReturnConstants
import Submissions.hailey_collet_1252270103.Record1252270103Return.SourceInlet
import Submissions.hailey_collet_1252270103.Record12518109Existence.UniformSource
import Submissions.hailey_collet_1252270103.Record12518109Raw.InitialMomentInlet
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.RepeatedMarks.Return
open QRH.Record1252270103Return
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths QRH.Record12518109Source QRH.Record12518109Existence
open HeckeFamily CenteredMomentNaturalFixedRaySource Filter
local notation "O" => HeckeFamily.O
local instance (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

def countGlobal : SourceFace := globalFace countCB countCL (549989/10000000)
def physicalGlobal : SourceFace := globalFace physicalB physicalLambda (549989/10000000)
def countWindow (j : ℕ) : SourceFace :=
  ⟨countCB-j/4000,countCL,2/5,11/25,17/500,13/250⟩
def physicalWindow : SourceFace :=
  ⟨physicalB,physicalLambda,2/5,11/25,17/500,43/1000⟩

theorem count_restricts (j : ℕ) : countGlobal.Restricts (countWindow j) := by
  constructor <;> norm_num [countGlobal,globalFace,countWindow,countCB,countCL]
  positivity

theorem physical_restricts : physicalGlobal.Restricts physicalWindow := by
  constructor <;> norm_num [physicalGlobal,globalFace,physicalWindow,physicalB,physicalLambda]

/-- One mesh, chosen before the ambient slot type and every live parameter,
works for both global sources and every weaker count face. -/
theorem selected_sources_common_mesh
    (hC : UniformUnitFaceSource countGlobal) (hP : UniformUnitFaceSource physicalGlobal)
    {ε : ℝ} (hε : 0<ε) :
    ∃mesh : ℝ,0<mesh ∧ UnitFaceSource countGlobal mesh ε ∧
      UnitFaceSource physicalGlobal mesh ε ∧
      (∀j : ℕ, UnitFaceSource (countWindow j) mesh ε) ∧
      UnitFaceSource physicalWindow mesh ε := by
  obtain ⟨c,hc,hcs⟩ := hC ε hε
  obtain ⟨p,hp,hps⟩ := hP ε hε
  have hcs' := hcs.mono_mesh (min_le_left c p)
  have hps' := hps.mono_mesh (min_le_right c p)
  exact ⟨min c p,lt_min hc hp,hcs',hps',
    fun j=>unit_source_restrict (count_restricts j) hcs',
    unit_source_restrict physical_restricts hps'⟩

theorem source_on_root_interval {face : SourceFace} {unitMesh unitε : ℝ}
    (hsource : UnitFaceSource face unitMesh unitε)
    {α : Type} [Fintype α] [DecidableEq α]
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM≤H)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (bΦ mesh Mmin Mmax ε : ℝ) (hbΦ : 2≤bΦ)
    (hMmin : 0<Mmin) (hunitMesh : 0≤unitMesh)
    (hmesh : mesh≤unitMesh*Mmin) (hunitε : 0≤unitε) (hε : Mmax*unitε≤ε)
    (η η₀ : Character) (Q : Ideal O)
    (hQray : Q≤rayM) (hQ0 : internalQ Q η₀≠0) (hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) :
    ∃degree : ℕ, ∃S : Finset (ℕ×ℕ), ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      InitialAffineAt (α:=α) rayM H hH face W 2 (1/4) (9/4) bΦ mesh
        (33/50) (33/50) Mmin Mmax ε Z η η₀ Q degree S C := by
  obtain ⟨degree,S,C,hC,hsource⟩ := hsource α rayM H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  exact ⟨degree,S,C,hC,initialAffineAt_uniform_rescale rayM H hH face W
    2 (1/4) (9/4) bΦ mesh unitMesh (33/50) (33/50) Mmin Mmax ε unitε η η₀ Q
    degree S C hMmin hC.le hunitMesh hmesh hunitε hε hsource⟩
end
end QRH.RepeatedMarks.Return
#print axioms QRH.RepeatedMarks.Return.selected_sources_common_mesh
#print axioms QRH.RepeatedMarks.Return.source_on_root_interval
