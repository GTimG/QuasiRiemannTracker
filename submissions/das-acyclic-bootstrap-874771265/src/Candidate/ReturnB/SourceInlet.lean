/- Adapted 2026-10-24 for Subhanjan Das, AI-assisted with OpenAI Codex.
Original Hailey Collet/Mark Lewko notices and Apache-2.0 license retained. -/
/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal source inlets for the new return. Global source proofs remain premises. -/
import Candidate.ReturnB.Finite.ReturnConstants
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Existence.UniformSource
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Raw.InitialMomentInlet
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace Das.QRH.ReturnB
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths QRH.Record12518109Source QRH.Record12518109Existence
open HeckeFamily CenteredMomentNaturalFixedRaySource Filter DasStageBFinite
local notation "O" => HeckeFamily.O
local instance (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

def globalFace (B lam cap : ℝ) : SourceFace := ⟨B,lam,0,B,0,cap⟩
def countGlobal : SourceFace := globalFace countCB countCL (44001/1000000:ℝ)
def physicalGlobal : SourceFace := globalFace physicalB physicalLambda (43001/1000000:ℝ)
def countWindow (j : ℕ) : SourceFace :=
  ⟨countCB-j/4000,countCL,2/5,11/25,17/500,11/250⟩
def physicalWindow : SourceFace :=
  ⟨physicalB,physicalLambda,2/5,11/25,17/500,43/1000⟩

def broadFace (B lam cap : ℝ) : SourceFace := ⟨B,lam,0,1/2,0,cap⟩
theorem global_restricts_broad {B lam cap : ℝ} (hB : 1/2≤B) :
    (globalFace B lam cap).Restricts (broadFace B lam cap) := by
  constructor <;> simp only [globalFace,broadFace] <;> linarith

theorem count_restricts (j : ℕ) : countGlobal.Restricts (countWindow j) := by
  constructor <;> norm_num [countGlobal,globalFace,countWindow,countCB,countCL]
  positivity

theorem physical_restricts : physicalGlobal.Restricts physicalWindow := by
  constructor <;> norm_num [physicalGlobal,globalFace,physicalWindow,physicalB,physicalLambda]

theorem unit_source_restrict {strong weak : SourceFace} (hface : strong.Restricts weak)
    {mesh ε : ℝ} (hsource : UnitFaceSource strong mesh ε) : UnitFaceSource weak mesh ε := by
  intro α _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨degree,S,C,hC,hsource⟩ := hsource α rayM H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  exact ⟨degree,S,C,hC,hsource.mono (fun Z hZ=>initialAffineAt_restrict rayM H hH hface W
    2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε Z η η₀ Q degree S C (by norm_num) hZ)⟩

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

/-- The scale is not specialized to the original unit root. The threshold,
controls and constant precede all roots in the entire supplied interval. -/
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
end Das.QRH.ReturnB
#print axioms Das.QRH.ReturnB.selected_sources_common_mesh
#print axioms Das.QRH.ReturnB.source_on_root_interval
