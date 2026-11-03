/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Intertwining/RankOne/OpenCellKernelData.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Kubota.CubicLocalAndAdelicCovers
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.StandardIntegralAndLevelContinuation
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.HarmonicAnalysis.Haar.CubicPowerPushforward

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory
namespace DedekindZetaZeroFree.KPRankOneBruhatKernelTransport
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPRankOneShellContinuation
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))
abbrev LocalField := q.adicCompletion F
abbrev Cover := KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)
abbrev RawCover := KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)

instance coverTopology : TopologicalSpace (Cover F ζ hζ q) :=
  KPPGLLocalCover.finiteTopology F ζ hζ q
    (KPAdelicCoverRestrictedProduct.depth F ζ hζ q)

instance coverTopologicalGroup : IsTopologicalGroup (Cover F ζ hζ q) :=
  (KPPGLLocalCover.finite_topological_cover F ζ hζ q _
    (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).2.2.1

def signedWeylRaw : RawCover F ζ hζ q :=
  KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (-1) *
    KPStandardLocalRootLifts.W F ζ hζ (Sum.inr q)

def signedWeyl : Cover F ζ hζ q :=
  KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (signedWeylRaw F ζ hζ q)

def nLift (s : LocalField F q) : Cover F ζ hζ q :=
  KPPGLLocalCover.N F ζ hζ (Sum.inr q) s

def hLift (v : (LocalField F q)ˣ) : Cover F ζ hζ q :=
  KPPGLLocalCover.A F ζ hζ (Sum.inr q) (v ^ 2)

variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H D : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}

structure Binding
    (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
    (P : Polarization T) where
  projection_eq : ∀ g : RawCover F ζ hζ q,
    A.projection (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g) =
      Matrix.ProjGenLinGroup.mk g.g
  weyl_eq : A.liftedW = signedWeyl F ζ hζ q
  upper_eq : ∀ s : LocalField F q,
    (A.upperRoot (Multiplicative.ofAdd s) : Cover F ζ hζ q) = nLift F ζ hζ q s
  rootTorus : (LocalField F q)ˣ → H
  torus_eq : ∀ v, (A.torus (rootTorus v) : Cover F ζ hζ q) = hLift F ζ hζ q v
  coordinate_eq : ∀ v, A.coordinate (rootTorus v) = v ^ 2
  centralTorus : rootsOfUnity 3 F → H
  central_eq : ∀ e, (A.torus (centralTorus e) : Cover F ζ hζ q) =
    KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e
  central_coordinate : ∀ e, A.coordinate (centralTorus e) = 1
  eta : rootsOfUnity 3 F →* ℂˣ
  eta_injective : Function.Injective eta
  genuine : ∀ (ε : Sign) e (V : InducedModule P),
    (borelAction A P ε) (A.torus (centralTorus e)) V = (eta e : ℂ) • V

variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)

def openCoordinate (s : LocalField F q) : Cover F ζ hζ q :=
  (signedWeyl F ζ hζ q)⁻¹ * nLift F ζ hζ q s

def IsOpenCellSection (ε : Sign) (z : ℂ) (f : sectionSpace A P ε z) : Prop :=
  HasCompactSupport (fun s : LocalField F q => f.val (openCoordinate F ζ hζ q s)) ∧
    ∀ g : Cover F ζ hζ q,
      (¬ ∃ (b : A.B) (s : LocalField F q), g = (b : Cover F ζ hζ q) * openCoordinate F ζ hζ q s) →
      f.val g = 0

end
end DedekindZetaZeroFree.KPRankOneBruhatKernelTransport
