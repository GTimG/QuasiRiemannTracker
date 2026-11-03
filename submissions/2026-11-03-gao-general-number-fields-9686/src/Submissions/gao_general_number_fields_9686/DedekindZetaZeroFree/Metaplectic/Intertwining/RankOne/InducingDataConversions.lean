/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Intertwining/RankOne/InducingDataConversions.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Torus.CubicHeisenbergInducingData
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenbergInducingData

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLocalExceptionalConstruction
open KPLocalPrincipalSeries KPLocalStoneVonNeumann
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

def actualRawInducing (S : CanonicalFiniteInducingData F ζ hζ q) :
    KPExceptionalRaw.RawFiniteInducingData F ζ hζ q where
  D := S.D
  groupD := S.groupD
  finiteD := S.finiteD
  cubeClassEquiv := S.cubeClassEquiv
  heisenberg := S.heisenberg
  borel := S.borel
  borel_eq := S.borel_eq
  torus_full := S.torus_full
  coordinate_lift := S.coordinate_lift
  cube_class := S.cube_class
  center_exact := S.center_exact
  cube_actual := S.cube_actual
  central := S.central
  central_actual := S.central_actual
  central_character := S.central_character
  center_parameterization := S.center_parameterization
  prescribed_center := S.prescribed_center
  split_scalars := S.split_scalars
  polarization := S.polarization
  iwasawa := S.iwasawa
  openCell := S.openCell
  openCell_ordinary := S.openCell_ordinary

def actualCanonicalInducing (S : KPExceptionalRaw.RawFiniteInducingData F ζ hζ q) :
    CanonicalFiniteInducingData F ζ hζ q where
  D := S.D
  groupD := S.groupD
  finiteD := S.finiteD
  cubeClassEquiv := S.cubeClassEquiv
  heisenberg := S.heisenberg
  borel := S.borel
  borel_eq := S.borel_eq
  torus_full := S.torus_full
  coordinate_lift := S.coordinate_lift
  cube_class := S.cube_class
  center_exact := S.center_exact
  cube_actual := S.cube_actual
  central := S.central
  central_actual := S.central_actual
  central_character := S.central_character
  center_parameterization := S.center_parameterization
  prescribed_center := S.prescribed_center
  split_scalars := S.split_scalars
  polarization := S.polarization
  iwasawa := S.iwasawa
  openCell := S.openCell
  openCell_ordinary := S.openCell_ordinary

end
end DedekindZetaZeroFree.KPLocalExceptionalConstruction
