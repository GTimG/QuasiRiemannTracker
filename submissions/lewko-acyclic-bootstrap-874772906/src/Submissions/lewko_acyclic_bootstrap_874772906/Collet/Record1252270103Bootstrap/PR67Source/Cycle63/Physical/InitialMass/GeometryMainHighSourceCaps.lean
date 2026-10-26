import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainNormalized
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometrySecondCaps
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentSectorLocalization CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentLogDyadic
open RayFourExpansion CenteredMomentCommonProfile

/-- Both first ideals retain the original source-radius cap in either
physical orientation. No allocation or ordinary-energy estimate is used. -/
theorem actual_geometry_main_first_norm_caps {α : Type*}[Fintype α][DecidableEq α]
    (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)(hZ : 1≤Z)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^(3:ℝ))(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin)) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    (l.1.1.absNorm:ℝ)≤Z^(4:ℝ) ∧ (l.1.2.absNorm:ℝ)≤Z^(4:ℝ) := by
  have hc:=(actual_geometry_norm_caps s R seed K Z ξ 3 hs hz₁ hz₂ hsource j.1.val 0).2
  have hd:=(actual_geometry_norm_caps s R seed K Z ξ 3 hs hz₁ hz₂ hsource j.1.val 1).2
  have h34 : Z^(3:ℝ)≤Z^(4:ℝ):=Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)
  exact ⟨hc.trans h34,hd.trans h34⟩

/-- The canonical ordinary datum retains the original ideals. Its true
first-child support, rather than the high-density ceiling, caps both
second ideals. Constants precede all labels, allocations and heights. -/
theorem eventual_actual_geometry_main_high_source_caps (N : ℕ)(b bs loss : ℝ)
    (hb : 1≤b)(hbs : 1≤bs)(hloss : 0<loss)(hloss1 : loss≤1) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{α : Type}[Fintype α][DecidableEq α]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(M amp ξ reserve t : ℝ)(hZ : 1<Z),
      Fintype.card α≤N → Endpoints b bs bs s → Squarefree seed →
      ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
      sourceRadius s≤Z^(3:ℝ) → volume s≤Z^(3:ℝ) →
      ∀(bin : ℤ×(Fin 5→ℤ))(χ : RayCharacter)(Q : Ideal O)(m : O)
        (j : GeometryMainSecondIndex reflected s R seed Z M amp ξ reserve b t (Fintype.card α) hZ bin),
      frozenCoefficient j.1.2.val (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin j.1.1.val) R s.ν s.W s.P≠0 →
      let l:=geometryFirstLabel s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin j.1.1.val
      let d:=geometryMainOrdinaryDatum reflected s R seed Z M amp ξ reserve b t (Fintype.card α) hZ bin hz₁ hz₂ χ Q m j
      (l.1.1.absNorm:ℝ)≤Z^(4:ℝ) ∧ (l.1.2.absNorm:ℝ)≤Z^(4:ℝ) ∧
        (d.C.absNorm:ℝ)≤Z^(4:ℝ) ∧ (d.D.absNorm:ℝ)≤Z^(4:ℝ) := by
  filter_upwards [eventual_geometry_child_source_cap N b bs loss hb hbs hloss] with Z hz
  refine ⟨hz.1,?_⟩
  intro α _ _ reflected s R seed M amp ξ reserve t hZ hn hend hseed hz₁ hz₂ hsource hvolume bin χ Q m j hf l d
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
  have hfirst:=actual_geometry_main_first_norm_caps s R seed (Z^M) Z ξ hK hZ.le hseed hz₁ hz₂ hsource bin j.1.1.val
  have hchild:=hz.2 s 3 hn hend hvolume
    (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin j.1.1.val) R j.1.2
    (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK bin j.1.1.val) t hf
  have hchild4 : sourceRadius (geometryLowFirstChild reflected s R seed (Z^M) Z ξ hK bin t j.1)≤Z^(4:ℝ) :=
    hchild.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
  let label:=geometryFirstLabel s R seed (Z^M) Z ξ hK bin j.1.1.val
  let Kmain:=firstMainRadius reflected (Z^M) (volume s) Z ξ (3*amp) reserve label
  let Tsec:=firstMainFourierScale reflected (Z^M) (volume s) Z ξ (3*amp) reserve b (Fintype.card α) label
  have hseed1:=actual_first_live_squarefree (geometryFirstSource s R seed (Z^M) Z ξ hK bin)
    (fun _=>logAnnulus) j.1.1.val j.1.1.property
  have hg:=actual_retained_block_gates (liveIndices j.1.2.val)
    (geometryLowFirstChild reflected s R seed (Z^M) Z ξ hK bin t j.1)
    (R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin j.1.1.val) j.1.1.val.2.1.val
    hseed1 hz₁ hz₂ Kmain Tsec Z ξ
    (first_main_radius_pos reflected (Z^M) (volume s) Z ξ (3*amp) reserve (zero_lt_one.trans hZ) label) j.2
  exact ⟨hfirst.1,hfirst.2,hg.2.2.1.trans hchild4,hg.2.2.2.trans hchild4⟩

/-- Original full-value nonzero selection supplies the supported first
allocation. No nonzero ordinary restricted block is required. -/
theorem eventual_actual_geometry_main_nonzero_high_source_caps (N : ℕ)(b bs loss : ℝ)
    (hb : 1≤b)(hbs : 1≤bs)(hloss : 0<loss)(hloss1 : loss≤1) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{α : Type}[Fintype α][DecidableEq α]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(M amp ξ reserve t : ℝ)(hZ : 1<Z),
      Fintype.card α≤N → Endpoints b bs bs s → Squarefree seed →
      ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
      sourceRadius s≤Z^(3:ℝ) → volume s≤Z^(3:ℝ) →
      ∀(bin : ℤ×(Fin 5→ℤ))(χ : RayCharacter)(Q : Ideal O)(m : O)
        (j : geometryMainNonzeroBlocks reflected s R seed Z M amp ξ reserve b t (Fintype.card α) hZ bin hz₁ hz₂),
      let l:=geometryFirstLabel s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin j.val.1.1.val
      let d:=geometryMainOrdinaryDatum reflected s R seed Z M amp ξ reserve b t (Fintype.card α) hZ bin hz₁ hz₂ χ Q m j.val
      (l.1.1.absNorm:ℝ)≤Z^(4:ℝ) ∧ (l.1.2.absNorm:ℝ)≤Z^(4:ℝ) ∧
        (d.C.absNorm:ℝ)≤Z^(4:ℝ) ∧ (d.D.absNorm:ℝ)≤Z^(4:ℝ) := by
  filter_upwards [eventual_actual_geometry_main_high_source_caps N b bs loss hb hbs hloss hloss1] with Z hz
  refine ⟨hz.1,?_⟩
  intro α _ _ reflected s R seed M amp ξ reserve t hZ hn hend hseed hz₁ hz₂ hsource hvolume bin χ Q m j
  exact hz.2 reflected s R seed M amp ξ reserve t hZ hn hend hseed hz₁ hz₂ hsource hvolume bin χ Q m j.val
    (Finset.mem_filter.mp j.property).2.1

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
