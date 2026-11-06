/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B003
import Candidate.Bundles.B007
import Candidate.Bundles.B009
import Candidate.Bundles.B019

/- BEGIN ORIGINAL Cycle25.Energy.Endpoint; sha256 529de648decd1beab08e1748e11806143cdffb0f611aa0f17dd15252a468f7d8 -/
section
                                        
                                   

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace Cycle25.Energy

open OAI OAI.SevenEighths
open HeckeFamily CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthSchedule
open CenteredMomentEnergyWidthRanges

local notation "O" => HeckeFamily.O

/-- Independent of the arithmetic family, slot count, profiles and target height. -/
def commonMesh (Mcap Bmask L ε : ℝ) : ℝ := fineMesh Mcap Bmask L (3 / 4) ε

theorem commonMesh_pos (Mcap Bmask L ε : ℝ) (hM : 0 ≤ Mcap)
    (hB : 0 ≤ Bmask) (hε : 0 < ε) : 0 < commonMesh Mcap Bmask L ε := by
  exact (bounds Mcap (finalSourceCap Mcap Bmask L ε) (3 / 4) ε hM
    (sourceCap_nonneg Mcap Bmask L hM hB _) (by norm_num) hε).2.2.2.2.1

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The original canonical ray-prime family with one common smooth slot profile.
The zero-slot input is supplied by the completed unconditional endpoint. -/
theorem terminal_positive_at
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap κ ε : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1 / 4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap)
    (hκlo : 7 / 10 ≤ κ) (hκhi : κ ≤ 3 / 4) (hε : 0 < ε)
    (hbeta : 51 / 100 ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2 * HeckeZeroSupremum.beta - 1 ≤ κ) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character, ∀ Q : Ideal O, Q ≤ M →
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
        PositiveAt (α := α) M H hH W bslot a b radial Bmask L
          (commonMesh Mcap Bmask L ε) lo hi Mcap ε κ Z η₀ Q J S C := by
  have hcert := Cycle25CenteredMomentEnergyCertifiedExistence.terminal_certificate
    (α := α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
    haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap hκlo hε hbeta hκbeta
  obtain ⟨J, S, hbound⟩ := certified_terminal (α := α) M H hH W bslot a b radial
    Bmask L lo hi Mcap κ ε hmask hMcap.le (by linarith) hε hcert
  have hmesh := compact_mesh_le Mcap Bmask L κ ε hMcap.le hmask hε hκlo hκhi
  refine ⟨J, S, ?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cz, Cp, _, hCp, hz⟩ := hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cp, hCp, ?_⟩
  filter_upwards [hz] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p
    X₁ X₂ hX₁ hX₂ hLX₁ hLX₂ hcapacity
  exact hZ.2.2 T θ w σ v t height hw (fun i => (hwL i).trans hmesh)
    hσlo hσhi hheight hv s hQ hs p X₁ X₂ hX₁ hX₂ hLX₁ hLX₂ hcapacity

end Cycle25.Energy

end
/- END ORIGINAL Cycle25.Energy.Endpoint -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.PlainInput; sha256 455f02ac8fdcd8454096b3d8cb547a3789974f71f64c1386308c65535cba7538 -/
section
                                                                
                              
                                                              
namespace OAI.SevenEighths.Cycle25ProbeDetectorPlainMarkedFineField
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter HeckeFamily CenteredMomentEnergyBands
open Cycle25ProbeFinalAssembly Cycle25CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalFixedRaySource Cycle25CenteredMomentDetectorPlainMomentParameters
open Cycle25CenteredMomentDetectorPlainSlotProfile

/-- One mesh works for all fixed detector inducing characters and the eventual
finite physical slot count. No improved terminal bound is used. -/
theorem terminal_plain_input {D : Cycle25.Weighted.MomentData}
    (S : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κplain : ℝ)
    (hk : 7/10≤κplain) (hk1 : κplain≤3/4)
    (hbeta : 51/100≤HeckeZeroSupremum.beta) (hκbeta : 2*HeckeZeroSupremum.beta-1≤κplain) :
    weighted_PositiveFineSourceInput S κplain (Cycle25.Energy.commonMesh 2 0 1 (weighted_stageError D)) := by
  intro bΦ hbΦ
  obtain ⟨J,controls,he⟩ := Cycle25.Energy.terminal_positive_at (α:=Fin D.N)
    S.modulus ⊤ le_top (fun x=>conj (S.W x)) 1 2 (1/4) (9/4) bΦ 0 1
    (33/50) (33/50) 2 κplain (weighted_stageError D)
    (by norm_num) (weighted_conjugate_source_support S)
    (HeckeInverseAmplification.conjugate_profile_smooth _ (S.W.smooth ⊤)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbΦ
    (by norm_num) (by norm_num) hk hk1 (weighted_fixed_parameters D).2.2.1 hbeta hκbeta
  refine ⟨J,controls,?_⟩
  intro η₀
  obtain ⟨C,hC,hbound⟩ := he η₀ (weighted_sourceFixedIdeal S) (weighted_sourceFixedIdeal_le_modulus S)
    (internalQ_ne_zero _ (weighted_sourceFixedIdeal_ne_zero S) η₀)
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) η₀)
    (inf_le_left.trans (weighted_sourceFixedIdeal_le_72 S))
  exact ⟨C,hC,hbound.mono (fun _ hz=>hz.2)⟩

open Cycle25ProbeDetectorPlainUnmarkedField CenteredMomentEnergyCappedWidthInduction
/-- Unmarked plain input extracted from the zero-slot part of the completed
Cycle25 certificate; fixed inducing characters are removed by the dictionary. -/
theorem terminal_zero_input {D : Cycle25.Weighted.MomentData}
    (S : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κplain : ℝ)
    (hk : 7/10≤κplain) (hk1 : κplain≤3/4)
    (hbeta : 51/100≤HeckeZeroSupremum.beta) (hκbeta : 2*HeckeZeroSupremum.beta-1≤κplain) :
    ∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (weighted_sourceFixedIdeal S) η₀) (1/4) (9/4) weighted_radialSupportUpper
        0 1 2 (D.t/4) U degree control A := by
  have hcert := Cycle25CenteredMomentEnergyCertifiedExistence.terminal_certificate (α:=Fin D.N)
    S.modulus ⊤ le_top (fun x=>conj (S.W x)) 1 2 (1/4) (9/4) weighted_radialSupportUpper
    0 1 (33/50) (33/50) 2 κplain (weighted_stageError D)
    (by norm_num) (weighted_conjugate_source_support S)
    (HeckeInverseAmplification.conjugate_profile_smooth _ (S.W.smooth ⊤))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) weighted_radialSupportUpper_spec.1
    (by norm_num) (by norm_num) hk (weighted_fixed_parameters D).2.2.1 hbeta hκbeta
  obtain ⟨J,controls,he⟩ := certified_terminal (α:=Fin D.N) S.modulus ⊤ le_top
    (fun x=>conj (S.W x)) 2 (1/4) (9/4) weighted_radialSupportUpper 0 1 (33/50) (33/50)
    2 κplain (weighted_stageError D) (by norm_num) (by norm_num) (by linarith)
    (weighted_fixed_parameters D).2.2.1 hcert
  refine ⟨J,controls,?_⟩
  intro η₀
  obtain ⟨Cz,Cp,hCz,hCp,hbound⟩ := he η₀ (weighted_sourceFixedIdeal S) (weighted_sourceFixedIdeal_le_modulus S)
    (internalQ_ne_zero _ (weighted_sourceFixedIdeal_ne_zero S) η₀)
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) η₀)
    (inf_le_left.trans (weighted_sourceFixedIdeal_le_72 S))
  exact ⟨Cz,hCz,hbound.mono (fun _ hz=>hz.2.1)⟩
end
end OAI.SevenEighths.Cycle25ProbeDetectorPlainMarkedFineField

end
/- END ORIGINAL Cycle25.Assembly.Count.PlainInput -/

/- BEGIN ORIGINAL Cycle25.Assembly.Mesh; sha256 d9856d9d22fde4759ec77150252e26257e2877b715334a53691dd86be0d261d2 -/
section
                              

noncomputable section
namespace Cycle25

/-- One mesh for both the physical numerator and the marked detector family. -/
def sourceMesh (t : ℝ) : ℝ := Energy.commonMesh 2 0 1 (t/4)

theorem sourceMesh_pos {t : ℝ} (ht : 0 < t) : 0 < sourceMesh t := by
  exact Energy.commonMesh_pos 2 0 1 (t/4) (by norm_num) (by norm_num) (by positivity)

end Cycle25

end
/- END ORIGINAL Cycle25.Assembly.Mesh -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.ActualMoments; sha256 b4fac19450ff5b268fd81946730cf65dedc0722fa9154078a3ed7bc3c53d40fc -/
section
                                              
                                        
                            
                                        

namespace OAI.SevenEighths.Cycle25ProbeFinalAssembly
noncomputable section
open scoped Classical
open Filter HeckeFamily
open Cycle25ProbeDetectorPlainMarkedFineField

/-- Fresh inverse detector parameters for the variable-κ count. -/
theorem weighted_fresh_count_parameters {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) :
    Nonempty (Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t) := by
  exact Cycle25ProbeHighRowFamily.exists_count_parameters F.modulus ⊤ le_top F.S F.w
    F.smooth F.compact F.positive_support (fun x=>(F.bounded x).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support
    (fun x=>(F.bounded x).2) D.t D.t_pos

/-- Actual physical source moments from the completed energy endpoint, on the
same mesh used by the physical numerator. -/
theorem weighted_actual_source_moments {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) (κplain : ℝ)
    (hk : 7/10≤κplain) (hk1 : κplain≤3/4)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤κplain)
    (counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t)
    (hfine : ∀j,D.ell j≤Cycle25.sourceMesh D.t/200) :
    ∃J:ℝ,0≤J ∧ ∀η:Character,∃C:ℝ,0<C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        weighted_SourceMomentBound F κplain counts η Z τ
          (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
  exact Cycle25ProbeFinalAssemblyCertifiedBands.weighted_source_moments F κplain hk1
    counts (Cycle25.sourceMesh D.t) (Cycle25.sourceMesh_pos D.t_pos) hfine
    (terminal_plain_input F κplain hk hk1 hbeta hκbeta)
    (terminal_zero_input F κplain hk hk1 hbeta hκbeta)
end
end OAI.SevenEighths.Cycle25ProbeFinalAssembly

end
/- END ORIGINAL Cycle25.Assembly.Count.ActualMoments -/
