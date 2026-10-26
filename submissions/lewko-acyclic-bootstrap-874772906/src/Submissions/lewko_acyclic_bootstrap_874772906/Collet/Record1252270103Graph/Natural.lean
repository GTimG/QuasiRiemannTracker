/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform natural terminal transported to the literal global affine source. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Graph.GraphContract
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.NaturalSource
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Graph
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths QRH.Record12518109Source QRH.Record12518109Existence
open HeckeFamily CenteredMomentNaturalFixedRaySource Filter QuadraticInitialBound CenteredMomentEnergyBands
open Record1252270103Bootstrap.NaturalSource
local notation "O" => HeckeFamily.O
local instance (rayM:Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
 Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

theorem natural_global_source (K:ℝ) (hKlo:21/5≤K) (hKhi:K≤9/2)
 (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
 (hcap:6*(2*HeckeZeroSupremum.beta-1)≤K) :
 Record1252270103Source.GlobalSource 1 K (11/200) := by
 intro ε hε
 let e:ℝ := min ε 1
 have he:0<e := lt_min hε zero_lt_one
 have heone:e≤1 := min_le_right _ _
 let mesh := Cycle25.Energy.commonMesh (1+1) 0 (1+1) (e/2)
 have hmesh:0<mesh := Cycle25.Energy.commonMesh_pos _ _ _ _ (by norm_num) (by norm_num) (by positivity)
 refine ⟨mesh,hmesh,?_⟩
 intro α _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
 obtain ⟨degree,S,hsource⟩ := natural_initial_uniform (α:=α) (Label:=Unit) rayM H hH (K/6) K
   (by linarith) (by linarith) (by linarith) (by linarith)
   W 1 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 e
   (by norm_num) hWs hW (by norm_num) (by norm_num) (by norm_num) (by norm_num)
   (by linarith) le_rfl (by norm_num) le_rfl he heone hbeta (fun _:Unit=>η)
 obtain ⟨C,hC,hbound⟩ := hsource η₀ Q hQray hQ0 hQt hQ72
 refine ⟨degree,S,C,hC,?_⟩
 filter_upwards [hbound] with Z hz
 intro T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi
   Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hadm
 have hc:NaturalCapacity K (length Z X₁) (length Z X₂) (∑i,w i) M := by
  simpa [NaturalCapacity,Record1252270103Source.globalFace] using hadm.2.2.2.2.2.2
 have hn := (hz.2 ()) T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi
   Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hc
 apply hn.trans
 apply mul_le_mul_of_nonneg_left
  (Real.rpow_le_rpow_of_exponent_le hz.1.le (by dsimp [e];linarith [min_le_left ε 1]))
 have hd := diagonalControl_nonneg Φ
 positivity
end
end QRH.Record1252270103Graph
#print axioms QRH.Record1252270103Graph.natural_global_source
