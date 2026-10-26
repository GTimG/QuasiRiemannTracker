/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Tuple mass and support of an actual finite modifier; no column-norm contraction. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledFirstData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceLiveColumn
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentSourceZeroEnergy
open CenteredMomentSourceProfileMassUniform CenteredMomentSourceProfileMass
open CenteredMomentExceptionalAmplitudePair CenteredMomentNaturalRadialCutoff
open CenteredMomentSourceInputTailUniform CenteredMomentAddedZeroUniform
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance coupledFirstBoundsDecidable : DecidableEq (ι⊕Fin 2):=Classical.decEq _

omit [DecidableEq ι] in
theorem input_mass (hi:ι→ℝ)(whi:ℝ)(hhi:∀i,0≤hi i)(hwhi:0≤whi)
    (s:Input ι)(modifier:Tuple ι→ℂ)(L:ℝ)(hL:0≤L)
    (hmod:∀v∈Fintype.piFinset s.pools,‖modifier v‖≤L)(W₁ W₂:𝓢(ℝ,ℂ))(wlo:ℝ)(hwlo:0<wlo)
    (he₁:s.W₁=W₁)(he₂:s.W₂=W₂)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hshi:∀i,s.hi i≤hi i)(R seed:Ideal O):
    (∑I∈finiteColumns (Fintype.piFinset s.pools),‖coefficient s modifier R seed I‖)≤
      (2*128^(Fintype.card ι+2)*(∏i,hi i)*whi^2)*(L*plainControl s W₁ W₂)*volume s.toData:=by
  have hz (i:ι):s.W i 0=0:=by
    by_contra hn
    exact (not_le_of_gt (s.lo_pos i)) (s.support i hn).1
  have hzW (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (hs hn).1
  have hm:=profile_mass_explicit s.W W₁ W₂ hi s.M whi whi
    (SchwartzMap.seminorm ℝ 0 0 W₁) (SchwartzMap.seminorm ℝ 0 0 W₂)
    hhi hwhi hwhi (fun i=>zero_le_one.trans (s.M_ge_one i))
    (apply_nonneg _ _) (apply_nonneg _ _) hz (hzW W₁ hs₁) (hzW W₂ hs₂)
    (fun i x hx=>((s.support i hx).2).trans (hshi i))
    (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2) s.W_bound
    (SchwartzMap.norm_le_seminorm ℝ W₁) (SchwartzMap.norm_le_seminorm ℝ W₂)
    R s.ν s.ν_bound s.P s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed
    s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero
    rfl s.same_product (Fintype.piFinset s.pools)
  have hc:=finiteColumnCoefficient_mass (Fintype.piFinset s.pools)
    (tupleCoefficient s modifier R seed)
  have htuple : (∑v∈Fintype.piFinset s.pools,‖tupleCoefficient s modifier R seed v‖)≤
      L*(∑v∈Fintype.piFinset s.pools,
        ‖profileCoefficient R s.ν s.W s.P W₁ W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v‖) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    dsimp only [tupleCoefficient]
    rw [he₁,he₂,norm_mul]
    exact mul_le_mul_of_nonneg_right (hmod v hv) (norm_nonneg _)
  apply (hc.trans (htuple.trans (mul_le_mul_of_nonneg_left hm hL))).trans_eq
  simp only [map_one,Nat.cast_one,one_mul,div_one,plainControl,volume]
  ring

omit [DecidableEq ι] in
lemma input_column_bound (hi:ι→ℝ)(whi:ℝ)
    (s:Input ι)(modifier:Tuple ι→ℂ)(W₁ W₂:𝓢(ℝ,ℂ))(wlo:ℝ)(hwlo:0<wlo)
    (he₁:s.W₁=W₁)(he₂:s.W₂=W₂)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hshi:∀i,s.hi i≤hi i)(R seed I:Ideal O)(hn:coefficient s modifier R seed I≠0):
    (Ideal.absNorm I:ℝ)≤((∏i,hi i)*whi^2)*volume s.toData:=by
  obtain ⟨v,hv,hv0,hvI⟩:=finiteColumnCoefficient_witness _ _ I hn
  have hz (i:ι):s.W i 0=0:=by
    by_contra h
    exact (not_le_of_gt (s.lo_pos i)) (s.support i h).1
  have hzW (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra h
    exact (not_le_of_gt hwlo) (hs h).1
  have hv0 := tuple_nonzero s modifier R seed v hv0
  rw [he₁,he₂] at hv0
  have hp:=profileCoefficient_product_bound R s.ν s.W s.P hi W₁ W₂ whi whi
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed
    s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero rfl s.same_product
    hz (hzW W₁ hs₁) (hzW W₂ hs₂) (fun i x hx=>((s.support i hx).2).trans (hshi i))
    (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2) v hv0
  rw [hvI] at hp
  apply hp.2.trans_eq
  simp only [map_one,Nat.cast_one,one_mul,div_one,volume]
  ring


end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.input_mass
