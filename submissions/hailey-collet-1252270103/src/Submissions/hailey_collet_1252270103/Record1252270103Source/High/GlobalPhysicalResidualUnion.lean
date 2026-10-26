/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The residual ideal stays fixed while a joint row family is estimated. Its
full padded union is paid only afterwards by the genuine harmonic mass. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularResidualSelection
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve
local notation "O"=>HeckeFamily.O

theorem residual_union_reassembly {Row:Type*} (rows:Finset Row)
    (Ls:Row→Finset (Ideal O)) (f:Row→Ideal O→ℝ) :
    (∑r∈rows,∑L∈Ls r,f r L)=
      ∑L∈rows.biUnion Ls,∑r∈rows.filter (fun r=>L∈Ls r),f r L := by
  classical
  have hex (r:Row)(hr:r∈rows):
      (rows.biUnion Ls).filter (fun L=>L∈Ls r)=Ls r := by
    ext L
    simp only [Finset.mem_filter,Finset.mem_biUnion]
    exact ⟨fun h=>h.2,fun h=>⟨⟨r,hr,h⟩,h⟩⟩
  calc
    _=∑r∈rows,∑L∈rows.biUnion Ls,if L∈Ls r then f r L else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [←Finset.sum_filter,hex r hr]
    _=_ := by rw [Finset.sum_comm];simp only [Finset.sum_filter]

theorem residual_union_cap {Row:Type*} (rows:Finset Row)
    (Ls:Row→Finset (Ideal O)) (Z B:ℝ)
    (hcap:∀r∈rows,∀L∈Ls r,(L.absNorm:ℝ)≤Z^B) :
    ∀L∈rows.biUnion Ls,(L.absNorm:ℝ)≤Z^B := by
  intro L hL
  obtain ⟨r,hr,hL⟩:=Finset.mem_biUnion.mp hL
  exact hcap r hr L hL

/-- The scalar E is supplied by one common estimate for every fixed L,
before the residual union is summed. No maximum over row-dependent L or
unweighted cardinality bound for this padded pool is used. -/
theorem uniform_fixed_residual_collection (B δ:ℝ)(hB:0≤B)(hδ:0<δ) :
    ∃H:ℝ,0<H ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(ε E:ℝ),0≤ε→0≤E→
      ∀{Row:Type*}(rows:Finset Row)(Ls:Row→Finset (Ideal O))(f:Row→Ideal O→ℝ),
      (∀r∈rows,∀L∈Ls r,Squarefree L)→
      (∀r∈rows,∀L∈Ls r,(L.absNorm:ℝ)≤Z^B)→
      (∀L∈rows.biUnion Ls,(∑r∈rows.filter (fun r=>L∈Ls r),f r L)≤
        ((L.absNorm:ℝ)^ε/(L.absNorm:ℝ))*E)→
      (∑r∈rows,∑L∈Ls r,f r L)≤H*Z^(δ+B*ε)*E := by
  obtain ⟨H,hH,hmass⟩:=RegularResidualSelection.full_squarefree_seed_mass B δ hB hδ
  refine ⟨H,hH,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ε E hε hE Row rows Ls f hsf hcap hfixed
  have hsf' (L:Ideal O)(hL:L∈rows.biUnion Ls):Squarefree L := by
    obtain ⟨r,hr,hL⟩:=Finset.mem_biUnion.mp hL
    exact hsf r hr L hL
  rw [residual_union_reassembly]
  calc
    _≤∑L∈rows.biUnion Ls,((L.absNorm:ℝ)^ε/(L.absNorm:ℝ))*E:=Finset.sum_le_sum hfixed
    _=(∑L∈rows.biUnion Ls,(L.absNorm:ℝ)^ε/(L.absNorm:ℝ))*E:=(Finset.sum_mul ..).symm
    _≤_:=mul_le_mul_of_nonneg_right
      (hZ.2 ε hε (rows.biUnion Ls) hsf' (residual_union_cap rows Ls Z B hcap)) hE

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.residual_union_reassembly
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.residual_union_cap
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.uniform_fixed_residual_collection
