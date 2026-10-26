/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103StepScalar.Geometry
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103StepScalar
noncomputable section
open Record1252270103Finite

lemma compact_finite_margin {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (D : Set X) (hD : IsCompact D) (f : ι→X→ℝ)
    (hc : ∀i,ContinuousOn (f i) D) (hp : ∀i,∀x∈D,0<f i x) :
    ∃δ : ℝ,0<δ ∧ ∀i,∀x∈D,δ≤f i x := by
  classical
  have aux (S : Finset ι) : ∃δ : ℝ,0<δ ∧ ∀i∈S,∀x∈D,δ≤f i x := by
    induction S using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert i S hi ih =>
      obtain ⟨δ,hδ,hall⟩:=ih
      obtain ⟨γ,hγ,hγall⟩:=hD.exists_forall_le' (hc i) (hp i)
      refine ⟨min δ γ,lt_min hδ hγ,?_⟩
      intro j hj x hx
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact (min_le_right _ _).trans (hγall x hx)
      · exact (min_le_left _ _).trans (hall j hj x hx)
  obtain ⟨δ,hδ,hall⟩:=aux Finset.univ
  exact ⟨δ,hδ,fun i=>hall i (Finset.mem_univ _)⟩

lemma continuous_source_scalar (K : ℚ) (n low : Source) (j : Fin 16) :
    Continuous (fun x : ℝ×ℝ=>sourceScalarReal K n low x.1 j) := by
  fin_cases j <;> norm_num [sourceScalarReal,sourceAReal,sourceTReal,sourceFReal] <;> fun_prop

lemma continuous_source_density (n low : Source) (high : Option Source) (j : Fin 9) :
    Continuous (fun x : ℝ×ℝ=>sourceDensityWidthReal n low high x.1 x.2 j) := by
  cases high <;> fin_cases j <;>
    norm_num [sourceDensityWidthReal,sourceAReal,sourceTReal,sourceFReal] <;> fun_prop

/-- A single positive slack precedes every later finite slot/cardinality choice. -/
theorem nf_uniform_margin (n low : Source) (high : Option Source)
    (hv : SourceValid n low high) :
    ∃δ : ℝ,0<δ ∧ ∀b∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ),
      ∀ν∈Set.Icc (n.q:ℝ) (3/4),
      (∀j,δ≤sourceScalarReal (11243277/2500000) n low b j) ∧
      0≤sourceWeakReal n low b ∧
      ∀j,δ≤sourceDensityWidthReal n low high b ν j := by
  let D := Set.Icc (crossing n low:ℝ) (n.cap:ℝ) ×ˢ Set.Icc (n.q:ℝ) (3/4:ℝ)
  have hD : IsCompact D := isCompact_Icc.prod isCompact_Icc
  obtain ⟨δs,hδs,hs⟩:=compact_finite_margin D hD
    (fun j : Fin 16=>fun x : ℝ×ℝ=>sourceScalarReal (11243277/2500000) n low x.1 j)
    (fun j=>(continuous_source_scalar _ n low j).continuousOn)
    (fun j x hx=>(source_full_width_gates n low high hv hx.1 hx.2).1 j)
  obtain ⟨δd,hδd,hd⟩:=compact_finite_margin D hD
    (fun j : Fin 9=>fun x : ℝ×ℝ=>sourceDensityWidthReal n low high x.1 x.2 j)
    (fun j=>(continuous_source_density n low high j).continuousOn)
    (fun j x hx=>(source_full_width_gates n low high hv hx.1 hx.2).2.2 j)
  refine ⟨min δs δd,lt_min hδs hδd,?_⟩
  intro b hb ν hν
  exact ⟨fun j=>(min_le_left _ _).trans (hs j (b,ν) ⟨hb,hν⟩),
    (source_full_width_gates n low high hv hb hν).2.1,
    fun j=>(min_le_right _ _).trans (hd j (b,ν) ⟨hb,hν⟩)⟩

theorem seed_uniform_margin (n low : Source) (hv : SeedSourceValid n low) :
    ∃δ : ℝ,0<δ ∧ ∀b∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ),
      ∀ν∈Set.Icc (n.q:ℝ) (3/4),
      (∀j,δ≤sourceScalarReal (112445673/25000000) n low b j) ∧
      0≤sourceWeakReal n low b ∧
      ∀j : Fin 6,δ≤sourceDensityWidthReal n low none b ν (Fin.castLE (by decide) j) := by
  let D := Set.Icc (crossing n low:ℝ) (n.cap:ℝ) ×ˢ Set.Icc (n.q:ℝ) (3/4:ℝ)
  have hD : IsCompact D := isCompact_Icc.prod isCompact_Icc
  obtain ⟨δs,hδs,hs⟩:=compact_finite_margin D hD
    (fun j : Fin 16=>fun x : ℝ×ℝ=>sourceScalarReal (112445673/25000000) n low x.1 j)
    (fun j=>(continuous_source_scalar _ n low j).continuousOn)
    (fun j x hx=>(seed_full_width_gates n low hv hx.1 hx.2).1 j)
  obtain ⟨δd,hδd,hd⟩:=compact_finite_margin D hD
    (fun j : Fin 6=>fun x : ℝ×ℝ=>sourceDensityWidthReal n low none x.1 x.2 (Fin.castLE (by decide) j))
    (fun j=>(continuous_source_density n low none (Fin.castLE (by decide) j)).continuousOn)
    (fun j x hx=>(seed_full_width_gates n low hv hx.1 hx.2).2.2 j)
  refine ⟨min δs δd,lt_min hδs hδd,?_⟩
  intro b hb ν hν
  exact ⟨fun j=>(min_le_left _ _).trans (hs j (b,ν) ⟨hb,hν⟩),
    (seed_full_width_gates n low hv hb hν).2.1,
    fun j=>(min_le_right _ _).trans (hd j (b,ν) ⟨hb,hν⟩)⟩

theorem nf_uniform_mesh (n low : Source) (high : Option Source)
    (hv : SourceValid n low high) :
    ∃mesh : ℝ,0<mesh ∧ mesh≤1 ∧ ∀b∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ),
      ∀ν∈Set.Icc (n.q:ℝ) (3/4),
      (∀j,2*mesh≤sourceScalarReal (11243277/2500000) n low b j) ∧
      0≤sourceWeakReal n low b ∧
      ∀j,2*mesh≤sourceDensityWidthReal n low high b ν j := by
  obtain ⟨δ,hδ,hall⟩:=nf_uniform_margin n low high hv
  refine ⟨min 1 (δ/2),lt_min (by norm_num) (by linarith),min_le_left _ _,?_⟩
  intro b hb ν hν
  obtain ⟨hs,hw,hd⟩:=hall b hb ν hν
  have hm:=min_le_right (1:ℝ) (δ/2)
  exact ⟨fun j=>by linarith [hs j],hw,fun j=>by linarith [hd j]⟩

theorem seed_uniform_mesh (n low : Source) (hv : SeedSourceValid n low) :
    ∃mesh : ℝ,0<mesh ∧ mesh≤1 ∧ ∀b∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ),
      ∀ν∈Set.Icc (n.q:ℝ) (3/4),
      (∀j,2*mesh≤sourceScalarReal (112445673/25000000) n low b j) ∧
      0≤sourceWeakReal n low b ∧
      ∀j : Fin 6,2*mesh≤sourceDensityWidthReal n low none b ν (Fin.castLE (by decide) j) := by
  obtain ⟨δ,hδ,hall⟩:=seed_uniform_margin n low hv
  refine ⟨min 1 (δ/2),lt_min (by norm_num) (by linarith),min_le_left _ _,?_⟩
  intro b hb ν hν
  obtain ⟨hs,hw,hd⟩:=hall b hb ν hν
  have hm:=min_le_right (1:ℝ) (δ/2)
  exact ⟨fun j=>by linarith [hs j],hw,fun j=>by linarith [hd j]⟩
end
end QRH.Record1252270103StepScalar
#print axioms QRH.Record1252270103StepScalar.nf_uniform_margin
#print axioms QRH.Record1252270103StepScalar.seed_uniform_margin

#print axioms QRH.Record1252270103StepScalar.nf_uniform_mesh
#print axioms QRH.Record1252270103StepScalar.seed_uniform_mesh
