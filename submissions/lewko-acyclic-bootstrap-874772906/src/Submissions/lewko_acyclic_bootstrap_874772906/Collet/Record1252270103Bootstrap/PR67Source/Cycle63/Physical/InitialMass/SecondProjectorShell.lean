import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryZeroPayment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondRetainedContraction
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve UniqueFactorizationMonoid CompletedGauss
open CenteredMomentWholeDivisorShell CenteredMomentMobiusRegroup
open CenteredMomentCanonicalFirst
open CenteredMomentSecondSectorColumns CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceLiveColumn
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
local instance projectorShellSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Union before taking norm dyads: its size never counts the moving labels. -/
def sharedProjectors {Label : Type*} [Fintype Label] (Ds : Label→Finset (Ideal O)) :
    Finset (Ideal O) := Finset.univ.biUnion Ds

lemma mem_sharedProjectors {Label : Type*} [Fintype Label]
    (Ds : Label→Finset (Ideal O)) (l : Label) (D : Ideal O) (hD : D∈Ds l) :
    D∈sharedProjectors Ds := Finset.mem_biUnion.mpr ⟨l,Finset.mem_univ _,hD⟩

/-- Squarefree projectors have their literal common dyadic shell, with T≥1. -/
theorem shared_projector_shell_gates {Label : Type*} [Fintype Label]
    (Ds : Label→Finset (Ideal O)) (n : ℤ) (D : Ideal O)
    (hD : D∈shell (sharedProjectors Ds) n) :
    Squarefree D ∧ D≠0 ∧ dyadicScale n≤(D.absNorm:ℝ) ∧
      (D.absNorm:ℝ)<2*dyadicScale n := by
  have h:=shell_member_data _ _ _ hD
  exact ⟨h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩

/-- Exact common-shell reindexing retains the per-label membership filter. -/
theorem shared_projector_shell_sum {Label : Type*} [Fintype Label]
    (Ds : Label→Finset (Ideal O)) (hs : ∀l D,D∈Ds l→Squarefree D)
    (cost : Label→ Ideal O→ℝ) :
    (∑l,∑D∈Ds l,cost l D)=
      ∑n∈selectedShells (sharedProjectors Ds),∑l,
        ∑D∈shell (sharedProjectors Ds) n,if D∈Ds l then cost l D else 0 := by
  have hpoint (l : Label) : (∑D∈Ds l,cost l D)=
      ∑n∈selectedShells (sharedProjectors Ds),
        ∑D∈shell (sharedProjectors Ds) n,if D∈Ds l then cost l D else 0 := by
    have hsum := sum_norm_moebius_shells (sharedProjectors Ds)
      (fun D=>if D∈Ds l then cost l D else 0)
    have hm (D : Ideal O) (hD : D∈Ds l) : ‖(moebius D:ℂ)‖=1 :=
      squarefree_moebius_norm D (hs l D hD)
    have hleft : (∑D∈sharedProjectors Ds,‖(moebius D:ℂ)‖*
        (if D∈Ds l then cost l D else 0))=∑D∈Ds l,cost l D := by
      simp only [mul_ite,mul_zero]
      rw [←Finset.sum_filter]
      apply (Finset.sum_congr ?_ ?_)
      · ext D
        simp only [Finset.mem_filter]
        exact ⟨fun h=>h.2,fun h=>⟨mem_sharedProjectors Ds l D h,h⟩⟩
      · intro D hD
        rw [hm D hD,one_mul]
    rw [hleft] at hsum
    apply hsum.trans
    refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun D hD => ?_
    by_cases hd : D∈Ds l
    · simp only [hd,ite_true,hm D hd,one_mul]
    · simp only [hd,ite_false,mul_zero]
  simp_rw [hpoint]
  exact Finset.sum_comm

/-- Enlarge a positive cost to the shared shell, without paying label count. -/
theorem shared_projector_shell_sum_le {Label : Type*} [Fintype Label]
    (Ds : Label→Finset (Ideal O)) (hs : ∀l D,D∈Ds l→Squarefree D)
    (cost : Label→ Ideal O→ℝ) (hc : ∀l D,0≤ cost l D) :
    (∑l,∑D∈Ds l,cost l D)≤
      ∑n∈selectedShells (sharedProjectors Ds),∑l,∑D∈shell (sharedProjectors Ds) n,cost l D := by
  rw [shared_projector_shell_sum Ds hs cost]
  refine Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun l hl => Finset.sum_le_sum fun D hD => ?_
  split_ifs
  · exact le_rfl
  · exact hc l D

/-- Constants precede every finite family. One extra small power pays the
union of projector norm dyads; the four source-block dyads are separate. -/
theorem shared_projector_shell_subpower (L ε : ℝ) (hL : 0≤L) (he : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀{Label : Type*}[Fintype Label](Ds : Label→Finset (Ideal O)),
      (∀l D,D∈Ds l→(D.absNorm:ℝ)≤Z^L) →
      ((selectedShells (sharedProjectors Ds)).card:ℝ)≤C*Z^ε := by
  obtain ⟨C,hC,hbound⟩:=selected_card_subpower L ε hL he
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro Label _ Ds hcap
  apply hz.2
  intro D hD _
  obtain ⟨l,_,hl⟩:=Finset.mem_biUnion.mp hD
  exact hcap l D hl

/-- A scalar estimate for each entire shared shell pays the full projector
sum. No allocation or source is selected after an individual row. -/
theorem shared_projector_shell_payment (L ε : ℝ) (hL : 0≤L) (he : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀{Label : Type*}[Fintype Label](Ds : Label→Finset (Ideal O)),
      (∀l D,D∈Ds l→Squarefree D) →
      (∀l D,D∈Ds l→(D.absNorm:ℝ)≤Z^L) →
      ∀(cost : Label→ Ideal O→ℝ)(E : ℝ),(∀l D,0≤ cost l D) → 0≤E →
      (∀n∈selectedShells (sharedProjectors Ds),
        (∑l,∑D∈shell (sharedProjectors Ds) n,cost l D)≤E) →
      (∑l,∑D∈Ds l,cost l D)≤C*Z^ε*E := by
  obtain ⟨C,hC,hbound⟩:=shared_projector_shell_subpower L ε hL he
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro Label _ Ds hs hcap cost E hc hE hpay
  apply (shared_projector_shell_sum_le Ds hs cost hc).trans
  calc
    _≤∑n∈selectedShells (sharedProjectors Ds),E := Finset.sum_le_sum (fun n hn=>hpay n hn)
    _=((selectedShells (sharedProjectors Ds)).card:ℝ)*E := by simp
    _≤_ := mul_le_mul_of_nonneg_right (hz.2 Ds hcap) hE

/-- Literal second divisors are divisors of padded sector ideals, so the
bound covers zero coefficients as well as retained ordinary blocks. -/
theorem second_block_projector_norm (s : SecondBlockSource) (Y : ℝ)
    (hpool : ∀I∈s.pool,(I.absNorm:ℝ)≤Y) (D : Ideal O) (hD : D∈s.divisors) :
    D≠0 ∧ (D.absNorm:ℝ)≤Y := by
  apply divisorPool_nonzero_norm Finset.univ
    (fun J : sectorPool s.D s.hD.1 s.pool=>(J:Ideal O))
    (fun J _=>(sectorPool_supported s.D s.hD.1 s.pool J).1) Y _ D hD
  intro J _
  have hj := (mem_residualPool s.D s.hD.1 (supportedColumns s.pool) J.val).mp
    (Finset.mem_filter.mp J.property).1
  have hne : s.D*J.val≠0 := (Finset.mem_filter.mp hj).2.1
  exact (CenteredMomentFirstSourceConductorCaps.divisor_norm_le J.val (s.D*J.val) hne
    (dvd_mul_left _ _)).trans (hpool _ (Finset.mem_filter.mp hj).1)

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Actual datum projector cap from its literal independent source pools. -/
theorem second_datum_projector_cap (d : SecondInputDatum α) (N : ℕ) (Z U : ℝ)
    (hN : Fintype.card d.slots≤N)(hZ : 1≤Z)(hU : 0≤U)
    (hpool : ∀i I,I∈d.input.pools i→(I.absNorm:ℝ)≤Z^U)
    (D : Ideal O) (hD : D∈d.block.divisors) :
    D≠0 ∧ (D.absNorm:ℝ)≤Z^(((N:ℝ)+2)*U) :=
  second_block_projector_norm d.block _ (actual_finite_pool_cap d.input N Z U hN hZ hU hpool) D hD

/-- The common-allocation child keeps original slot pools and takes literal
ideal quotients for its plains; quotient norms cannot grow. -/
theorem actual_child_pool_cap {ι : Type*}[Fintype ι][DecidableEq ι]
    (s : Input ι)(C R : Ideal O)(B : actualAllocations s.pools C)(τ : Character)(t Y : ℝ)
    (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Y) :
    ∀i I,I∈(child s C R B τ t).pools i→(I.absNorm:ℝ)≤Y := by
  intro i I hI
  cases i with
  | inl j => exact hpool (Sum.inl j.val) I hI
  | inr j =>
    fin_cases j
    · have hj := (mem_residualPool (B.val (Sum.inr 0)) (alloc_ne s C B _) s.plain₁ I).mp hI
      have hne := (child s C R B τ t).pools_ne _ I hI
      apply (CenteredMomentFirstSourceConductorCaps.divisor_norm_le I _
        (mul_ne_zero (alloc_ne s C B _) hne) (dvd_mul_left _ _)).trans
      exact hpool (Sum.inr 0) _ hj
    · have hj := (mem_residualPool (B.val (Sum.inr 1)) (alloc_ne s C B _) s.plain₂ I).mp hI
      have hne := (child s C R B τ t).pools_ne _ I hI
      apply (CenteredMomentFirstSourceConductorCaps.divisor_norm_le I _
        (mul_ne_zero (alloc_ne s C B _) hne) (dvd_mul_left _ _)).trans
      exact hpool (Sum.inr 1) _ hj

/-- Every selected shared shell has its genuine common scale in [1,Z^L]. -/
theorem shared_projector_shell_scale {Label : Type*}[Fintype Label]
    (Ds : Label→Finset (Ideal O))(Z L : ℝ)
    (hcap : ∀l D,D∈Ds l→(D.absNorm:ℝ)≤Z^L)
    (n : ℤ)(hn : n∈selectedShells (sharedProjectors Ds)) :
    1≤dyadicScale n ∧ dyadicScale n≤Z^L := by
  apply selected_scale_bounds (sharedProjectors Ds) (Z^L) _ n hn
  intro D hD _
  obtain ⟨l,_,hl⟩:=Finset.mem_biUnion.mp hD
  exact hcap l D hl

/-- First projector union with its exact retained arithmetic identity. -/
def firstProjectorSet {ι : Type*}[Fintype ι]
    (s : Input ι)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)(key : ℤ×(Fin 5→ℤ))
    (rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))) :
    Finset (Ideal O) := rows.image (fun j=>j.2.1.val)

theorem actual_first_projector_set_cap {ι : Type*}[Fintype ι][DecidableEq ι]
    (s : Input ι)(N : ℕ)(R seed : Ideal O)(K Z ξ U : ℝ)(hK : 0<K)
    (hN : Fintype.card ι≤N)(hZ : 1≤Z)(hU : 0≤U)
    (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^U)
    (key : ℤ×(Fin 5→ℤ))
    (rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))) :
    ∀D∈firstProjectorSet s R seed K Z ξ hK key rows,(D.absNorm:ℝ)≤Z^(((N:ℝ)+2)*U) := by
  intro D hD
  obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hD
  exact actual_geometry_projector_cap s N R seed K Z ξ U hK hN hZ hU hpool key j

/-- The additional first-projector shell count is uniform before sources,
labels, allocation choices and Mellin heights. -/
theorem actual_first_projector_shell_subpower (N : ℕ)(U ε : ℝ)
    (hU : 0≤U)(he : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀{ι : Type*}[Fintype ι][DecidableEq ι](s : Input ι),Fintype.card ι≤N →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^U) →
      ∀(R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(key : ℤ×(Fin 5→ℤ))
        (rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))),
      ((selectedShells (firstProjectorSet s R seed K Z ξ hK key rows)).card:ℝ)≤C*Z^ε := by
  obtain ⟨C,hC,hbound⟩:=selected_card_subpower (((N:ℝ)+2)*U) ε (by positivity) he
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ _ s hN hpool R seed K ξ hK key rows
  exact hz.2 _ (fun D hD _=>actual_first_projector_set_cap s N R seed K Z ξ U hK
    hN hz.1.le hU hpool key rows D hD)

/-- Ordinary blocks have exactly the same projector cap, even if their
restricted physical block vanishes. -/
theorem ordinary_second_projector_cap (d : SecondInputDatum α)(N : ℕ)(Z U : ℝ)
    (hN : Fintype.card d.slots≤N)(hZ : 1≤Z)(hU : 0≤U)
    (hpool : ∀i I,I∈d.input.pools i→(I.absNorm:ℝ)≤Z^U)
    (χ : RayFourExpansion.RayCharacter)(Q : Ideal O)(m : O)(D : Ideal O)
    (hD : D∈(ordinarySecondDatum d χ Q m).block.divisors) :
    D≠0 ∧ (D.absNorm:ℝ)≤Z^(((N:ℝ)+2)*U) :=
  second_datum_projector_cap d N Z U hN hZ hU hpool D hD

/-- Uniform shared second-projector shell count for all moving block labels,
using literal source-pool caps and no arithmetic-label cardinality. -/
theorem actual_second_projector_shell_subpower (N : ℕ)(U ε : ℝ)
    (hU : 0≤U)(he : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀{Label : Type*}[Fintype Label](d : Label→SecondInputDatum α),
      (∀l,Fintype.card (d l).slots≤N) →
      (∀l i I,I∈(d l).input.pools i→(I.absNorm:ℝ)≤Z^U) →
      ((selectedShells (sharedProjectors (fun l=>(d l).block.divisors))).card:ℝ)≤C*Z^ε := by
  obtain ⟨C,hC,hbound⟩:=shared_projector_shell_subpower (((N:ℝ)+2)*U) ε (by positivity) he
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro Label _ d hN hpool
  exact hz.2 _ (fun l D hD=>(second_datum_projector_cap (d l) N Z U (hN l)
    hz.1.le hU (hpool l) D hD).2)

/-- Exact per-label subset of the common shell. Allocator dependence on D
may remain in cost; neither the label nor the projector is identified. -/
def sharedLabelProjectorShell {Label : Type*}[Fintype Label]
    (Ds : Label→Finset (Ideal O))(l : Label)(n : ℤ) : Finset (Ideal O) :=
  (shell (sharedProjectors Ds) n).filter (fun D=>D∈Ds l)

theorem shared_label_projector_shell_gates {Label : Type*}[Fintype Label]
    (Ds : Label→Finset (Ideal O))(l : Label)(n : ℤ)(D : Ideal O)
    (hD : D∈sharedLabelProjectorShell Ds l n) :
    D∈Ds l ∧ Squarefree D ∧ dyadicScale n≤(D.absNorm:ℝ) ∧
      (D.absNorm:ℝ)<2*dyadicScale n := by
  obtain ⟨hd,hl⟩:=Finset.mem_filter.mp hD
  have hg:=shared_projector_shell_gates Ds n D hd
  exact ⟨hl,hg.1,hg.2.2⟩

theorem shared_label_projector_shell_sum {Label : Type*}[Fintype Label]
    (Ds : Label→Finset (Ideal O))(hs : ∀l D,D∈Ds l→Squarefree D)
    (cost : Label→ Ideal O→ℝ) :
    (∑l,∑D∈Ds l,cost l D)=
      ∑n∈selectedShells (sharedProjectors Ds),∑l,
        ∑D∈sharedLabelProjectorShell Ds l n,cost l D := by
  rw [shared_projector_shell_sum Ds hs cost]
  simp only [sharedLabelProjectorShell,Finset.sum_filter]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
