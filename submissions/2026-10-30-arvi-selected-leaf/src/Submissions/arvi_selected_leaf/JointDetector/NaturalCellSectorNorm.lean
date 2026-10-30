/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.NaturalTableNorm
import Submissions.arvi_selected_leaf.JointDetector.NaturalCellFibreNorm
import Submissions.arvi_selected_leaf.JointDetector.NaturalRootBudget
import Submissions.arvi_selected_leaf.JointDetector.NaturalSectorBound

/-! Actual cell-family inputs to the finite near-sector estimate. All
counts and rays are inherited from the selected original tuple family. -/
namespace Qrh.JointDetector.NaturalSelectedNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open ConcretePrimeRowBridge CompletedGauss CenteredExceptionalCount IdealMobiusDivisorSum ConcreteTraceCRT
open NaturalSharedTables NaturalPairPackets NaturalTupleIdentity NaturalNearPackets TableGeometry
local notation "O" => ActualEisensteinCubic.O

theorem cell_higher_cardinal_bounds (ε : ℝ) (hε : 0 < ε) :
    ∃ Ch : ℝ,0 < Ch ∧ ∀ (F : Finset ColourTuple)
      (hF : ∀ c ∈ F,∀ j,Admissible (c j))
      (hpF : ∀ c ∈ F,Pairwise (fun j l => IsCoprime (c j) (c l)))
      (Y : ℝ) (k : TuplePartition.Key Y) (g : SharedTable),
      (∀ j l,g j l ≠ 0) →
      Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)) →
      1 ≤ Y → (∀ c ∈ F,((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y) →
      ((((leftFamily (TuplePartition.cell F Y k) g).image higherTuple).card:ℝ) ≤
        Ch*(16*(V k/((Ideal.absNorm (TableBudget.H g):ℝ)*
          (Ideal.absNorm (TableBudget.J g):ℝ)*(Ideal.absNorm (TableBudget.F g):ℝ))))*Y^ε) ∧
      ((((rightFamily (TuplePartition.cell F Y k) g).image higherTuple).card:ℝ) ≤
        Ch*(16*(V k/((Ideal.absNorm (TableBudget.H g):ℝ)*
          (Ideal.absNorm (TableBudget.J g):ℝ)*(Ideal.absNorm (TableBudget.E g):ℝ))))*Y^ε) := by
  obtain ⟨Cl,hCl,hleft⟩ := leftFamily_higher_cardinal ε hε
  obtain ⟨Cr,hCr,hright⟩ := rightFamily_higher_cardinal ε hε
  refine ⟨Cl+Cr,add_pos hCl hCr,?_⟩
  intro F hF hpF Y k g hgn hgp hY hheight
  have hVpos := V_pos k
  let Fc := TuplePartition.cell F Y k
  have hf : ∀ c ∈ Fc,∀ j,Admissible (c j) := fun c hc => hF c (Finset.mem_filter.mp hc).1
  have hp : ∀ c ∈ Fc,Pairwise (fun j l => IsCoprime (c j) (c l)) :=
    fun c hc => hpF c (Finset.mem_filter.mp hc).1
  have hh : ∀ c ∈ Fc,((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y :=
    fun c hc => hheight c (Finset.mem_filter.mp hc).1
  have hn := cell_higher_norm F Y k hF hheight
  have hl := hleft Fc hf hp g hgn hgp Y (16*V k) hY (by positivity [V_pos k]) hh hn
  have hr := hright Fc hf hp g hgn hgp Y (16*V k) hY (by positivity [V_pos k]) hh hn
  simp only [map_mul,Nat.cast_mul] at hl hr
  constructor
  · apply hl.trans
    have hc : Cl ≤ Cl+Cr := by linarith
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ 16*V k/
        ((Ideal.absNorm (TableBudget.H g):ℝ)*(Ideal.absNorm (TableBudget.J g):ℝ)*
          (Ideal.absNorm (TableBudget.F g):ℝ)))) (Real.rpow_nonneg (by linarith : 0 ≤ Y) ε)
    convert hmul using 1 <;> ring
  · apply hr.trans
    have hc : Cr ≤ Cl+Cr := by linarith
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ 16*V k/
        ((Ideal.absNorm (TableBudget.H g):ℝ)*(Ideal.absNorm (TableBudget.J g):ℝ)*
          (Ideal.absNorm (TableBudget.E g):ℝ)))) (Real.rpow_nonneg (by linarith : 0 ≤ Y) ε)
    convert hmul using 1 <;> ring

theorem cell_residual_rays (F : Finset ColourTuple) (Y : ℝ) (k : TuplePartition.Key Y)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j l => IsCoprime (c j) (c l)))
    (g : SharedTable) (hgn : ∀ j l,g j l ≠ 0)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2))) :
    ∃ rL rR : EisensteinEPrimaryPhase.Coord,
      (∀ a ∈ leftFamily (TuplePartition.cell F Y k) g,
        ActualEisensteinCoordinates.residue (primaryGenerator (a 0))=rL) ∧
      (∀ a ∈ rightFamily (TuplePartition.cell F Y k) g,
        ActualEisensteinCoordinates.residue (primaryGenerator (a 0))=rR) := by
  let Fc := TuplePartition.cell F Y k
  have hf : ∀ c ∈ Fc,∀ j,Admissible (c j) := fun c hc => hF c (Finset.mem_filter.mp hc).1
  have hp : ∀ c ∈ Fc,Pairwise (fun j l => IsCoprime (c j) (c l)) :=
    fun c hc => hpF c (Finset.mem_filter.mp hc).1
  have hray : ∀ c ∈ Fc,∀ e ∈ Fc,primaryGenerator (c 0)-primaryGenerator (e 0) ∈
      (Ideal.span {(36:O)} : Ideal O) := fun c hc e he =>
    TuplePartition.cell_same_ray F Y k c e hc he 0
  obtain ⟨rL,hrL⟩ := fixed_pivot_ray _ (leftFamily_pivot_ray hf hp hgn hgp hray)
  obtain ⟨rR,hrR⟩ := fixed_pivot_ray _ (rightFamily_pivot_ray hf hp hgn hgp hray)
  exact ⟨rL,rR,hrL,hrR⟩

/-- The actual whole finite sector estimate, consuming the closed selected
squarefree norm and every literal table, puncture, output-sector and dyad
interface. There is no operator or packet estimate among its hypotheses. -/
theorem cell_sector_norm (A P gap ε : ℝ)
    (hA : 0 < A) (hP : 3*A+1 ≤ P) (hgap : 0 < gap) (hgh : gap < 1/2) (hε : 0 < ε) :
    ∃ mesh₀ : ℝ,0 < mesh₀ ∧ ∀ (N : ℕ) (Cslot wmin : ℝ),0 ≤ Cslot → 0 < wmin →
      ∃ C Z₀ : ℝ,0 < C ∧ ∀ (Z mesh δ : ℝ),Z₀ ≤ Z → 0 ≤ mesh → mesh ≤ mesh₀ →
        1/2+gap ≤ δ → δ ≤ 3/4 →
      ∀ (d : SelectedSlotData N) (F : Finset ColourTuple) (Y L : ℝ),
      d.Bounded Z mesh Cslot → d.Selects Z (F.image tupleRow) → d.HasSlope δ →
      wmin ≤ ∑ i,d.width i → ∀ hF : ∀ c ∈ F,∀ j,Admissible (c j),
      (∀ c ∈ F,Pairwise (fun j l => IsCoprime (c j) (c l))) →
      1 ≤ Y → Y ≤ Z^A → (∀ c ∈ F,((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y) →
      Y ≤ L → L ≤ Z^P →
      ∀ (k : TuplePartition.Key Y) (g : SharedTable),
      g ∈ actualTablePool (TuplePartition.cell F Y k) →
      ∀ E ∈ (tableSourceMask (TuplePartition.cell F Y k) g).powerset,
      ∀ sector ∈ BadFrequencySectors.boundedKeys (Z^P),∀ j : Fin (columnDyadicLength (Z^P)+1),
      ∀ α β : ColourTuple → ℂ,
      ‖actualSectorForm (TuplePartition.cell F Y k) (fun c hc => hF c (Finset.mem_filter.mp hc).1)
        g α β QuadraticInitialBound.sieveCutoff L E sector
          (NaturalFrequencyReindex.sourceDyad (reflectionFrequencies (Z^P)) (Z^P) sector j)‖ ≤
        C*Z^ε*Y^(2*ε)*L*
          Real.sqrt (tableArrayEnergy true (TuplePartition.cell F Y k) g α)*
            Real.sqrt (tableArrayEnergy false (TuplePartition.cell F Y k) g β) := by
  obtain ⟨m,hm,hsf⟩ := cell_pivot_selected_norms A P gap ε hA hP hgap hgh hε
  obtain ⟨Ch,hCh,hcard⟩ := cell_higher_cardinal_bounds ε hε
  obtain ⟨Cm,hCm,hsector⟩ := NaturalSectorBound.actual_sector_bound QuadraticInitialBound.sieveCutoff 2
  let Deps := idealDivisorConstant ε hε
  have hDeps : 0 < Deps := idealDivisorConstant_pos ε hε
  refine ⟨m,hm,?_⟩
  intro N Cslot wmin hCslot hwmin
  obtain ⟨Cs,Zs,hCs,hsf⟩ := hsf N Cslot wmin hCslot hwmin
  let C₀ := 8*16*16384*NaturalActualTail.badNorm*Cm*Ch*Cs*Deps
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity [NaturalActualTail.badNorm_pos]
  refine ⟨C₀+1,max 1 Zs,by positivity,?_⟩
  intro Z mesh δ hZ hm0 hmm hδlo hδhi d F Y L hb hs hslope hw hF hpF hY hYA hheight hYL hLP
    k g hg E hE sector hsect j α β
  have hz1 : 1 ≤ Z := (le_max_left _ _).trans hZ
  have hz0 : 0 < Z := lt_of_lt_of_le zero_lt_one hz1
  have hy0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hL : 0 < L := hy0.trans_le hYL
  let Fc := TuplePartition.cell F Y k
  have hf : ∀ c ∈ Fc,∀ l,Admissible (c l) := fun c hc => hF c (Finset.mem_filter.mp hc).1
  have hp : ∀ c ∈ Fc,Pairwise (fun l n => IsCoprime (c l) (c n)) :=
    fun c hc => hpF c (Finset.mem_filter.mp hc).1
  have hh : ∀ c ∈ Fc,((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y :=
    fun c hc => hheight c (Finset.mem_filter.mp hc).1
  have hv := actualTablePool_valid Fc hf hp g hg
  have hgn := hv.1
  have hgp := hv.2
  have hLF : ∀ a ∈ leftFamily Fc g,∀ l,Admissible (a l) :=
    fun a ha => (leftFamily_ok hf hp hgn hgp ha).2.1
  have hRF : ∀ a ∈ rightFamily Fc g,∀ l,Admissible (a l) :=
    fun a ha => (rightFamily_ok hf hp hgn hgp ha).2.1
  obtain ⟨pair,hpair,heq⟩ := Finset.mem_image.mp hg
  have hc := (Finset.mem_product.mp hpair).1
  have hgeo := cell_ranges F Y k hF hheight pair.1 hc
  have hnorms := table_norms_one_le g hgn
  let GN : ℝ := Ideal.absNorm (TableBudget.G g)
  let HN : ℝ := Ideal.absNorm (TableBudget.H g)
  let JN : ℝ := Ideal.absNorm (TableBudget.J g)
  let EN : ℝ := Ideal.absNorm (TableBudget.E g)
  let FN : ℝ := Ideal.absNorm (TableBudget.F g)
  let b := NaturalPunctureBudget.badScale Fc E
  let R := NaturalPunctureBudget.goodScale Fc E
  let T := divisorDyadicScale j.val
  let S := NaturalFrequencyReindex.sourceDyad (reflectionFrequencies (Z^P)) (Z^P) sector j
  let r := packetScale Fc g L E sector T (D k g) (D k g)
  have hT : 1 ≤ T := divisorDyadicScale_ge_one _
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hD := D_pos k g hgn
  have hr : 0 < r := packetScale_positive Fc k g hgn L T hL hT0 E sector
  have hbnd := NaturalPunctureBudget.badScale_bounds Fc E
  have hRbnd := NaturalPunctureBudget.goodScale_bounds Fc g hgn E hE
  rw [diagonal_norm] at hRbnd
  have hfreq := reflectionFrequencies_bound (Z^P) (Real.rpow_nonneg hz0.le _)
  have hST : ∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ 2*T := fun I hI =>
    (NaturalFrequencyReindex.sourceDyad_bounds _ _ hfreq sector j I hI).2
  have hScap : ∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ Z^P :=
    NaturalFrequencyReindex.sourceDyad_cap _ _ hfreq Z P le_rfl sector j
  have hS : ∀ I ∈ S,Supported I := NaturalFrequencyReindex.sourceDyad_supported _ _ sector j
  have hcoord : ∀ I ∈ S,(Ideal.absNorm I:ℝ)/T ∈ Set.Icc (1:ℝ) 2 :=
    NaturalFrequencyReindex.sourceDyad_coordinate _ _ hfreq sector j
  obtain ⟨rL,rR,hrL,hrR⟩ := cell_residual_rays F Y k hF hpF g hgn hgp
  have hx : ∀ a ∈ leftFamily Fc g,radicalNorm a/(D k g) ∈ Set.Icc (1:ℝ) 2 :=
    leftFamily_cell_radical_coordinate F Y k hF hpF hheight g hgn hgp
  have hy : ∀ a ∈ rightFamily Fc g,radicalNorm a/(D k g) ∈ Set.Icc (1:ℝ) 2 :=
    rightFamily_cell_radical_coordinate F Y k hF hpF hheight g hgn hgp
  have hNL : ∀ a ∈ leftFamily Fc g,(Ideal.absNorm (a 0):ℝ) ≤ Y :=
    fun a ha => (leftFamily_original_height hf hp hgn hgp Y hh a ha).1
  have hNR : ∀ a ∈ rightFamily Fc g,(Ideal.absNorm (a 0):ℝ) ≤ Y :=
    fun a ha => (rightFamily_original_height hf hp hgn hgp Y hh a ha).1
  let fL := 2*T+(2*(U k/(GN*EN)))^(1-δ)*(2*T)^δ
  let fR := 2*T+(2*(U k/(GN*FN)))^(1-δ)*(2*T)^δ
  let KL := Cs*Z^ε*fL
  let KR := Cs*Z^ε*fR
  have hfL : 0 ≤ fL := by dsimp [fL]; positivity [U_pos k]
  have hfR : 0 ≤ fR := by dsimp [fR]; positivity [U_pos k]
  have hKL : 0 ≤ KL := by dsimp [KL]; positivity
  have hKR : 0 ≤ KR := by dsimp [KR]; positivity
  have hop := hsf Z mesh δ ((le_max_right _ _).trans hZ) hm0 hmm hδlo hδhi
    d F S Y T k g hb hs hslope hw hF hpF hgn hgp hY hYA hheight hT hST hScap
  have hfracL : (2*TuplePartition.colourScale k 0)/(Ideal.absNorm (rowProduct g 0):ℝ)=
      2*(U k/(GN*EN)) := by rw [rowProduct_norm]; dsimp [U,GN,EN]; ring
  have hfracR : (2*TuplePartition.colourScale k 0)/(Ideal.absNorm (columnProduct g 0):ℝ)=
      2*(U k/(GN*FN)) := by rw [columnProduct_norm]; dsimp [U,GN,FN]; ring
  have hopL : ∀ v,selectedNorm (leftRows Fc g v) S ≤ KL := by
    intro v
    simpa only [leftRows,hfracL] using hop.1 v.val
  have hopR : ∀ v,selectedNorm (rightRows Fc g v) S ≤ KR := by
    intro v
    simpa only [rightRows,hfracR] using hop.2 v.val
  have hraw := hsector Fc hf hp g hgn hgp hLF hRF α β L hL.le E sector S hS
    rL rR hrL hrR T (D k g) (D k g) KL KR Y Y ε hε hD hD hT0 hr
    hKL hKR hy0.le hy0.le hopL hopR hNL hNR hx hy hcoord
  have hnodes := hcard F hF hpF Y k g hgn hgp hY hheight
  let nL : ℝ := ((leftFamily Fc g).image higherTuple).card
  let nR : ℝ := ((rightFamily Fc g).image higherTuple).card
  let EL := tableArrayEnergy true Fc g α
  let ER := tableArrayEnergy false Fc g β
  have hroot := NaturalRootBudget.complete_root_budget
    (U k) (V k) L GN HN JN EN FN R r b (rho k) (inputSectorScale sector)
    NaturalActualTail.badNorm δ (D k g) T nL nR KL KR Cm Ch Cs Deps (Z^ε) (Y^ε) fL fR EL ER
    (U_pos k) (V_pos k) (hgeo.1.trans hYL) hnorms.1 hnorms.2.1 hnorms.2.2.1
    hnorms.2.2.2.1 hnorms.2.2.2.2 hRbnd.1 hRbnd.2 hr hbnd.1 hbnd.2 hgeo.2
    (inputSectorScale_one_le sector) ⟨by linarith,by linarith⟩ (D_normalized k g)
    (packetScale_physical_relation Fc k g hgn L T hL (by linarith [hgeo.2.1]) E sector)
    rfl rfl (Nat.cast_nonneg _) (Nat.cast_nonneg _) hKL hKR hCm hCh.le hCs.le hDeps.le
    (Real.rpow_nonneg hz0.le _) (Real.rpow_nonneg hy0.le _) hfL hfR
    (tableArrayEnergy_nonneg true Fc g α) (tableArrayEnergy_nonneg false Fc g β)
    hnodes.2 hnodes.1 le_rfl le_rfl
  have hden : ‖eisEmbedding (primeSubsetGenerator (sourceMaskPrime Fc) E)‖^2*
      Real.sqrt ((Ideal.absNorm (offDiagonalIdeal g):ℝ)*(D k g)*(D k g))=
      b*R*Real.sqrt ((EN*FN*JN)*(D k g)^2) := by
    rw [NaturalPunctureBudget.puncture_norm_eq,offDiagonal_norm]
    congr 1
    congr 1
    ring
  rw [NaturalSectorBound.prefactorBound,hden] at hraw
  have hraw' : ‖actualSectorForm Fc hf g α β QuadraticInitialBound.sieveCutoff L E sector S‖ ≤
      (8*L/(b*R*Real.sqrt ((EN*FN*JN)*(D k g)^2))*Cm/(1+r)^2)*
        Real.sqrt (nR*KL*(Deps*Y^ε)*EL)*Real.sqrt (nL*KR*(Deps*Y^ε)*ER) := by
    change ‖actualSectorForm Fc hf g α β QuadraticInitialBound.sieveCutoff L E sector S‖ ≤
      (8*L/(b*R*Real.sqrt ((EN*FN*JN)*(D k g)^2)))*(Cm/(1+r)^2)*
        Real.sqrt (nR*KL*(Deps*Y^ε)*EL)*Real.sqrt (nL*KR*(Deps*Y^ε)*ER) at hraw
    simpa only [div_eq_mul_inv,mul_assoc] using hraw
  apply (hraw'.trans hroot).trans
  have hpow : (Y^ε)^2=Y^(2*ε) := by
    rw [← Real.rpow_mul_natCast hy0.le]
    congr 1
    ring
  rw [hpow]
  have hfactor : 0 ≤ Z^ε*Y^(2*ε)*L*Real.sqrt EL*Real.sqrt ER := by positivity
  have hh' := mul_le_mul_of_nonneg_right (show C₀ ≤ C₀+1 by linarith) hfactor
  simpa only [C₀,mul_assoc] using hh'

end
end Qrh.JointDetector.NaturalSelectedNorm

#print axioms Qrh.JointDetector.NaturalSelectedNorm.cell_higher_cardinal_bounds
#print axioms Qrh.JointDetector.NaturalSelectedNorm.cell_residual_rays
#print axioms Qrh.JointDetector.NaturalSelectedNorm.cell_sector_norm
