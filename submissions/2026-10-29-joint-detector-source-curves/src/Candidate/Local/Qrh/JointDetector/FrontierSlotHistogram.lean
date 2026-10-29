/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed selected-amplitude gap 1/10^9; original slots, masks, ordinary sources
and early mesh order are retained. Inherited notices follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.FrontierNaturalSelectedNormContract
import Candidate.Local.Qrh.JointDetector.FrontierDetectorWords

/-! Absolute individual-energy cells for the original aggregate slot event.
The cell precision is chosen after the finite slot count, whereas its total
error allowance and the physical slot mesh are chosen earlier. -/
namespace Qrh.JointDetector.FrontierSlotHistogram
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open FrontierDetectorWords
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

def energyBin (n : ℕ) (step Z response : ℝ) : Fin (n+1) :=
  ⟨Nat.findGreatest (fun i => Z^((i:ℝ)*step) ≤ response) n,
    Nat.lt_succ_of_le (Nat.findGreatest_le n)⟩

theorem energyBin_lower {n : ℕ} {step Z response : ℝ}
    (h : (energyBin n step Z response).val ≠ 0) :
    Z^(((energyBin n step Z response).val:ℝ)*step) ≤ response :=
  Nat.findGreatest_of_ne_zero rfl h

theorem energyBin_upper {n : ℕ} {step Z response : ℝ}
    (hZ : 1 ≤ Z) (hstep : 0 ≤ step) (hresponse : response ≤ Z^((n:ℝ)*step)) :
    response ≤ Z^((((energyBin n step Z response).val:ℝ)+1)*step) := by
  by_cases h : (energyBin n step Z response).val < n
  · have hh : response < Z^(((((energyBin n step Z response).val+1:ℕ):ℝ))*step) := by
      apply lt_of_not_ge
      exact Nat.findGreatest_is_greatest
        (P:=fun i => Z^((i:ℝ)*step) ≤ response) (Nat.lt_succ_self _)
        (by simpa only [energyBin] using Nat.succ_le_iff.mpr h)
    exact hh.le.trans_eq (by norm_num)
  · have he : (energyBin n step Z response).val=n := by
      have := (energyBin n step Z response).isLt
      omega
    rw [he]
    exact hresponse.trans (Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith))

/-- The full norm is controlled by primal ordinary-polynomial energy as well
as dual energy. Whole conjugation preserves the actual source coefficients. -/
theorem selectedNorm_le_of_primal_energy (rows : Finset O) (S : Finset (Ideal O))
    (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ c : S → ℂ, (∑ z : rows, ‖ordinaryPolynomial S c z.val‖^2) ≤
      K*∑ I, ‖c I‖^2) : selectedNorm rows S ≤ K := by
  have hh := FiniteSieveOperator.squared_norm_le_of_energy
    (selectedMatrix rows S).conjTranspose K hK
  have hp : ‖FiniteSieveOperator.operator (selectedMatrix rows S).conjTranspose‖^2 ≤ K := by
    apply hh
    intro c
    have hc := h (fun I => star (c I))
    have hid (z : rows) :
        (∑ I : S, (selectedMatrix rows S).conjTranspose z I*c I)=
          star (ordinaryPolynomial S (fun I => star (c I)) z.val) := by
      simp only [ordinaryPolynomial,star_sum,star_mul,star_star,selectedMatrix,
        Matrix.conjTranspose_apply,mul_comm]
    simpa only [hid,norm_star] using hc
  simpa only [FiniteSieveOperator.operator_conjTranspose_norm,selectedNorm] using hp

theorem selectedNorm_rows_partition_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    (rows : Finset O) (S : Finset (Ideal O)) (cell : O → κ) (K : ℝ) (hK : 0 ≤ K)
    (hcell : ∀ k, selectedNorm (rows.filter fun z => cell z=k) S ≤ K) :
    selectedNorm rows S ≤ (Fintype.card κ:ℝ)*K := by
  apply selectedNorm_le_of_primal_energy rows S _ (mul_nonneg (Nat.cast_nonneg _) hK)
  intro c
  have hsplit : (∑ z : rows, ‖ordinaryPolynomial S c z.val‖^2)=
      ∑ k : κ, ∑ z : rows.filter (fun z => cell z=k), ‖ordinaryPolynomial S c z.val‖^2 := by
    simp only [Finset.sum_coe_sort _ (fun z => ‖ordinaryPolynomial S c z‖^2)]
    exact (Finset.sum_fiberwise rows cell (fun z => ‖ordinaryPolynomial S c z‖^2)).symm
  rw [hsplit]
  calc
    _ ≤ ∑ _k : κ, K*(∑ I : S, ‖c I‖^2) := by
      apply Finset.sum_le_sum
      intro k hk
      exact (ordinaryPolynomial_energy (rows.filter fun z => cell z=k) S c).trans
        (mul_le_mul_of_nonneg_right (hcell k) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    _ = _ := by simp [mul_assoc]

theorem selectedNorm_empty_rows (S : Finset (Ideal O)) : selectedNorm ∅ S=0 := by
  apply le_antisymm ?_ (sq_nonneg _)
  apply selectedNorm_le_of_energy ∅ S 0 le_rfl
  intro c
  simp [selectedDualEnergy,selectedMatrix]

theorem slot_polynomial_upper {N : ℕ} (d : SelectedSlotData N) (Z mesh C : ℝ)
    (hZ : 1 ≤ Z) (hC : 0 ≤ C) (hd : d.Bounded Z mesh C) (i : Fin N) (z : O) :
    ‖d.polynomial i z‖^2 ≤ 256*C*Z^(d.width i) := by
  have hP : 1 ≤ Z^(d.width i) := Real.one_le_rpow hZ (hd.width_nonneg i)
  have hcard := DescentFiberCost.finite_ideal_count_real (d.sources i)
    (2*Z^(d.width i)) (by linarith) (hd.source_nonzero i) (hd.source_norm i)
  have hc := coefficient_cauchy (fun I : d.sources i => d.coefficient i I.val)
    (fun I => idealRowHom z I.val)
  have hunit : (∑ I : d.sources i, ‖idealRowHom z I.val‖^2) ≤ (d.sources i).card := by
    calc
      _ ≤ ∑ _I : d.sources i, (1:ℝ) := Finset.sum_le_sum fun I _ => by
        exact (pow_le_pow_left₀ (norm_nonneg _) (idealRowHom_norm z I.val) 2).trans_eq (by norm_num)
      _ = _ := by simp
  have hmass : (∑ I : d.sources i, ‖d.coefficient i I.val‖^2) ≤ C := by
    rw [Finset.sum_coe_sort _ (fun I => ‖d.coefficient i I‖^2)]
    exact hd.coefficient_mass i
  have hp : ‖d.polynomial i z‖^2 ≤ C*(d.sources i).card := by
    have hh := hc.trans (mul_le_mul hmass hunit
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) hC)
    simpa only [SelectedSlotData.polynomial,
      Finset.sum_coe_sort _ (fun I => d.coefficient i I*idealRowHom z I)] using hh
  exact hp.trans (by nlinarith)

def cellData {N n : ℕ} (d : SelectedSlotData N) (labels : Fin N → Fin (n+1))
    (step : ℝ) : SelectedSlotData N where
  width := fun i => if (labels i).val=0 then 0 else d.width i
  energy := fun i => ((labels i).val:ℝ)*step
  sources := fun i => if (labels i).val=0 then {1} else d.sources i
  coefficient := fun i I => if (labels i).val=0 then (if I=1 then 1 else 0) else d.coefficient i I

theorem cellData_polynomial {N n : ℕ} (d : SelectedSlotData N)
    (labels : Fin N → Fin (n+1)) (step : ℝ) (i : Fin N) (z : O) :
    (cellData d labels step).polynomial i z=
      if (labels i).val=0 then 1 else d.polynomial i z := by
  by_cases hi : (labels i).val=0
  · simp only [cellData,SelectedSlotData.polynomial,hi,ite_true]
    rw [Finset.sum_singleton]
    simp only [ite_true,one_mul]
    exact map_one (idealRowHom z)
  · simp only [cellData,SelectedSlotData.polynomial,hi,ite_false]

theorem cellData_bounded {N n : ℕ} (d : SelectedSlotData N)
    (labels : Fin N → Fin (n+1)) (step Z mesh C : ℝ)
    (hm : 0 ≤ mesh) (hC : 1 ≤ C) (hd : d.Bounded Z mesh C) :
    (cellData d labels step).Bounded Z mesh C := by
  constructor
  · intro i; by_cases hi : (labels i).val=0
    · simp only [cellData,hi,ite_true,le_refl]
    · simpa only [cellData,hi,ite_false] using hd.width_nonneg i
  · intro i; by_cases hi : (labels i).val=0
    · simpa only [cellData,hi,ite_true] using hm
    · simpa only [cellData,hi,ite_false] using hd.width_le_mesh i
  · intro i I hI
    by_cases hi : (labels i).val=0
    · have hI1 : I=1 := by simpa only [cellData,hi,ite_true,Finset.mem_singleton] using hI
      subst I
      exact one_ne_zero
    · exact hd.source_nonzero i I (by simpa only [cellData,hi,ite_false] using hI)
  · intro i I hI
    by_cases hi : (labels i).val=0
    · have hI1 : I=1 := by simpa only [cellData,hi,ite_true,Finset.mem_singleton] using hI
      subst I
      simp only [cellData,hi,ite_true]
      norm_num
    · simpa only [cellData,hi,ite_false] using
        hd.source_norm i I (by simpa only [cellData,hi,ite_false] using hI)
  · intro i
    by_cases hi : (labels i).val=0
    · simp only [cellData,hi,ite_true]
      simpa using hC
    · simpa only [cellData,hi,ite_false] using hd.coefficient_mass i

theorem cellData_selects {N n : ℕ} (d : SelectedSlotData N)
    (labels : Fin N → Fin (n+1)) (step Z : ℝ) (rows : Finset O)
    (hcell : ∀ z ∈ rows, ∀ i,
      energyBin n step Z (‖d.polynomial i z‖^2)=labels i) :
    (cellData d labels step).Selects Z rows := by
  intro z hz i
  by_cases hi : (labels i).val=0
  · rw [cellData_polynomial]
    simp [cellData,hi]
  · rw [cellData_polynomial,ite_eq_right hi]
    have hh := energyBin_lower (n:=n) (step:=step) (Z:=Z)
      (response:=‖d.polynomial i z‖^2) (by rw [hcell z hz i]; exact hi)
    simpa only [hcell z hz i,cellData] using hh

theorem cellData_width_le {N n : ℕ} (d : SelectedSlotData N)
    (labels : Fin N → Fin (n+1)) (step : ℝ) (hw : ∀ i, 0 ≤ d.width i) :
    (∑ i, (cellData d labels step).width i) ≤ ∑ i, d.width i := by
  apply Finset.sum_le_sum
  intro i hi
  by_cases hh : (labels i).val=0
  · simpa only [cellData,hh,ite_true] using hw i
  · simp only [cellData,hh,ite_false,le_refl]

theorem aggregate_label_lower {N n : ℕ} (d : SelectedSlotData N)
    (labels : Fin N → Fin (n+1)) (step Z δ : ℝ) (z : O)
    (hZ : 1 < Z) (hstep : 0 ≤ step)
    (hcell : ∀ i, energyBin n step Z (‖d.polynomial i z‖^2)=labels i)
    (htop : ∀ i, ‖d.polynomial i z‖^2 ≤ Z^((n:ℝ)*step))
    (hlower : Z^(δ*∑ i, d.width i) ≤ ∏ i, ‖d.polynomial i z‖^2) :
    δ*(∑ i, d.width i) ≤ (∑ i, (cellData d labels step).energy i)+(N:ℝ)*step := by
  have hp : (∏ i, ‖d.polynomial i z‖^2) ≤ ∏ i, Z^((((labels i).val:ℝ)+1)*step) := by
    apply Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _)
    intro i hi
    have hh := energyBin_upper hZ.le hstep (htop i)
    simpa only [hcell i] using hh
  rw [← Real.rpow_sum_of_pos (by linarith : 0 < Z)] at hp
  have he := (Real.rpow_le_rpow_left_iff hZ).mp (hlower.trans hp)
  convert he using 1
  simp only [cellData,add_mul,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,one_mul]

theorem label_upper_width {N n : ℕ} (d : SelectedSlotData N)
    (labels : Fin N → Fin (n+1)) (step Z : ℝ) (z : O)
    (hZ : 1 < Z) (hstep : 0 ≤ step)
    (hcell : ∀ i, energyBin n step Z (‖d.polynomial i z‖^2)=labels i)
    (hupper : ∀ i, ‖d.polynomial i z‖^2 ≤ Z^(d.width i+step)) :
    (∑ i, (cellData d labels step).energy i) ≤
      (∑ i, (cellData d labels step).width i)+(N:ℝ)*step := by
  have hi (i : Fin N) : (cellData d labels step).energy i ≤
      (cellData d labels step).width i+step := by
    by_cases hh : (labels i).val=0
    · simpa only [cellData,hh,Nat.cast_zero,zero_mul,ite_true,zero_add] using hstep
    · have hl := energyBin_lower (n:=n) (step:=step) (Z:=Z)
        (response:=‖d.polynomial i z‖^2) (by rw [hcell i]; exact hh)
      rw [hcell i] at hl
      have he := (Real.rpow_le_rpow_left_iff hZ).mp (hl.trans (hupper i))
      simpa only [cellData,hh,ite_false] using he
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] using h

theorem cell_geometry {N n : ℕ} (d : SelectedSlotData N)
    (labels : Fin N → Fin (n+1)) (step δ β smin : ℝ)
    (hw : ∀ i, 0 ≤ d.width i) (hsmin : 0 < smin)
    (hs : smin ≤ ∑ i, d.width i) (hδ : (1/2:ℝ) ≤ δ)
    (hβ : β ∈ Set.Icc (0:ℝ) (1/8)) (hδβ : 0 ≤ δ-β)
    (hbudget : (N:ℝ)*step ≤ β*smin)
    (hlower : δ*(∑ i, d.width i) ≤ (∑ i, (cellData d labels step).energy i)+(N:ℝ)*step)
    (hupper : (∑ i, (cellData d labels step).energy i) ≤
      (∑ i, (cellData d labels step).width i)+(N:ℝ)*step) :
    smin/4 ≤ ∑ i, (cellData d labels step).width i ∧
      (cellData d labels step).HasSlope (δ-β) := by
  have hβS := mul_le_mul_of_nonneg_left hs hβ.1
  have hδS := mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ δ)
  have hδs := mul_le_mul_of_nonneg_right hδ hsmin.le
  have hβs := mul_le_mul_of_nonneg_right hβ.2 hsmin.le
  have hwidth := cellData_width_le d labels step hw
  constructor
  · nlinarith
  · have hh := mul_le_mul_of_nonneg_left hwidth hδβ
    unfold SelectedSlotData.HasSlope
    nlinarith

theorem envelope_shift {Z A Y L δ β : ℝ}
    (hZ : 1 ≤ Z) (hA : 0 ≤ A) (hY : 1 ≤ Y) (hYU : Y ≤ Z^A)
    (hL : 1 ≤ L) (hβ : 0 ≤ β) :
    L+Y^(1-(δ-β))*L^(δ-β) ≤ Z^(A*β)*(L+Y^(1-δ)*L^δ) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hYβ : Y^β ≤ Z^(A*β) := by
    calc
      _ ≤ (Z^A)^β := Real.rpow_le_rpow hY0.le hYU hβ
      _ = _ := (Real.rpow_mul hZ0.le A β).symm
  have hYY : Y^(1-(δ-β))=Y^(1-δ)*Y^β := by
    rw [← Real.rpow_add hY0]
    congr 1
    ring
  have hLL : L^(δ-β) ≤ L^δ := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hterm : Y^(1-(δ-β))*L^(δ-β) ≤ Z^(A*β)*(Y^(1-δ)*L^δ) := by
    rw [hYY]
    have hh := mul_le_mul
      (mul_le_mul_of_nonneg_left hYβ (Real.rpow_nonneg hY0.le (1-δ))) hLL
      (Real.rpow_nonneg (by linarith : 0 ≤ L) (δ-β))
      (mul_nonneg (Real.rpow_nonneg hY0.le (1-δ)) (Real.rpow_nonneg hZ0.le (A*β)))
    nlinarith
  have hpower : 1 ≤ Z^(A*β) := Real.one_le_rpow hZ (mul_nonneg hA hβ)
  have hlinear : L ≤ Z^(A*β)*L := le_mul_of_one_le_left (by linarith) hpower
  nlinarith

def labelsFor {N : ℕ} (d : SelectedSlotData N) (n : ℕ) (step Z : ℝ) (z : O) :
    Fin N → Fin (n+1) := fun i => energyBin n step Z (‖d.polynomial i z‖^2)

def coreCell {N : ℕ} (d : SelectedSlotData N) (n : ℕ) (step Z : ℝ)
    (cores : Finset HeckeInverseAmplification.FreeRow) (labels : Fin N → Fin (n+1)) :=
  cores.filter fun u => labelsFor d n step Z u.val=labels

theorem coreCell_image {N : ℕ} (d : SelectedSlotData N) (n : ℕ) (step Z : ℝ)
    (cores : Finset HeckeInverseAmplification.FreeRow) (labels : Fin N → Fin (n+1)) :
    (coreCell d n step Z cores labels).image Subtype.val=
      (cores.image Subtype.val).filter (fun z => labelsFor d n step Z z=labels) := by
  ext z
  constructor
  · intro hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hu,hcell⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨u,hu,rfl⟩,hcell⟩
  · intro hz
    obtain ⟨hz,hcell⟩ := Finset.mem_filter.mp hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨hu,hcell⟩,rfl⟩

theorem finite_aggregate_norm {N n : ℕ} (d : SelectedSlotData N)
    (cores : Finset HeckeInverseAmplification.FreeRow) (S : Finset (Ideal O))
    (Z A P mesh C smin δ β step Y L K : ℝ)
    (hZ : 1 < Z) (hA : 0 ≤ A) (hm : 0 ≤ mesh) (hm1 : mesh ≤ 1)
    (hC : 1 ≤ C) (hd : d.Bounded Z mesh C) (hsmin : 0 < smin)
    (hs : smin ≤ ∑ i, d.width i) (hδ : (1/2:ℝ) ≤ δ)
    (hβ : β ∈ Set.Icc (0:ℝ) (1/8)) (hδβ : 0 ≤ δ-β)
    (hstep : step ∈ Set.Icc (0:ℝ) 1) (hbudget : (N:ℝ)*step ≤ β*smin)
    (hn : (2:ℝ) ≤ (n:ℝ)*step)
    (hupper : ∀ i z, ‖d.polynomial i z‖^2 ≤ Z^(d.width i+step))
    (hresponse : ∀ u ∈ cores, Z^(δ*∑ i, d.width i) ≤ ∏ i, ‖d.polynomial i u.val‖^2)
    (hY : 1 ≤ Y) (hYU : Y ≤ Z^A)
    (hcores : ∀ u ∈ cores, ProbeHighRowFamily.rowNorm u ≤ Y)
    (hL : 1 ≤ L) (hLU : L ≤ Z^P) (hS : ∀ I ∈ S, (Ideal.absNorm I:ℝ) ≤ L)
    (hK : 0 ≤ K)
    (hcellNorm : NaturalCellNormBound N Z A P mesh C (smin/4) (δ-β) K) :
    selectedNorm (cores.image Subtype.val) S ≤
      (Fintype.card (Fin N → Fin (n+1)):ℝ)*K*Z^(A*β)*(L+Y^(1-δ)*L^δ) := by
  let E := cores.image Subtype.val
  let cell := labelsFor d n step Z
  have hp : ∀ labels, selectedNorm (E.filter fun z => cell z=labels) S ≤
      K*Z^(A*β)*(L+Y^(1-δ)*L^δ) := by
    intro labels
    let F := coreCell d n step Z cores labels
    have hFE : F.image Subtype.val=E.filter (fun z => cell z=labels) := coreCell_image d n step Z cores labels
    rw [← hFE]
    by_cases hF : F.Nonempty
    · obtain ⟨u,hu⟩ := hF
      have huc := Finset.mem_filter.mp hu
      have hclass (z : O) (hz : z ∈ F.image Subtype.val) (i : Fin N) :
          energyBin n step Z (‖d.polynomial i z‖^2)=labels i := by
        rw [hFE] at hz
        exact congrFun (Finset.mem_filter.mp hz).2 i
      have hrep (i : Fin N) : energyBin n step Z (‖d.polynomial i u.val‖^2)=labels i :=
        congrFun huc.2 i
      have htop (i : Fin N) : ‖d.polynomial i u.val‖^2 ≤ Z^((n:ℝ)*step) := by
        apply (hupper i u.val).trans
        apply Real.rpow_le_rpow_of_exponent_le hZ.le
        have hw := (hd.width_le_mesh i).trans hm1
        linarith [hstep.2]
      have hlower := aggregate_label_lower d labels step Z δ u.val hZ hstep.1
        hrep htop (hresponse u huc.1)
      have henergy := label_upper_width d labels step Z u.val hZ hstep.1 hrep
        (fun i => hupper i u.val)
      have hg := cell_geometry d labels step δ β smin hd.width_nonneg hsmin hs hδ hβ
        hδβ hbudget hlower henergy
      have hnrm := hcellNorm (cellData d labels step) F S Y L
        (cellData_bounded d labels step Z mesh C hm hC hd)
        (cellData_selects d labels step Z _ hclass) hg.2 hg.1 hY hYU
        (fun v hv => hcores v (Finset.mem_filter.mp hv).1) hL hLU hS
      exact hnrm.trans (by
        have he := mul_le_mul_of_nonneg_left (envelope_shift (δ:=δ) hZ.le hA hY hYU hL hβ.1) hK
        nlinarith)
    · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hF
      rw [he,Finset.image_empty,selectedNorm_empty_rows]
      positivity
  have hK' : 0 ≤ K*Z^(A*β)*(L+Y^(1-δ)*L^δ) := by positivity
  have h := selectedNorm_rows_partition_le E S cell _ hK' hp
  simpa only [mul_assoc] using h

/-- The absolute total energy buffer is fixed before N. Per-slot precision
is chosen afterwards; neither the physical mesh nor the norm exponent loss
is multiplied by the number of original slots. -/
theorem naturalAggregateSlotNorm_of_cell (hcell : NaturalSelectedCellNorm) :
    FrontierNaturalAggregateSlotNorm := by
  intro A P loss hA hP hloss
  let β : ℝ := min (1/4000000000) (loss/(8*(A+1)))
  have hβ0 : 0 < β := by dsimp [β]; positivity
  have hβ1 : β ≤ 1/4000000000 := min_le_left _ _
  have hβ2 : β ≤ loss/(8*(A+1)) := min_le_right _ _
  have hβ : β ∈ Set.Icc (0:ℝ) (1/8) := ⟨hβ0.le,by linarith⟩
  have hexp : loss/4+A*β ≤ loss := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8*(A+1))).mp hβ2
    nlinarith
  obtain ⟨mesh₀,hmesh₀,hnorm⟩ := hcell A P (1/2000000000) (loss/4)
    hA hP (by norm_num) (by norm_num) (by positivity)
  refine ⟨min 1 mesh₀,lt_min zero_lt_one hmesh₀,?_⟩
  intro N Cslot smin hCslot hsmin
  obtain ⟨Cn,Zn,hCn,hnorm⟩ := hnorm N Cslot (smin/4) (by linarith) (by positivity)
  let step : ℝ := min (β*smin/(N+1)) (1/2)
  have hstep0 : 0 < step := by dsimp [step]; positivity
  have hstep1 : step ≤ 1/2 := min_le_right _ _
  have hstepU : step ≤ β*smin/(N+1) := min_le_left _ _
  have hbudget : (N:ℝ)*step ≤ β*smin := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ) < N+1)).mp hstepU
    nlinarith
  let n : ℕ := ⌈2/step⌉₊
  have hn : (2:ℝ) ≤ (n:ℝ)*step :=
    (div_le_iff₀ hstep0).mp (Nat.le_ceil (2/step))
  let D : ℝ := Fintype.card (Fin N → Fin (n+1))
  have hD : 0 < D := by dsimp [D]; exact_mod_cast Fintype.card_pos
  refine ⟨D*Cn,max 2 (max Zn ((256*Cslot)^(1/step))),mul_pos hD hCn,?_⟩
  intro Z mesh δ hZ hm hmU hδ hδU
  have hZ2 : 2 ≤ Z := (le_max_left _ _).trans hZ
  have hZ1 : 1 < Z := by linarith
  have hZn : Zn ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZ)
  have hRoot : (256*Cslot)^(1/step) ≤ Z :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hZ)
  have hconst : 0 < 256*Cslot := by linarith
  have hCpower : 256*Cslot ≤ Z^step := by
    calc
      _ = ((256*Cslot)^(1/step))^step := by
        rw [← Real.rpow_mul hconst.le,div_mul_cancel₀ _ hstep0.ne',Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hconst.le _) hRoot hstep0.le
  have hm1 : mesh ≤ 1 := hmU.trans (min_le_left _ _)
  have hδcell : 1/2+(1/2000000000:ℝ) ≤ δ-β := by linarith
  have hδcellU : δ-β ≤ 3/4 := by linarith
  have hnrm := hnorm Z mesh (δ-β) hZn hm (hmU.trans (min_le_right _ _)) hδcell hδcellU
  intro d cores S Y L hd hs hresponse hY hYU hcores hL hLU hS
  have hupper (i : Fin N) (z : O) : ‖d.polynomial i z‖^2 ≤ Z^(d.width i+step) := by
    calc
      _ ≤ 256*Cslot*Z^(d.width i) := slot_polynomial_upper d Z mesh Cslot hZ1.le (by linarith) hd i z
      _ ≤ Z^step*Z^(d.width i) :=
        mul_le_mul_of_nonneg_right hCpower (Real.rpow_nonneg (by linarith : 0 ≤ Z) _)
      _ = _ := by rw [← Real.rpow_add (by linarith : 0 < Z)]; congr 1; ring
  have hh := finite_aggregate_norm d cores S Z A P mesh Cslot smin δ β step Y L (Cn*Z^(loss/4))
    hZ1 hA.le hm hm1 hCslot hd hsmin hs (by linarith) hβ (by linarith [hδcell])
    ⟨hstep0.le,by linarith⟩ hbudget hn hupper hresponse hY hYU hcores hL hLU hS
    (by positivity) hnrm
  apply hh.trans
  have hpower := Real.rpow_le_rpow_of_exponent_le hZ1.le hexp
  have hp : Z^(loss/4)*Z^(A*β) ≤ Z^loss := by
    rwa [← Real.rpow_add (by linarith : 0 < Z)]
  have hmul := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ D*Cn*(L+Y^(1-δ)*L^δ) by positivity)
  dsimp [D] at hmul ⊢
  nlinarith

end
end Qrh.JointDetector.FrontierSlotHistogram

#print axioms Qrh.JointDetector.FrontierSlotHistogram.selectedNorm_rows_partition_le
#print axioms Qrh.JointDetector.FrontierSlotHistogram.slot_polynomial_upper
#print axioms Qrh.JointDetector.FrontierSlotHistogram.naturalAggregateSlotNorm_of_cell
