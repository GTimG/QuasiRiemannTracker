/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B043
import Submissions.cycle61_c0125139.Bundles.B044
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDyadic

/- BEGIN ORIGINAL Cycle61.Numerator.Finite.Partition; sha256 b57726f7b5e2dc85833ce64010f256b976800d213a2519f2e0450dfb4102acca -/
section
                                                  
                                                           

set_option autoImplicit false
namespace Cycle61.FiniteNumerator
noncomputable section
open scoped Classical BigOperators
open OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open Cycle25.Weighted.FullWContour
local notation "O" => HeckeFamily.O

theorem fullW_bin_partition {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e B : ℝ) (idx grid : FreeRow→ℕ) (n m : ℕ)
    (hlabel : ∀u∈R,idx u ≤ n ∧ grid u ≤ m) :
    finiteCentralFullWRows S hS hmax η R T hT W Yp W0 W1 X Y Z e
      (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*B)=
    ∑i∈Finset.range (n+1),∑j∈Finset.range (m+1),
      finiteCentralFullWRows S hS hmax η (cubeBinRows R idx grid i j) T hT W Yp W0 W1 X Y Z e
        (fun _=>51/100+e*j) (fun _=>(3*i+1:ℕ)*B) := by
  unfold finiteCentralFullWRows
  rw [←sum_cubeBinRows R idx grid n m hlabel]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro u hu
  rcases (mem_cubeBinRows R idx grid i j u).mp hu with ⟨_,hi,hj⟩
  simp only [hi,hj]

theorem fullW_dyadic_partition {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e U : ℝ) (a H : FreeRow→ℝ)
    (hR : ∀u∈R,u.val≠1 ∧ rowNorm u≤U) :
    finiteCentralFullWRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H =
      ∑k∈smallDyadicIndices U,
        finiteCentralFullWRows S hS hmax η (R∩dyadicRows 1 k) T hT W Yp W0 W1 X Y Z e a H := by
  unfold finiteCentralFullWRows
  exact retained_dyadic_sum R U hR _

theorem fullW_cells_norm_bound {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e B U : ℝ) (idx grid : FreeRow→ℕ)
    (n m : ℕ) (N : ℂ) (A : ℝ) (hA : 0≤A)
    (hR : ∀u∈R,u.val≠1 ∧ rowNorm u≤U)
    (hlabel : ∀u∈R,idx u ≤ n ∧ grid u ≤ m)
    (hcell : ∀k∈smallDyadicIndices U,∀i∈Finset.range (n+1),∀j∈Finset.range (m+1),
      (cubeBinRows (R∩dyadicRows 1 k) idx grid i j).Nonempty →
      ‖finiteCentralFullWRows S hS hmax η (cubeBinRows (R∩dyadicRows 1 k) idx grid i j)
        T hT W Yp W0 W1 X Y Z e (fun _=>51/100+e*j) (fun _=>(3*i+1:ℕ)*B)/N‖≤A) :
    ‖finiteCentralFullWRows S hS hmax η R T hT W Yp W0 W1 X Y Z e
      (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*B)/N‖ ≤
      ((smallDyadicIndices U).card:ℝ)*(n+1:ℕ)*(m+1:ℕ)*A := by
  rw [fullW_dyadic_partition S hS hmax η R T hT W Yp W0 W1 X Y Z e U _ _ hR,
    Finset.sum_div]
  calc
    _ ≤ ∑k∈smallDyadicIndices U,(n+1:ℕ)*(m+1:ℕ)*A := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      rw [fullW_bin_partition S hS hmax η (R∩dyadicRows 1 k) T hT W Yp W0 W1 X Y Z e B
        idx grid n m (fun u hu=>hlabel u (Finset.mem_inter.mp hu).1),Finset.sum_div]
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑i∈Finset.range (n+1),∑j∈Finset.range (m+1),A := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.sum_div]
          apply (norm_sum_le _ _).trans
          apply Finset.sum_le_sum
          intro j hj
          by_cases hn : (cubeBinRows (R∩dyadicRows 1 k) idx grid i j).Nonempty
          · exact hcell k hk i hi j hj hn
          · have hempty:=Finset.not_nonempty_iff_eq_empty.mp hn
            simpa only [hempty,finiteCentralFullWRows,Finset.sum_empty,zero_div,norm_zero] using hA
        _ = _ := by simp;ring
    _ = _ := by simp;ring
end
end Cycle61.FiniteNumerator

end
/- END ORIGINAL Cycle61.Numerator.Finite.Partition -/

/- BEGIN ORIGINAL Cycle61.Numerator.Finite.Cells; sha256 5bf8b987634db4873922a27c8a453f3ba27bc32364deb93c8ff5b4b425f618ee -/
section
                                         
                                         

set_option autoImplicit false
namespace Cycle61.FiniteNumerator
noncomputable section
open scoped Classical BigOperators
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open Cycle61DetectorCount FinalAssembly Cycle61HighTransport
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

instance fixedProduct (D : BaselineData) (F : BaselineSourceData D) : NeZero (∏P∈F.S,P) :=
  ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩

def primePool (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ) (j : Fin D.N) :=
  pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Z^(D.length j))

theorem poolOutside (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ) :
    ∀j P,P∈primePool D F Z j→P.val∉F.S :=
  fun j P hP=>(mem_pool _ F.S 1 2 (Z^(D.length j)) P).mp hP |>.2.2.2

def normalizer (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ) : ℂ :=
  actualNormalizer F.modulus ⊤ F.S D.length 1 2 (fun _=>F.w) F.W F.W Z

def fullW (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z : ℝ) (R : Finset FreeRow) (a H : FreeRow→ℝ) : ℂ :=
  Cycle25.Weighted.FullWContour.finiteCentralFullWRows F.S F.exclusions F.maximal η R
    (primePool D F Z) (poolOutside D F Z) (fun _ y=>(F.w y:ℂ)) (fun j=>Z^(D.length j))
    F.W F.W (Z^Arithmetic.x) (Z^Arithmetic.y) Z D.e a H

def selectedRows (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ) (grid : FreeRow→ℕ) :=
  supportedNonfloorRows F.S F.maximal (rowBand (Z^(1/100:ℝ)) (Z^(Arithmetic.h+rowPadding))) grid

def cellRows (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ)
    (idx grid : FreeRow→ℕ) (k i j : ℕ) :=
  cubeBinRows (selectedRows D F Z grid∩dyadicRows 1 k) idx grid i j

def cellTarget : ℝ :=
  HeckeZeroSupremum.beta+Assembly.signalShift-4999/5000000000-
    (HeckeZeroSupremum.beta-Arithmetic.theta)/2

structure CellFacts (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z τ : ℝ) (R : Finset FreeRow) (d a : ℝ) (i : ℕ) : Prop where
  d_lower : (1/200:ℝ)≤d
  d_upper : d≤Arithmetic.dPlus
  a_lower : (51/100:ℝ)<a
  a_upper : a≤7/8
  source_rows : ∀u∈R,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
    (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-D.t)
  moment_rows : ∀u∈R,(Z^d)^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤Z^d
  frequency_lower : ∀u∈R,Z^(d-2*D.t)≤rowNorm u
  natural_nonprincipal : ∀u∈R,∀θ,(rayCubeFamily F.modulus ⊤ le_top u θ).residue≠1
  next_maximum : ∀u∈R,detectorMaximum
    (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
    (3*(i+1:ℕ)*Z^τ)<a+2*D.e
  current_maximum : ∀u∈R,a≤detectorMaximum
    (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
    ((3*i:ℕ)*Z^τ)

theorem selected_rows_facts (D : BaselineData) (F : BaselineSourceData D)
    (Z : ℝ) (grid : FreeRow→ℕ) :
    ∀u∈selectedRows D F Z grid,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧
      rowNorm u≤Z^(Arithmetic.h+rowPadding) := by
  intro u hu
  rcases (mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu with ⟨hb,hcal,_⟩
  rcases mem_rowBand.mp hb with ⟨hne,hlo,hhi⟩
  exact ⟨hne,hlo,hcal,hhi.le⟩
end
end Cycle61.FiniteNumerator

end
/- END ORIGINAL Cycle61.Numerator.Finite.Cells -/

/- BEGIN ORIGINAL Cycle61.Numerator.Finite.Geometry; sha256 4f31a88fa6a071a989a9d2beac9445756c8012aad4cc6f3a2c21aaaf2b878684 -/
section
                                     

set_option autoImplicit false
namespace Cycle61.FiniteNumerator
noncomputable section
open scoped Classical BigOperators
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open Cycle61DetectorCount FinalAssembly Cycle61HighTransport

/-- All cell geometry is uniform before the live row labels. -/
theorem actual_cell_geometry (A : ChosenData) (η : Character) (τ : ℝ) (n : ℕ) :
    ∀ᶠZ : ℝ in atTop,∀idx grid : FreeRow→ℕ,
      ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
        η rowPadding A.D.e τ n Z idx grid →
      ∀k i j : ℕ,(cellRows A.D A.F Z idx grid k i j).Nonempty →
        CellFacts A.D A.F η Z τ (cellRows A.D A.F Z idx grid k i j)
          (sourceDyadConductor Z A.D.t k) (51/100+A.D.e*j) i := by
  filter_upwards [sourceDyad_geometry_eventually (1/200) Arithmetic.dPlus A.D.t
    (Arithmetic.h+rowPadding) (by norm_num) (by norm_num) A.D.t_pos
    (padded_row_cutoff A.D A.P),eventually_gt_atTop (1:ℝ)] with Z hgeo hZ
  intro idx grid hsel k i j hne
  let R := selectedRows A.D A.F Z grid
  let Rij := cellRows A.D A.F Z idx grid k i j
  have hsubk : Rij⊆R∩dyadicRows 1 k := Finset.filter_subset _ _
  have hsub : Rij⊆R := hsubk.trans Finset.inter_subset_left
  have hrows:=selected_rows_facts A.D A.F Z grid
  have hg:=hgeo R (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.1,(hrows u hu).2.2.2⟩) k
    (hne.mono hsubk)
  obtain ⟨u,hu⟩ := hne
  have hmem := (mem_cubeBinRows (R∩dyadicRows 1 k) idx grid i j u).mp hu
  have hgu := ((mem_supportedNonfloorRows A.F.S A.F.maximal _ grid u).mp (hsub hu)).2.2
  have hjpos : (0:ℝ)<j := by exact_mod_cast Nat.pos_of_ne_zero (hmem.2.2 ▸ hgu)
  have ha : (51/100:ℝ)<51/100+A.D.e*j := by nlinarith [A.D.e_pos]
  have hai : 51/100+A.D.e*j≤7/8 := by simpa only [hmem.2.2] using (hsel.2.1 u).2.1
  have hZp : 0<Z := zero_lt_one.trans hZ
  refine ⟨hg.2.2.1,hg.2.2.2.1,ha,hai,?_,?_,?_,?_,?_,?_⟩
  · intro u hu
    exact ⟨(hrows u (hsub hu)).1,(hrows u (hsub hu)).2.1,
      (hrows u (hsub hu)).2.2.1,hg.2.2.2.2.2 u (hsubk hu)⟩
  · intro u hu
    constructor
    · rw [←Real.rpow_mul hZp.le]
      apply (Real.rpow_le_rpow_of_exponent_le hZ.le ?_).trans (hrows u (hsub hu)).2.1
      have hd:=hg.2.2.2.1
      have hcap : Arithmetic.dPlus≤1 := by norm_num [Arithmetic.dPlus,Arithmetic.h]
      nlinarith
    · exact (hg.2.2.2.2.2 u (hsubk hu)).trans
        (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [A.D.t_pos]))
  · intro u hu
    simpa only [sourceDyadConductor,add_sub_cancel_right] using (hg.2.2.2.2.1 u (hsubk hu)).1
  · intro u hu
    exact (hsel.2.2 u ((mem_supportedNonfloorRows A.F.S A.F.maximal _ grid u).mp (hsub hu)).1
      (hrows u (hsub hu)).2.2.1).1
  · intro u hu
    have hb:=(hsel.2.1 u).2.2.2.2.1
    have hm:=(mem_cubeBinRows (R∩dyadicRows 1 k) idx grid i j u).mp hu
    rwa [hm.2.1,hm.2.2] at hb
  · intro u hu
    have hb:=(hsel.2.1 u).2.2.1
    have hm:=(mem_cubeBinRows (R∩dyadicRows 1 k) idx grid i j u).mp hu
    simpa only [hm.2.1,hm.2.2,Nat.cast_mul,Nat.cast_ofNat] using hb
end
end Cycle61.FiniteNumerator

end
/- END ORIGINAL Cycle61.Numerator.Finite.Geometry -/

/- BEGIN ORIGINAL Cycle61.Numerator.Finite.Summation; sha256 8c9cca81fb45fc618150d451aa3209f718a6c4680fc41742a5bea48c19b3f3a5 -/
section
                                        

set_option autoImplicit false
namespace Cycle61.FiniteNumerator
noncomputable section
open scoped Classical BigOperators
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open Cycle61DetectorCount FinalAssembly Cycle61HighTransport

def FullWCellsAt (A : ChosenData) (τ : ℝ) (n : ℕ) (η : Character) (C Z : ℝ) : Prop :=
  ∀idx grid : FreeRow→ℕ,
    ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
      η rowPadding A.D.e τ n Z idx grid →
    ∀k∈smallDyadicIndices (Z^(Arithmetic.h+rowPadding)),
    ∀i∈Finset.range (n+1),∀j∈Finset.range (⌊(49/100:ℝ)/A.D.e⌋₊+1),
      (cellRows A.D A.F Z idx grid k i j).Nonempty →
      ‖fullW A.D A.F η Z (cellRows A.D A.F Z idx grid k i j)
        (fun _=>51/100+A.D.e*j) (fun _=>(3*i+1:ℕ)*Z^τ)/normalizer A.D A.F Z‖ ≤
        C*Z^(cellTarget+A.D.t/8)

/-- The genuine normalized full-W cell theorem fixes its degree before height. -/
def ActualFullWCellInput (A : ChosenData) (J : ℝ) : Prop :=
  ∀τ : ℝ,HeightAdmissible A.D A.P J τ → ∀n : ℕ,∀η : Character,
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,∀C0 : ℝ,1≤C0 →
      SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ
        (C0*Z^A.D.t) (Z^(2*τ)) →
      FullWCellsAt A τ n η (C*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps)) Z

theorem cell_exponent_le (A : ChosenData) :
    cellTarget+A.D.t/4≤HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma := by
  have ht:=A.P.t_padding
  have hs:=A.P.sigma_small
  have hc:=A.count_budget
  have he:=A.D.epsilon_pos
  have htp:=A.D.t_pos
  dsimp [cellTarget]
  linarith

theorem fullW_sum_bound (A : ChosenData) (τ : ℝ) (n : ℕ) (η : Character)
    (C : ℝ) (hC : 0<C) :
    ∃Csum : ℝ,0<Csum ∧ ∀ᶠZ : ℝ in atTop,
      FullWCellsAt A τ n η C Z → ∀idx grid : FreeRow→ℕ,
      ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
        η rowPadding A.D.e τ n Z idx grid →
      ‖fullW A.D A.F η Z (selectedRows A.D A.F Z grid)
        (fun u=>51/100+A.D.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normalizer A.D A.F Z‖ ≤
        Csum*Z^(HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma) := by
  have ht:=A.D.t_pos
  obtain ⟨Cd,hCd,hdyad⟩:=canonical_dyad_cost (A.D.t/8) (by positivity)
  let m : ℕ:=⌊(49/100:ℝ)/A.D.e⌋₊
  refine ⟨Cd*(n+1:ℕ)*(m+1:ℕ)*C,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with Z hZ
  intro hcell idx grid hsel
  have hZp : 0<Z:=zero_lt_one.trans_le hZ
  have hrows:=selected_rows_facts A.D A.F Z grid
  have hb:=fullW_cells_norm_bound A.F.S A.F.exclusions A.F.maximal η
    (selectedRows A.D A.F Z grid) (primePool A.D A.F Z) (poolOutside A.D A.F Z)
    (fun _ y=>(A.F.w y:ℂ)) (fun j=>Z^(A.D.length j)) A.F.W A.F.W
    (Z^Arithmetic.x) (Z^Arithmetic.y) Z A.D.e (Z^τ) (Z^(Arithmetic.h+rowPadding))
    idx grid n m (normalizer A.D A.F Z) (C*Z^(cellTarget+A.D.t/8)) (by positivity)
    (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.2.2⟩)
    (fun u _=>⟨(hsel.1 u).2.1,(hsel.1 u).2.2.1⟩) (hcell idx grid hsel)
  have htop : Arithmetic.h+rowPadding≤1 := by norm_num [Arithmetic.h,rowPadding]
  have hd:=hdyad Z (Arithmetic.h+rowPadding) hZ htop
  have hexp:=Real.rpow_le_rpow_of_exponent_le hZ (cell_exponent_le A)
  calc
    _ ≤ ((smallDyadicIndices (Z^(Arithmetic.h+rowPadding))).card:ℝ)*(n+1:ℕ)*(m+1:ℕ)*
        (C*Z^(cellTarget+A.D.t/8)) := hb
    _ ≤ (Cd*Z^(A.D.t/8))*(n+1:ℕ)*(m+1:ℕ)*(C*Z^(cellTarget+A.D.t/8)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (by positivity)) (by positivity))
        (by positivity)
    _ = (Cd*(n+1:ℕ)*(m+1:ℕ)*C)*Z^(cellTarget+A.D.t/4) := by
      have hp : Z^(A.D.t/8)*Z^(cellTarget+A.D.t/8)=Z^(cellTarget+A.D.t/4) := by
        rw [←Real.rpow_add hZp]
        congr 1
        ring
      calc
        _ = (Cd*(n+1:ℕ)*(m+1:ℕ)*C)*(Z^(A.D.t/8)*Z^(cellTarget+A.D.t/8)) := by ring
        _ = _ := by rw [hp]
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
end
end Cycle61.FiniteNumerator

end
/- END ORIGINAL Cycle61.Numerator.Finite.Summation -/
