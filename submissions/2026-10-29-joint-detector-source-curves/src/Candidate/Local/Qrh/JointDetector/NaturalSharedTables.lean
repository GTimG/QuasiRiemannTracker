/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.NaturalSelectedNorm
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.QuadraticSieve.IdealQuotients

/-! The literal shared 25-table of two natural colour tuples. Residual
coordinates recover the complete original pair, and fixed-table selectors
retain the original finite family rather than replacing it by a rectangle. -/
namespace Qrh.JointDetector.NaturalSharedTables
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic
open CanonicalQuadraticSieve NaturalSelectedNorm
local notation "O" => ActualEisensteinCubic.O

abbrev SharedTable := Fin 5 → Fin 5 → Ideal O

def table (c d : ColourTuple) : SharedTable := fun j k => gcd (c j) (d k)
def rowProduct (g : SharedTable) (j : Fin 5) : Ideal O := ∏ k,g j k
def columnProduct (g : SharedTable) (k : Fin 5) : Ideal O := ∏ j,g j k

def leftResidual (c d : ColourTuple) : ColourTuple :=
  fun j => idealQuotient (rowProduct (table c d) j) (c j)
def rightResidual (c d : ColourTuple) : ColourTuple :=
  fun k => idealQuotient (columnProduct (table c d) k) (d k)

def recoverLeft (g : SharedTable) (a : ColourTuple) : ColourTuple := fun j => rowProduct g j*a j
def recoverRight (g : SharedTable) (b : ColourTuple) : ColourTuple := fun k => columnProduct g k*b k

theorem table_admissible {c d : ColourTuple} (hc : ∀ j,Admissible (c j)) :
    ∀ j k,Admissible (table c d j k) := by
  intro j k
  exact admissible_of_dvd (hc j) (gcd_dvd_left _ _)

theorem table_pairwise {c d : ColourTuple}
    (hc : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hd : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (table c d p.1 p.2) (table c d q.1 q.2)) := by
  rintro ⟨j,k⟩ ⟨l,m⟩ hpq
  by_cases hj : j=l
  · subst l
    have hk : k ≠ m := by intro h; exact hpq (Prod.ext rfl h)
    exact ((hd hk).of_isCoprime_of_dvd_left (gcd_dvd_right _ _)).of_isCoprime_of_dvd_right
      (gcd_dvd_right _ _)
  · exact ((hc hj).of_isCoprime_of_dvd_left (gcd_dvd_left _ _)).of_isCoprime_of_dvd_right
      (gcd_dvd_left _ _)

theorem rowProduct_dvd {c d : ColourTuple}
    (hd : Pairwise (fun j k => IsCoprime (d j) (d k))) (j : Fin 5) :
    rowProduct (table c d) j ∣ c j := by
  apply Fintype.prod_dvd_of_coprime
  · intro k l hkl
    exact ((hd hkl).of_isCoprime_of_dvd_left (gcd_dvd_right _ _)).of_isCoprime_of_dvd_right
      (gcd_dvd_right _ _)
  · intro k
    exact gcd_dvd_left _ _

theorem columnProduct_dvd {c d : ColourTuple}
    (hc : Pairwise (fun j k => IsCoprime (c j) (c k))) (k : Fin 5) :
    columnProduct (table c d) k ∣ d k := by
  apply Fintype.prod_dvd_of_coprime
  · intro j l hjl
    exact ((hc hjl).of_isCoprime_of_dvd_left (gcd_dvd_left _ _)).of_isCoprime_of_dvd_right
      (gcd_dvd_left _ _)
  · intro j
    exact gcd_dvd_right _ _

theorem recover_left {c d : ColourTuple}
    (hd : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    recoverLeft (table c d) (leftResidual c d)=c := by
  funext j
  exact idealQuotient_mul (rowProduct_dvd hd j)

theorem recover_right {c d : ColourTuple}
    (hc : Pairwise (fun j k => IsCoprime (c j) (c k))) :
    recoverRight (table c d) (rightResidual c d)=d := by
  funext k
  exact idealQuotient_mul (columnProduct_dvd hc k)

theorem leftResidual_dvd {c d : ColourTuple}
    (hd : Pairwise (fun j k => IsCoprime (d j) (d k))) (j : Fin 5) :
    leftResidual c d j ∣ c j := idealQuotient_dvd (rowProduct_dvd hd j)

theorem rightResidual_dvd {c d : ColourTuple}
    (hc : Pairwise (fun j k => IsCoprime (c j) (c k))) (k : Fin 5) :
    rightResidual c d k ∣ d k := idealQuotient_dvd (columnProduct_dvd hc k)

private theorem coprime_of_relprime {I J : Ideal O} (h : IsRelPrime I J) : IsCoprime I J :=
  Ideal.isCoprime_iff_gcd.mpr (isUnit_iff_eq_one.mp (gcd_isUnit_iff_isRelPrime.mpr h))

/-- The left residual is coprime to the ENTIRE opposite colour, including
all of its shared-table factors. -/
theorem leftResidual_coprime_right {c d : ColourTuple}
    (hc : ∀ j,Admissible (c j))
    (hd : Pairwise (fun j k => IsCoprime (d j) (d k))) (j k : Fin 5) :
    IsCoprime (leftResidual c d j) (d k) := by
  apply coprime_of_relprime
  intro I hIl hIr
  have hrec : rowProduct (table c d) j*leftResidual c d j=c j :=
    congrFun (recover_left hd) j
  have hsf : Squarefree (rowProduct (table c d) j*leftResidual c d j) := by
    rw [hrec]
    exact (hc j).2.1
  have hIg : I ∣ table c d j k := dvd_gcd (hIl.trans (leftResidual_dvd hd j)) hIr
  exact IsRelPrime.of_squarefree_mul hsf
    (hIg.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))) hIl

theorem rightResidual_coprime_left {c d : ColourTuple}
    (hd : ∀ k,Admissible (d k))
    (hc : Pairwise (fun j k => IsCoprime (c j) (c k))) (j k : Fin 5) :
    IsCoprime (rightResidual c d k) (c j) := by
  apply coprime_of_relprime
  intro I hIr hIl
  have hrec : columnProduct (table c d) k*rightResidual c d k=d k :=
    congrFun (recover_right hc) k
  have hsf : Squarefree (columnProduct (table c d) k*rightResidual c d k) := by
    rw [hrec]
    exact (hd k).2.1
  have hIg : I ∣ table c d j k := dvd_gcd hIl (hIr.trans (rightResidual_dvd hc k))
  exact IsRelPrime.of_squarefree_mul hsf
    (hIg.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))) hIr

theorem residuals_admissible {c d : ColourTuple}
    (hc : ∀ j,Admissible (c j)) (hd : ∀ j,Admissible (d j))
    (hpc : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hpd : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    (∀ j,Admissible (leftResidual c d j)) ∧ (∀ k,Admissible (rightResidual c d k)) :=
  ⟨fun j => admissible_idealQuotient (hc j) (rowProduct_dvd hpd j),
    fun k => admissible_idealQuotient (hd k) (columnProduct_dvd hpc k)⟩

theorem leftResidual_pairwise {c d : ColourTuple}
    (hc : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hd : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    Pairwise (fun j k => IsCoprime (leftResidual c d j) (leftResidual c d k)) := by
  intro j k hjk
  exact ((hc hjk).of_isCoprime_of_dvd_left (leftResidual_dvd hd j)).of_isCoprime_of_dvd_right
    (leftResidual_dvd hd k)

theorem rightResidual_pairwise {c d : ColourTuple}
    (hc : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hd : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    Pairwise (fun j k => IsCoprime (rightResidual c d j) (rightResidual c d k)) := by
  intro j k hjk
  exact ((hd hjk).of_isCoprime_of_dvd_left (rightResidual_dvd hc j)).of_isCoprime_of_dvd_right
    (rightResidual_dvd hc k)

theorem leftResidual_coprime_table {c d : ColourTuple}
    (hc : ∀ j,Admissible (c j))
    (hd : Pairwise (fun j k => IsCoprime (d j) (d k))) (j l k : Fin 5) :
    IsCoprime (leftResidual c d j) (table c d l k) :=
  (leftResidual_coprime_right hc hd j k).of_isCoprime_of_dvd_right (gcd_dvd_right _ _)

theorem rightResidual_coprime_table {c d : ColourTuple}
    (hd : ∀ j,Admissible (d j))
    (hc : Pairwise (fun j k => IsCoprime (c j) (c k))) (k j l : Fin 5) :
    IsCoprime (rightResidual c d k) (table c d j l) :=
  (rightResidual_coprime_left hd hc j k).of_isCoprime_of_dvd_right (gcd_dvd_left _ _)

theorem residual_cross_coprime {c d : ColourTuple}
    (hc : ∀ j,Admissible (c j))
    (hpc : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hpd : Pairwise (fun j k => IsCoprime (d j) (d k))) (j k : Fin 5) :
    IsCoprime (leftResidual c d j) (rightResidual c d k) :=
  (leftResidual_coprime_right hc hpd j k).of_isCoprime_of_dvd_right (rightResidual_dvd hpc k)

def residualPair (p : ColourTuple × ColourTuple) : ColourTuple × ColourTuple :=
  (leftResidual p.1 p.2,rightResidual p.1 p.2)
def recoverPair (g : SharedTable) (p : ColourTuple × ColourTuple) : ColourTuple × ColourTuple :=
  (recoverLeft g p.1,recoverRight g p.2)

def pairFibre (F : Finset ColourTuple) (g : SharedTable) : Finset (ColourTuple × ColourTuple) :=
  (F.product F).filter (fun p => table p.1 p.2=g)
def residualFibre (F : Finset ColourTuple) (g : SharedTable) : Finset (ColourTuple × ColourTuple) :=
  (pairFibre F g).image residualPair

theorem recover_pair {c d : ColourTuple}
    (hc : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hd : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    recoverPair (table c d) (residualPair (c,d))=(c,d) :=
  Prod.ext (recover_left hd) (recover_right hc)

theorem recover_pair_of_mem {F : Finset ColourTuple} {g : SharedTable}
    (hF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    {p : ColourTuple × ColourTuple} (hp : p ∈ pairFibre F g) :
    recoverPair g (residualPair p)=p := by
  obtain ⟨hp,hg⟩ := Finset.mem_filter.mp hp
  have hp' := Finset.mem_product.mp hp
  have he := recover_pair (hF p.1 hp'.1) (hF p.2 hp'.2)
  rwa [hg] at he

theorem residualPair_injOn (F : Finset ColourTuple) (g : SharedTable)
    (hF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k))) :
    Set.InjOn residualPair (pairFibre F g) := by
  intro p hp q hq he
  rw [← recover_pair_of_mem hF hp,← recover_pair_of_mem hF hq,he]

private theorem quotient_mul_cancel (D I : Ideal O) (hD : D ≠ 0) :
    idealQuotient D (D*I)=I := by
  apply mul_left_cancel₀ hD
  exact idealQuotient_mul (show D ∣ D*I from ⟨I,rfl⟩)

theorem residual_recover {g : SharedTable} (hg : ∀ j k,g j k ≠ 0)
    (a b : ColourTuple) (ht : table (recoverLeft g a) (recoverRight g b)=g) :
    residualPair (recoverPair g (a,b))=(a,b) := by
  apply Prod.ext
  · funext j
    change idealQuotient (rowProduct (table (recoverLeft g a) (recoverRight g b)) j)
      (rowProduct g j*a j)=a j
    rw [ht]
    exact quotient_mul_cancel _ _ (Finset.prod_ne_zero_iff.mpr (fun k _ => hg j k))
  · funext k
    change idealQuotient (columnProduct (table (recoverLeft g a) (recoverRight g b)) k)
      (columnProduct g k*b k)=b k
    rw [ht]
    exact quotient_mul_cancel _ _ (Finset.prod_ne_zero_iff.mpr (fun j _ => hg j k))

/-- Exact finite selector before factorization; it retains every restriction
of the original (possibly nonrectangular) tuple family. -/
theorem mem_residualFibre_iff {F : Finset ColourTuple} {g : SharedTable}
    (hF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hg : ∀ j k,g j k ≠ 0) (r : ColourTuple × ColourTuple) :
    r ∈ residualFibre F g ↔ recoverPair g r ∈ F.product F ∧
      table (recoverLeft g r.1) (recoverRight g r.2)=g := by
  constructor
  · intro hr
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
    have he := recover_pair_of_mem hF hp
    have hp' := Finset.mem_filter.mp hp
    refine ⟨?_,?_⟩
    · rw [he]
      exact hp'.1
    · change table (recoverPair g (residualPair p)).1 (recoverPair g (residualPair p)).2=g
      rw [he]
      exact hp'.2
  · rintro ⟨hp,ht⟩
    apply Finset.mem_image.mpr
    exact ⟨recoverPair g r,Finset.mem_filter.mpr ⟨hp,ht⟩,residual_recover hg r.1 r.2 ht⟩

/-- Recovered cross-gcds are exactly the fixed table when all unshared
cross factors are coprime. This is the arithmetic converse used by selectors. -/
theorem table_recover {g : SharedTable}
    (hg : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    {a b : ColourTuple}
    (ha : ∀ j l k,IsCoprime (a j) (g l k))
    (hb : ∀ k j l,IsCoprime (b k) (g j l))
    (hab : ∀ j k,IsCoprime (a j) (b k)) :
    table (recoverLeft g a) (recoverRight g b)=g := by
  funext j k
  let left : Ideal O := ∏ l ∈ Finset.univ.erase k,g j l
  let right : Ideal O := ∏ i ∈ Finset.univ.erase j,g i k
  have hlr : IsCoprime left right := by
    apply IsCoprime.prod_left
    intro l hl
    apply IsCoprime.prod_right
    intro i hi
    exact @hg (j,l) (i,k) (by
      intro he
      exact (Finset.mem_erase.mp hi).1 (congrArg Prod.fst he).symm)
  have hlb : IsCoprime left (b k) := by
    apply IsCoprime.prod_left
    intro l hl
    exact (hb k j l).symm
  have har : IsCoprime (a j) right := by
    apply IsCoprime.prod_right
    intro i hi
    exact ha j i k
  have hrest : IsCoprime (left*a j) (right*b k) :=
    (hlr.mul_right hlb).mul_left (har.mul_right (hab j k))
  have hrow : rowProduct g j=g j k*left :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ k)).symm
  have hcol : columnProduct g k=g j k*right :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
  change gcd (rowProduct g j*a j) (columnProduct g k*b k)=g j k
  rw [hrow,hcol]
  calc
    gcd ((g j k*left)*a j) ((g j k*right)*b k) =
      gcd (g j k*(left*a j)) (g j k*(right*b k)) := by rw [mul_assoc,mul_assoc]
    _ = normalize (g j k)*gcd (left*a j) (right*b k) := gcd_mul_left _ _ _
    _ = g j k := by rw [normalize_eq,Ideal.isCoprime_iff_gcd.mp hrest,mul_one]

/-- Independent left constraints at a fixed table. -/
def LeftOK (F : Finset ColourTuple) (g : SharedTable) (a : ColourTuple) : Prop :=
  recoverLeft g a ∈ F ∧ (∀ j,Admissible (a j)) ∧
    Pairwise (fun j k => IsCoprime (a j) (a k)) ∧ ∀ j l k,IsCoprime (a j) (g l k)
/-- Independent right constraints at a fixed table. -/
def RightOK (F : Finset ColourTuple) (g : SharedTable) (b : ColourTuple) : Prop :=
  recoverRight g b ∈ F ∧ (∀ k,Admissible (b k)) ∧
    Pairwise (fun j k => IsCoprime (b j) (b k)) ∧ ∀ k j l,IsCoprime (b k) (g j l)

/-- The exact selector factorizes into independent residual choices and
literal cross-coprime selectors. No opaque two-pivot table predicate remains. -/
theorem mem_residualFibre_iff_factorized {F : Finset ColourTuple} {g : SharedTable}
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hgn : ∀ j k,g j k ≠ 0)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (r : ColourTuple × ColourTuple) :
    r ∈ residualFibre F g ↔ LeftOK F g r.1 ∧ RightOK F g r.2 ∧
      ∀ j k,IsCoprime (r.1 j) (r.2 k) := by
  constructor
  · intro hr
    obtain ⟨⟨c,d⟩,hp,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hp,ht⟩ := Finset.mem_filter.mp hp
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hp
    have hpc := hpF c hc
    have hpd := hpF d hd
    have hca := hF c hc
    have hda := hF d hd
    have hadm := residuals_admissible hca hda hpc hpd
    refine ⟨⟨?_,hadm.1,leftResidual_pairwise hpc hpd,?_⟩,
      ⟨?_,hadm.2,rightResidual_pairwise hpc hpd,?_⟩,
      residual_cross_coprime hca hpc hpd⟩
    · change recoverLeft g (leftResidual c d) ∈ F
      rw [← ht,recover_left hpd]
      exact hc
    · intro j l k
      rw [← ht]
      exact leftResidual_coprime_table hca hpd j l k
    · change recoverRight g (rightResidual c d) ∈ F
      rw [← ht,recover_right hpc]
      exact hd
    · intro k j l
      rw [← ht]
      exact rightResidual_coprime_table hda hpc k j l
  · rintro ⟨hl,hr,hcross⟩
    apply (mem_residualFibre_iff hpF hgn r).2
    exact ⟨Finset.mem_product.mpr ⟨hl.1,hr.1⟩,table_recover hgp hl.2.2.2 hr.2.2.2 hcross⟩

/-- Exact finite reindexing of arbitrary coefficients/kernels at fixed g.
No enlargement of a selected fibre is made. -/
theorem sum_reindex {M : Type*} [AddCommMonoid M] (F : Finset ColourTuple) (g : SharedTable)
    (hF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (f : (ColourTuple × ColourTuple) → M) :
    (∑ r ∈ residualFibre F g,f (recoverPair g r)) = ∑ p ∈ pairFibre F g,f p := by
  rw [residualFibre,Finset.sum_image (residualPair_injOn F g hF)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [recover_pair_of_mem hF hp]

theorem coefficient_mass_reindex (F : Finset ColourTuple) (g : SharedTable)
    (hF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (a : (ColourTuple × ColourTuple) → ℂ) :
    (∑ r ∈ residualFibre F g,‖a (recoverPair g r)‖^2) = ∑ p ∈ pairFibre F g,‖a p‖^2 :=
  sum_reindex F g hF (fun p => ‖a p‖^2)

/-- Separate the only free-pivot selector from the two pivot/higher masks
and the common higher/higher mask. The latter depends only on higher tuples. -/
theorem cross_coprime_split (a b : ColourTuple) :
    (∀ j k,IsCoprime (a j) (b k)) ↔
      IsCoprime (a 0) (b 0) ∧
      (∀ k,IsCoprime (a 0) (higherTuple b k)) ∧
      (∀ j,IsCoprime (higherTuple a j) (b 0)) ∧
      (∀ j k,IsCoprime (higherTuple a j) (higherTuple b k)) := by
  constructor
  · intro h
    exact ⟨h 0 0,(fun k => h 0 k.succ),(fun j => h j.succ 0),(fun j k => h j.succ k.succ)⟩
  · rintro ⟨h00,h0h,hh0,hhh⟩ j k
    refine Fin.cases ?_ (fun j => ?_) j
    · exact Fin.cases h00 (fun k => h0h k) k
    · exact Fin.cases (hh0 j) (fun k => hhh j k) k

/-- The exact selector in the form consumed by the mixed-pair packet:
only the first displayed cross mask couples the two free pivots. -/
theorem mem_residualFibre_iff_pivots {F : Finset ColourTuple} {g : SharedTable}
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hgn : ∀ j k,g j k ≠ 0)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (r : ColourTuple × ColourTuple) :
    r ∈ residualFibre F g ↔ LeftOK F g r.1 ∧ RightOK F g r.2 ∧
      IsCoprime (r.1 0) (r.2 0) ∧
      (∀ k,IsCoprime (r.1 0) (higherTuple r.2 k)) ∧
      (∀ j,IsCoprime (higherTuple r.1 j) (r.2 0)) ∧
      (∀ j k,IsCoprime (higherTuple r.1 j) (higherTuple r.2 k)) := by
  rw [mem_residualFibre_iff_factorized hF hpF hgn hgp,cross_coprime_split]

end
end Qrh.JointDetector.NaturalSharedTables

#print axioms Qrh.JointDetector.NaturalSharedTables.recover_left
#print axioms Qrh.JointDetector.NaturalSharedTables.residual_cross_coprime

#print axioms Qrh.JointDetector.NaturalSharedTables.mem_residualFibre_iff_factorized
#print axioms Qrh.JointDetector.NaturalSharedTables.coefficient_mass_reindex

#print axioms Qrh.JointDetector.NaturalSharedTables.mem_residualFibre_iff_pivots
