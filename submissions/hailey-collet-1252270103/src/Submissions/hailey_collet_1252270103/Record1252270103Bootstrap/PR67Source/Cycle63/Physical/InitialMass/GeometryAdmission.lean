import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometrySources
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.JointAmplification
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FirstAnnularAdmission
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentFirstPhysicalSource
open CenteredMomentFirstCanonicalFamily CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstReferenceSource CenteredMomentFirstScale CenteredMomentCommonSupport
open CenteredMomentSourceRow CenteredMomentWholeDivisorShell CenteredMomentSourceMass
open CenteredMomentExceptionalAmplitudePair CenteredMomentSectorLocalization
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentFirstSectors CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O

/-- A first residual projector divides an actual column. This uses a bound
on the actual finite pool, not an assertion that every padded column has
nonzero coefficient. -/
theorem first_divisor_norm (s : FirstBlockSource) (Y : ℝ)
    (hpool : ∀I∈s.pool,(I.absNorm:ℝ)≤Y) (L : s.divisors) :
    L.val≠0 ∧ (L.val.absNorm:ℝ)≤Y := by
  apply divisorPool_nonzero_norm Finset.univ
    (fun i : s.RightIndex=>Ideal.span {element s.C s.D s.hD.1 s.pool i})
    (fun i _=>by rw [element_span];exact (column_supported _ _ _ _ i).1) Y _ L.val L.property
  intro i _
  rw [element_span]
  have hmem := (mem_residualPool s.D s.hD.1 (supportedColumns s.pool) i.val).mp
    (Finset.mem_filter.mp i.property).1
  have hd : s.D*i.val≠0 := (Finset.mem_filter.mp hmem).2.1
  exact (CenteredMomentFirstSourceConductorCaps.divisor_norm_le i.val (s.D*i.val) hd
    (dvd_mul_left _ _)).trans (hpool _ (Finset.mem_filter.mp hmem).1)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance geometryAdmissionDecidableSum : DecidableEq (ι⊕Fin 2) := Classical.decEq _

omit [DecidableEq ι] in
/-- A coarse finite-pool bound is sufficient for amplifier admission. It
includes padded zero-coefficient columns and costs no source-mass factor. -/
theorem actual_finite_pool_cap (s : Input ι) (N : ℕ) (Z U : ℝ)
    (hN : Fintype.card ι≤N) (hZ : 1≤Z) (hU : 0≤U)
    (hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤Z^U) :
    ∀I∈finiteColumns (Fintype.piFinset s.pools),(I.absNorm:ℝ)≤Z^(((N:ℝ)+2)*U) := by
  intro I hI
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
  have he : ((CenteredMomentAddedZeroUniform.finiteTupleProduct v).absNorm:ℝ)=
      ∏j,((v j).absNorm:ℝ) := by
    simp only [CenteredMomentAddedZeroUniform.finiteTupleProduct,map_prod,Nat.cast_prod]
  rw [he]
  calc
    _ ≤ ∏_j : ι⊕Fin 2,Z^U :=
      Finset.prod_le_prod₀ (fun _ _=>Nat.cast_nonneg _)
        (fun j _=>hpool j (v j) ((Fintype.mem_piFinset.mp hv) j))
    _ = Z^(((Fintype.card ι:ℝ)+2)*U) := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
      rw [←Real.rpow_mul_natCast (zero_le_one.trans hZ)]
      congr 1
      push_cast
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ
      (mul_le_mul_of_nonneg_right (show (Fintype.card ι:ℝ)+2≤(N:ℝ)+2 by
        exact_mod_cast Nat.add_le_add_right hN 2) hU)

omit [DecidableEq ι] in
/-- The standard completed plain pools obey their advertised cutoff even
when they include values at which the smooth profile vanishes. -/
theorem actual_completed_pool_cap (s : Input ι) (Y : ℝ)
    (hslot : ∀i I,I∈s.slots i→(I.absNorm:ℝ)≤Y)
    (hp₁ : s.plain₁=CenteredMomentSourceRectangle.plainSupportPool s.b₁ s.X₁ s.Y₁)
    (hp₂ : s.plain₂=CenteredMomentSourceRectangle.plainSupportPool s.b₂ s.X₂ s.Y₂)
    (hx₁ : s.b₁*s.X₁≤Y) (hy₁ : s.b₁*s.Y₁≤Y)
    (hx₂ : s.b₂*s.X₂≤Y) (hy₂ : s.b₂*s.Y₂≤Y) :
    ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤Y := by
  intro j I hi
  cases j with
  | inl i => exact hslot i I hi
  | inr i =>
    fin_cases i
    · change I∈s.plain₁ at hi
      rw [hp₁] at hi
      rcases Finset.mem_union.mp hi with hx|hy
      · exact ((mem_idealBall _ _).mp hx).2.trans hx₁
      · exact ((mem_idealBall _ _).mp hy).2.trans hy₁
    · change I∈s.plain₂ at hi
      rw [hp₂] at hi
      rcases Finset.mem_union.mp hi with hx|hy
      · exact ((mem_idealBall _ _).mp hx).2.trans hx₂
      · exact ((mem_idealBall _ _).mp hy).2.trans hy₂

def geometryBranch (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) : FirstBranchGeometry :=
  let src := geometryFirstSource s R seed K Z ξ hK key j.1
  { R := R*geometryColumnIdeal reflected s R seed K Z ξ hK key j
    seed := j.2.1.val
    I := src.C
    J := src.D
    E := Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val) src.inactive}
    d := Real.logb Z ((if reflected then src.C else src.D).absNorm:ℝ)
    cLog := Real.logb Z ((geometryColumnIdeal reflected s R seed K Z ξ hK key j).absNorm:ℝ)
    K := K
    X := volume s.toData
    Tsec := firstNominalScale src.C src.D
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val) src.inactive})
      K (volume s.toData)
    H0 := src.H0 }

omit [DecidableEq ι] in
/-- Actual live first columns satisfy amplification's geometric gates.
Both reflected and unreflected columns retain the original annular scale. -/
theorem actual_geometry_admission (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ A D ξcap B BR Bs : ℝ) (hK : 0<K) (hZ : 32≤Z)
    (hξ : ξ≤ξcap) (hV : volume s.toData≤Z^A) (hKi : K⁻¹≤Z^D)
    (hR : R≠0) (hRn : (R.absNorm:ℝ)≤Z^BR)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B)
    (hpool : ∀I∈finiteColumns (Fintype.piFinset s.pools),(I.absNorm:ℝ)≤Z^Bs)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) :
    (geometryBranch reflected s R seed K Z ξ hK key j).Eligible
      Z (BR+B) Bs (amplifierCap A D ξcap) 1 ξ := by
  let src := geometryFirstSource s R seed K Z ξ hK key j.1
  have hC : Supported (geometryColumnIdeal reflected s R seed K Z ξ hK key j) := by
    cases reflected
    · exact src.hC
    · exact src.hD
  have hn : ((geometryColumnIdeal reflected s R seed K Z ξ hK key j).absNorm:ℝ)≤Z^B := by
    cases reflected
    · exact (actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource j.1.val 0).2
    · exact (actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource j.1.val 1).2
  have hL := first_divisor_norm src (Z^Bs) hpool j.2.1
  have he := (subsetGenerator_supported src.C src.D src.hC src.inactive).1
  have hh := source_amplifier_packet A D ξcap Z hZ s R seed K ξ hK hξ hV hKi
    j.1.val.1 j.1.val.2.1.val j.1.val.2.2
  rw [source_nominal_span] at hh
  refine ⟨mul_ne_zero hR hC.1,hL.1,?_,hL.2,he,hK,
    volume_pos s.toData,(by simp [geometryBranch]),src.H0_pos,hh.2.2.1,hh.2.2.2.1⟩
  change ((R*geometryColumnIdeal reflected s R seed K Z ξ hK key j).absNorm:ℝ)≤Z^(BR+B)
  rw [map_mul,Nat.cast_mul,Real.rpow_add (by linarith : 0<Z)]
  exact mul_le_mul hRn hn (Nat.cast_nonneg _) (Real.rpow_nonneg (by linarith) _)

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
