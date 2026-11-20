/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.NaturalPacketLowFinal
import Candidate.C092.transport.PacketJoinPrefactor
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeDetectorWitnessRows HeckeDetectorBatch
open HeckeDetectorFiberPartition HeckeDetectorRawFiber HeckeDetectorClassBudget
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor
open QRH.Cycle092.PacketJoin
namespace QRH.Cycle092.NaturalPacketLow
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

lemma natural_dyadic_cost_uniform (loss : ℝ) (hloss : 0 < loss) :
    ∃ L : ℝ,0 ≤ L ∧ ∀ᶠ Z : ℝ in atTop,1 ≤ Z ∧ ∀ d : ℝ,1/200 ≤ d →
      (dyadicLength (Z^d):ℝ)^2 ≤ L*(Z^d)^loss := by
  obtain ⟨L,hL,h⟩ := dyadic_cost_eventually loss hloss
  obtain ⟨b,hb⟩ := Filter.eventually_atTop.mp h
  refine ⟨L,hL,?_⟩
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/200)).eventually
    (eventually_ge_atTop b),eventually_ge_atTop (1:ℝ)] with Z hZb hZ
  refine ⟨hZ,fun d hd=>hb _ (hZb.trans ?_)⟩
  exact Real.rpow_le_rpow_of_exponent_le hZ hd

/-- Both occurrences of phase bins (the count and the final finite partition),
all original masks, and the dyadic logarithms are included. The degree and
constant precede the height exponent, order, scale and live cell. -/
theorem natural_prefactors_absorbed (D : BaselineData) (F : BaselineSourceData D)
    (K Cc : ℝ) (Jc : ℕ) (hCc : 0 < Cc)
    (degree : Finset (Fin D.N) → ℕ) (C : Finset (Fin D.N) → ℝ)
    (hC : ∀ J,0 < C J) (loss : ℝ) (hloss : 0 < loss) :
    ∃ m : ℕ,∃ C0 : ℝ,0 < C0 ∧ ∀ᶠ Z : ℝ in atTop,1 ≤ Z ∧
    ∀ d a τ : ℝ,1/200 ≤ d → d ≤ 7/8 → a ≤ 7/8 → 0 ≤ τ → ∀ i : ℕ,
    (Nat.card (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t):ℝ)*
      (∑ J∈Finset.univ.powerset,actualMaskWeight D F J K Cc (C J) Jc (degree J) Z d a τ i) ≤
    C0*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*
      Z^(-(4/25:ℝ)*Geometry.ell)*(Z^d)^loss := by
  obtain ⟨L,hL,hlog⟩ := natural_dyadic_cost_uniform loss hloss
  let B := phaseCardBound D
  let Q : ℝ := Nat.card (Sum Bool (RayQuotient.Characters F.modulus ⊤))
  let A : ℝ := 1+Q*192*Cc*max 1 K*B*L
  let m : ℕ := Jc+1+∑ J : Finset (Fin D.N),degree J
  let S : ℝ := ∑ J : Finset (Fin D.N), C J
  let C0 : ℝ := (1+B)*S*A*(2*Real.pi+2)^m
  have hB : 0 ≤ B := by dsimp [B,phaseCardBound];positivity
  have hQ : 0 ≤ Q := by dsimp [Q];positivity
  have hA : 1 ≤ A := by dsimp [A]; linarith [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hQ (by norm_num : (0:ℝ) ≤ 192)) hCc.le) (le_max_left 1 K |>.trans' zero_le_one)) hB) hL]
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hS : 0 < S := Finset.sum_pos (fun J _=>hC J) Finset.univ_nonempty
  have hC0 : 0 < C0 := by dsimp [C0];positivity
  refine ⟨m,C0,hC0,?_⟩
  filter_upwards [hlog] with Z hlog
  refine ⟨hlog.1,?_⟩
  intro d a τ hd hdhi ha hτ i
  have hZ0 : 0 < Z := zero_lt_one.trans_le hlog.1
  let H := nativeHeight Z d τ i
  let T : ℝ := 3+(3*i+1:ℕ)*Z^τ
  let U := Z^d
  let bc : ℝ := Nat.card (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t)
  have hbc : bc ≤ B := phase_card_le D a ha
  have hbc0 : 0 ≤ bc := by dsimp [bc];positivity
  have hH : 0 ≤ H := by dsimp [H,nativeHeight];positivity
  have hU : 1 ≤ U := Real.one_le_rpow hlog.1 (by linarith)
  have hUl : 1 ≤ U^loss := Real.one_le_rpow hU hloss.le
  have hH1 : 1 ≤ 1+H := by linarith
  have hcount : nativeCountPrefactor D F K Cc Jc Z d a τ i ≤ A*U^loss*(1+H)^(Jc+1) := by
    unfold nativeCountPrefactor
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA hUl) (one_le_pow₀ hH1)
    · change Q*(dyadicLength U:ℝ)^2*fiberConstant (Cc*(1+H)^Jc) H K*bc ≤ _
      calc
        _ = Q*192*Cc*max 1 K*bc*(dyadicLength U:ℝ)^2*(1+H)^(Jc+1) := by unfold fiberConstant;rw [pow_succ];ring
        _ ≤ Q*192*Cc*max 1 K*B*(L*U^loss)*(1+H)^(Jc+1) := by gcongr;exact hlog.2 d hd
        _ ≤ A*U^loss*(1+H)^(Jc+1) := by dsimp [A];nlinarith [mul_nonneg (by positivity : 0 ≤ U^loss) (by positivity : 0 ≤ (1+H)^(Jc+1))]
  have hm (J : Finset (Fin D.N)) : Jc+1+degree J ≤ m := by
    dsimp [m]
    exact Nat.add_le_add_left (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ J)) _
  have hheight : (1+H)^m ≤ (2*Real.pi+2)^m*T^m := by
    rw [←mul_pow]
    exact pow_le_pow_left₀ (by positivity) (nativeHeight_le Z d τ i hlog.1 hdhi hτ) _
  let front := (Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)
  have hf : 0 ≤ front := by dsimp [front];positivity
  have hmask (J : Finset (Fin D.N)) :
      actualMaskWeight D F J K Cc (C J) Jc (degree J) Z d a τ i ≤
      C J*A*U^loss*(2*Real.pi+2)^m*T^m*front := by
    have he : actualMaskWeight D F J K Cc (C J) Jc (degree J) Z d a τ i =
        C J*nativeCountPrefactor D F K Cc Jc Z d a τ i*(1+H)^(degree J)*front := by
      dsimp only [actualMaskWeight,front,H]
      rw [←prime_front_identity D J Z hZ0]
      ring
    have hCJ := (hC J).le
    have hCU : 0 ≤ C J*A*U^loss := by positivity
    rw [he]
    calc
      _ ≤ C J*(A*U^loss*(1+H)^(Jc+1))*(1+H)^(degree J)*front := by exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcount hCJ) (by positivity)) hf
      _ = C J*A*U^loss*(1+H)^(Jc+1+degree J)*front := by rw [pow_add];ring
      _ ≤ C J*A*U^loss*(1+H)^m*front := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH1 (hm J)) hCU) hf
      _ ≤ _ := by
        calc
          _ ≤ (C J*A*U^loss)*((2*Real.pi+2)^m*T^m)*front := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hheight hCU) hf
          _ = _ := by ring
  have hsum : (∑ J∈Finset.univ.powerset,actualMaskWeight D F J K Cc (C J) Jc (degree J) Z d a τ i) ≤
      S*A*U^loss*(2*Real.pi+2)^m*T^m*front := by
    calc
      _ ≤ ∑ J∈Finset.univ.powerset,C J*A*U^loss*(2*Real.pi+2)^m*T^m*front := Finset.sum_le_sum (fun J _=>hmask J)
      _ = S*A*U^loss*(2*Real.pi+2)^m*T^m*front := by simp only [Finset.powerset_univ];rw [←Finset.sum_mul,←Finset.sum_mul,←Finset.sum_mul,←Finset.sum_mul,←Finset.sum_mul]
  have hW0 : 0 ≤ ∑ J∈Finset.univ.powerset,actualMaskWeight D F J K Cc (C J) Jc (degree J) Z d a τ i := by
    apply Finset.sum_nonneg
    intro J hJ
    have hCJ := hC J
    unfold actualMaskWeight mainFront
    have hcp : 0 ≤ nativeCountPrefactor D F K Cc Jc Z d a τ i := zero_le_one.trans (le_max_left _ _)
    positivity
  calc
    _ ≤ B*(S*A*U^loss*(2*Real.pi+2)^m*T^m*front) := mul_le_mul hbc hsum hW0 hB
    _ ≤ (1+B)*(S*A*U^loss*(2*Real.pi+2)^m*T^m*front) := by gcongr;linarith
    _ = _ := by dsimp only [C0,front,U,T];ring

end QRH.Cycle092.NaturalPacketLow
#print axioms QRH.Cycle092.NaturalPacketLow.natural_prefactors_absorbed
