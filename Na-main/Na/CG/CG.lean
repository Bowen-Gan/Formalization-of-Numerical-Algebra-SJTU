import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.PosDef
import Na.CG.Defs

open Matrix Set Submodule

noncomputable section conjugate_gradient

def conjugate_gradient.stepsize {n: ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
  ((Fin n) → ℝ) → ((Fin n) → ℝ) → ℝ :=
  fun r p ↦ if r = 0 ∨ p = 0 then 0 else (r ⬝ᵥ r) / (p ⬝ᵥ (A *ᵥ p))

def conjugate_gradient.info {n: ℕ}  (A : Matrix (Fin n) (Fin n) ℝ) (x0 b : (Fin n) → ℝ)  :
    ℕ → (((Fin n) → ℝ) × ((Fin n) → ℝ) × ((Fin n) → ℝ) × ℝ × ℝ)
  | 0 =>
    let r0 := linearsystem.residual A b x0
    (x0, r0, r0, conjugate_gradient.stepsize A r0 r0, 0)
  | 1 =>
      let (x0, r0, p0, α0, _) := conjugate_gradient.info A x0 b 0
      let r1 := r0 - α0 • (A *ᵥ p0)
      let β1 := (r1 ⬝ᵥ r1) / (r0 ⬝ᵥ r0)
      (x0 + α0 • p0, r1, r1 + β1 • p0, conjugate_gradient.stepsize A r1 (r1 + β1 • p0), β1)
  | p + 2 =>
      let (x1, r1, p1, α1, _) := conjugate_gradient.info A x0 b (p + 1)
      let r2 := r1 - α1 • (A *ᵥ p1)
      let β2 := (r2 ⬝ᵥ r2) / (r1 ⬝ᵥ r1)
      (x1 + α1 • p1, r2, r2 + β2 • p1, conjugate_gradient.stepsize A r2 (r2 + β2 • p1), β2)

def conjugate_gradient.x {n: ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x0 b : (Fin n) → ℝ)  :
    ℕ → ((Fin n) → ℝ) := fun k ↦ (conjugate_gradient.info A x0 b k).1

def conjugate_gradient.r {n: ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x0 b : (Fin n) → ℝ)  :
    ℕ → ((Fin n) → ℝ) := fun k ↦ (conjugate_gradient.info A x0 b k).2.1

def conjugate_gradient.p {n: ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x0 b : (Fin n) → ℝ)  :
    ℕ → ((Fin n) → ℝ) := fun k ↦ (conjugate_gradient.info A x0 b k).2.2.1

def conjugate_gradient.α {n: ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x0 b : (Fin n) → ℝ)  :
    ℕ → ℝ := fun k ↦ (conjugate_gradient.info A x0 b k).2.2.2.1

def conjugate_gradient.β {n: ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x0 b : (Fin n) → ℝ)  :
    ℕ → ℝ := fun k ↦ (conjugate_gradient.info A x0 b k).2.2.2.2


variable (A : Matrix (Fin n) (Fin n) ℝ) (x0 b : (Fin n) → ℝ)
local notation "xk" => conjugate_gradient.x A x0 b
local notation "r" => conjugate_gradient.r A x0 b
local notation "p" => conjugate_gradient.p A x0 b
local notation "α" => conjugate_gradient.α A x0 b
local notation "β" => conjugate_gradient.β A x0 b
local notation "φ" => quad_func A b

lemma r0_eq_p0 : r 0 = p 0 := rfl
lemma r1_eq : r 1 = r 0 - α 0 • (A *ᵥ p 0) := rfl
lemma p1_eq : p 1 = r 1 + β 1 • p 0 := rfl
lemma α0_eq : α 0 = if r 0 = 0 ∨ p 0 = 0 then 0 else (r 0 ⬝ᵥ r 0) / (p 0 ⬝ᵥ (A *ᵥ p 0)) := rfl
lemma β1_eq : β 1 = (r 1 ⬝ᵥ r 1) / (r 0 ⬝ᵥ r 0) := rfl
lemma rk_eq : ∀ k, r (k + 1) = r k - α k • (A *ᵥ p k)
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

lemma αk_eq : ∀ k, α k = if r k = 0 ∨ p k = 0 then 0 else (r k ⬝ᵥ r k) / (p k ⬝ᵥ (A *ᵥ p k))
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

lemma βk_eq : ∀ k, β (k + 1) = (r (k + 1) ⬝ᵥ r (k + 1)) / (r k ⬝ᵥ r k)
  | 0 => by simp; rfl
  | 1 => by simp; rfl
  | _ + 2 => by rfl

lemma pk_eq : ∀ k, p (k + 1) = r (k + 1) + β (k + 1) • p k
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

lemma def_pos_def (hA : A.PosDef) : ∀ x : (Fin n → ℝ), x ≠ 0 → x ⬝ᵥ A *ᵥ x ≠ 0 := by
  intro x hx; obtain xtAx_pos := hA.2 x hx
  rw [star_trivial] at xtAx_pos; linarith

theorem ortho_pr_k_eq_1 (hA : A.PosDef): (p 0) ⬝ᵥ (r 1) = 0 := by
  rw [← r0_eq_p0, r1_eq, α0_eq]
  by_cases hr0 : r 0 = 0
  simp [hr0]
  push_neg at hr0
  have : p 0 ≠ 0 := hr0
  simp [this, r0_eq_p0]
  have h : p 0 ⬝ᵥ A *ᵥ p 0 ≠ 0 := def_pos_def A hA (p 0) this
  field_simp [h]

theorem ortho_rr_k_eq_1 (hA : A.PosDef) : (r 1) ⬝ᵥ (r 0) = 0 := by
  rw [r0_eq_p0, dotProduct_comm (r 1) (p 0)]
  exact ortho_pr_k_eq_1 A x0 b hA

theorem ortho_pAp_k_eq_1 (hA : A.PosDef) : (p 1) ⬝ᵥ (A *ᵥ (p 0)) = 0 := by
  calc
    _ = (r 1) ⬝ᵥ A *ᵥ r 0 + ((r 1 ⬝ᵥ r 0 -
      r 1 ⬝ᵥ conjugate_gradient.stepsize A (r 0) (r 0) • (A *ᵥ r 0)) / (r 0 ⬝ᵥ r 0))•(r 0) ⬝ᵥ (A *ᵥ (r 0)) := by
      simp [conjugate_gradient.r, conjugate_gradient.p, conjugate_gradient.info]
    _ = (r 1) ⬝ᵥ A *ᵥ r 0 + (-conjugate_gradient.stepsize A (r 0) (r 0)
      * (r 1 ⬝ᵥ  (A *ᵥ r 0)) / (r 0 ⬝ᵥ r 0)) • (r 0) ⬝ᵥ (A *ᵥ (r 0)) := by
      rw [ortho_rr_k_eq_1]; simp; exact hA
    _ = 0 := by
      by_cases i : r 0 = 0
      repeat simp [i, conjugate_gradient.stepsize]
      push_neg at i
      have h : r 0 ⬝ᵥ A *ᵥ r 0 ≠ 0 := def_pos_def A hA (r 0) i
      field_simp[i, h]; ring

lemma add_sub_Fin {a b c d : Fin n → ℝ} : a + (b - c + d) = a + d + b - c:= by
  ext j; simp; linarith

theorem span_eq_k_eq_1 : (span ℝ $ range (fun (i:Fin 2) => r i.val)) =
    (span ℝ $ range (fun (i:Fin 2) => p i.val)) := by
  ext x; repeat rw [mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩; simp at *; rw [← hc]
    let τ : Fin 2 → ℝ := fun k => if k = 0 then c 0 - c 1 * β 1 else c 1
    use τ; simp [τ, r1_eq, p1_eq,r0_eq_p0, sub_smul, smul_sub, add_sub_Fin, add_sub_assoc]
    rw [← smul_eq_mul (c 1) (β 1)]
    simp [Eq.symm (IsScalarTower.smul_assoc (c 1) (β 1) (p 0))]
  · rintro ⟨c, hc⟩; simp at *; rw [← hc]
    let τ : Fin 2 → ℝ := fun k => if k = 0 then c 0 + c 1 * β 1 else c 1
    use τ; simp [τ, r1_eq, p1_eq,r0_eq_p0, add_smul, smul_sub, add_sub_Fin, add_sub_assoc]
    rw [← smul_eq_mul (c 1) (β 1)]
    exact IsScalarTower.smul_assoc (c 1) (β 1) (p 0)

lemma ortho_α_k (k : ℕ) (h : k > 0 ∧ p (k - 1) ⬝ᵥ r k = 0) : α k = if r k = 0 ∨ p k = 0 then 0 else
    (r k ⬝ᵥ p k) / (p k ⬝ᵥ (A *ᵥ p k)) := by
  rw [αk_eq]; split_ifs
  · rfl
  by_cases hk : k = 0
  · rw [hk, r0_eq_p0]
  have : r k ⬝ᵥ r k = r k ⬝ᵥ p k := by
    let j := k - 1
    have : j + 1 = k := Nat.succ_pred_eq_of_ne_zero hk
    rw [← this, pk_eq]
    simp; right
    have : k - 1 + 1 = k := this
    rw [dotProduct_comm]; simp [j]; rw [this]; exact h.2
  rw [this]

lemma ortho_k_1 (hA : A.PosDef) (k : ℕ)
    (hcon : ∀ i j : Fin (k + 2), i < j → p i ⬝ᵥ r j = 0 ∧ r j ⬝ᵥ r i = 0 ∧ p j ⬝ᵥ A *ᵥ p i = 0) :
    ∀ (i j : Fin (k + 2 + 1)), i < j → p ↑i ⬝ᵥ r ↑j = 0 := by
  intro i j hij
  obtain hj := j.isLt
  by_cases hl : j.1 < k + 2
  · let j' : Fin (k + 2) := ⟨j.val, hl⟩
    let i' : Fin (k + 2) := ⟨i.val, Nat.lt_trans hij hl⟩
    obtain ⟨hk1, _, _⟩ := hcon i' j' hij
    exact hk1
  have hl : j.1 = k + 2 := by
    push_neg at hl
    exact Nat.eq_of_le_of_lt_succ hl hj
  rw [hl, rk_eq, dotProduct_sub]
  by_cases hr : i < k + 1
  · let i' : Fin (k + 2) := ⟨i.val, by linarith⟩
    let j' : Fin (k + 2) := ⟨k + 1, by simp⟩
    obtain ⟨hij1, _, hij2⟩ := hcon i' j' (by rw [Fin.mk_lt_mk]; linarith)
    rw [hij1]; simp; right
    rwa [inner_x_Ay_eq_inner_y_Ax A hA.1]
  have : i = k + 1 := by linarith [Nat.lt_of_lt_of_eq hij hl]
  rw [this]; rw [ortho_α_k]
  · split_ifs with h1
    · simp; rcases h1 with h1a | h1b
      · rw [h1a]; simp
      rw [h1b]; simp
    push_neg at h1
    simp; rw [dotProduct_comm]
    have : p (k + 1) ⬝ᵥ A *ᵥ p (k + 1) ≠ 0 := def_pos_def A hA (p (k + 1)) h1.2
    field_simp [this]
  constructor
  · exact Nat.zero_lt_succ k
  obtain ⟨heq, _, _⟩ := hcon ⟨k, by linarith⟩ ⟨k + 1, by linarith⟩ (Ici_subset_Ioi.mp fun ⦃a⦄ a ↦ a)
  convert heq

lemma finsum_dot_product_assoc (k : ℕ) (q1 : ℕ → Fin n → ℝ) (c : Fin k → ℝ) (q2: Fin n → ℝ) :
   (∑ (a:Fin k), c a • q1 a.val) ⬝ᵥ q2 = (∑ (a:Fin k), (c a • q1 a.val) ⬝ᵥ q2 ):= by
    let cq:=(λ (a:Fin k) =>(c a • q1 a.val) )
    have : ∀(a:Fin k),  (c a • q1 a.val)= cq a:=by simp[cq]
    simp_rw [this,dotProduct,Finset.sum_apply,Finset.sum_mul];rw[Finset.sum_comm]

lemma ortho_k_2 (hA : A.PosDef) (k : ℕ)
    (hcon1 : ∀ i j : Fin (k + 2), i < j → p i ⬝ᵥ r j = 0 ∧ r j ⬝ᵥ r i = 0 ∧ p j ⬝ᵥ A *ᵥ p i = 0)
    (hcon2 : (span ℝ $ range (fun (i : Fin (k+2)) => r i.val)) =
      (span ℝ $ range (fun (i : Fin (k+2)) => p i.val))) :
    ∀ (i j : Fin (k + 2 + 1)), i < j → r j ⬝ᵥ r i = 0 := by
    intro i j hij
    obtain hj := j.isLt
    have hli: i.1<k+2:=by
      apply Nat.lt_of_lt_of_le
      rw[Fin.lt_def] at hij
      apply hij
      exact Nat.le_of_lt_add_one hj
    by_cases hl : j.1 < k + 2
    · let j' : Fin (k + 2) := ⟨j.val, hl⟩
      let i' : Fin (k + 2) := ⟨i.val, hli⟩
      obtain ⟨_,hk1, _⟩ := hcon1 i' j' hij
      exact hk1
    have hl : j.1 = k + 2 := by
      push_neg at hl
      exact Nat.eq_of_le_of_lt_succ hl hj
    rw [hl,dotProduct_comm]
    let i' : Fin (k + 2) := ⟨i.val, hli⟩
    have decompose_r : ∃ (c : Fin (k + 2) → ℝ), ∑ a, c a • p ↑a = r ↑i := by
      rw[←mem_span_range_iff_exists_fun,hcon2.symm,mem_span_range_iff_exists_fun,(show i.val=i'.val from by simp[i'])]
      use (λ i => if i = i' then 1 else 0);simp
    rcases decompose_r with ⟨c,hc⟩;rw[hc.symm]
    rw [finsum_dot_product_assoc]
    apply Finset.sum_eq_zero
    intro x hx
    let x' : Fin (k + 3) :=
  ⟨x.val, Nat.lt_trans (show x.val < k + 2 from by simp) (show k + 2 < k + 3 from by norm_num)⟩
    obtain h_ortho_1:= ortho_k_1 A x0 b hA k hcon1 x' j (show x' < j from by rw [Fin.lt_def];have : x'.val = x.val := rfl;rw[this];simp[hl])
    rw [hl] at h_ortho_1
    have : x.val = x'.val := rfl
    rw [this]
    simp
    right
    exact h_ortho_1

lemma ortho_k_3 (hA : A.PosDef) (k : ℕ)
    (hcon : ∀ i j : Fin (k + 2), i < j → p i ⬝ᵥ r j = 0 ∧ r j ⬝ᵥ r i = 0 ∧ p j ⬝ᵥ A *ᵥ p i = 0)
    (hcon2 : (span ℝ $ range (fun (i : Fin (k + 2)) => r i.val)) =
      (span ℝ $ range (fun (i : Fin (k + 2)) => p i.val))) :
    ∀ (i j : Fin (k + 2 + 1)), i < j → p j ⬝ᵥ A *ᵥ p i = 0 := by
    intro i j hij
    obtain hj := j.isLt
    have hli: i.1<k+2:=by
      apply Nat.lt_of_lt_of_le
      rw[Fin.lt_def] at hij
      apply hij
      exact Nat.le_of_lt_add_one hj
    by_cases hl : j.1 < k + 2
    · let j' : Fin (k + 2) := ⟨j.val, hl⟩
      let i' : Fin (k + 2) := ⟨i.val, hli⟩
      obtain ⟨_,_, hk1⟩ := hcon i' j' hij
      exact hk1
    have hl : j.1 = k + 2 := by
      push_neg at hl
      exact Nat.eq_of_le_of_lt_succ hl hj
    rw[hl,pk_eq]
    have ortho_k_2:=ortho_k_2 A x0 b hA k hcon hcon2
    have ortho_k_2_k:=ortho_k_2 (j-1) j (by simp[hl,Fin.lt_def,Fin.sub_one_lt_iff.mpr])
    have ortho_k_2_i:=ortho_k_2 i j hij
    have hjsubone:(j-1).val=k+1:=by
      rw[Fin.sub_val_of_le,hl];norm_num;simp[Fin.le_def,hl]
    rw[hjsubone,hl] at ortho_k_2_k
    rw[hl] at ortho_k_2_i
    rw[add_dotProduct,βk_eq];nth_rw 3 [rk_eq];rw[dotProduct_sub]
    simp[show k+1+1=k+2 from by norm_num];rw[ortho_k_2_k,zero_sub]
    by_cases hi: i.val<k+1
    have hAp:α i.val≠0 → A *ᵥ p i.val = (1/α i.val) • (r i.val-r (i.val+1)):=by
      intro halpha
      rw[rk_eq,sub_sub_cancel,←smul_assoc];norm_num[halpha]
    by_cases hα : α i.val ≠0
    · nth_rw 1 [hAp]
      have ortho_k_2_i':=ortho_k_2 (i+1) j (by simp[hl,Fin.lt_def];rw[show ↑(i+1)=↑i+1 by exact Fin.val_add_one_of_lt hli];omega)
      rw[hl,show ↑(i+1)=↑i+1 by exact Fin.val_add_one_of_lt hli] at ortho_k_2_i'
      let j' : Fin (k + 2) := ⟨k+1, by omega⟩
      let i' : Fin (k + 2) := ⟨i.val, hli⟩
      obtain ⟨_,_, hk1⟩ := hcon i' j' (by exact hi)
      rw[show ↑j' = k+1 by rfl,show i'.1 = ↑i by rfl] at hk1
      simp[ortho_k_2_i,ortho_k_2_i',hk1]
      exact hα
    · push_neg at hα
      have hrp : r i=0 ∨ p i =0 := by
        by_contra h
        have hαk_eq := αk_eq A x0 b ↑i
        simp[h] at hαk_eq
        push_neg at h
        have : α ↑i ≠0 := by
          rw[hαk_eq]
          have := def_pos_def A hA (p i) h.2
          have : r i ⬝ᵥ r i ≠ 0 := by
            have h':=h.1
            contrapose! h'
            exact dotProduct_self_eq_zero.mp h'
          (expose_names; exact div_ne_zero this this_1)
        tauto
      obtain hr|hp := hrp
      · have hr_eq0: (i1 : ℕ) → (r i1 =0) → (i2 : ℕ) → i1 ≤ i2 → r i2 =0 := by
          intro i1 hri1 i2 hi2
          induction i2,hi2 using Nat.le_induction with
          | base => exact hri1
          | succ t ht ih =>
            rw[rk_eq]
            have :α t =0 := by simp[αk_eq,ih]
            simp[ih,this]
        have hk'_eq0:= hr_eq0 ↑i hr (k+1) (by omega)
        have hk''_eq0:= hr_eq0 ↑i hr (k+2) (by omega)
        simp[hk'_eq0,hk''_eq0]
      · simp[hp]
    have hi_eq : ↑i=k+1 := by exact Nat.eq_of_lt_succ_of_not_lt hli hi
    rw[hi_eq]
    by_cases hrp : ¬ (r (k+1) = 0 ∨ p (k+1) = 0)
    · have hα :=αk_eq A x0 b (k+1)
      simp[hrp] at hα
      rw[hα]
      push_neg at hrp
      have t1 := def_pos_def A hA (p (k+1)) hrp.2
      have t2 :r (k+1) ⬝ᵥ r (k+1) ≠ 0 := by
        have h':=hrp.1
        contrapose! h'
        exact dotProduct_self_eq_zero.mp h'
      let a := r (k + 2) ⬝ᵥ A *ᵥ p (k + 1)
      have ha : a = r (k + 2) ⬝ᵥ A *ᵥ p (k + 1) := rfl
      let b := r (k + 1) ⬝ᵥ r (k + 1)
      have hb :  b = r (k + 1) ⬝ᵥ r (k + 1) := rfl
      let c := p (k + 1) ⬝ᵥ A *ᵥ p (k + 1)
      have hc : c = p (k + 1) ⬝ᵥ A *ᵥ p (k + 1) := rfl
      rw[← ha,← hb,← hc]
      rw[← hc] at t1
      rw[← hb] at t2
      ring
      simp[t1,t2]
    · push_neg at hrp
      obtain hr|hp := hrp
      · have : r (k+2) =0 := by
          rw[rk_eq]
          rw[αk_eq]
          simp[hr]
        simp[hr,this]
      · simp[hp]

lemma ortho_k_4 (hA : A.PosDef) (k : ℕ)
    (hcon : ∀ i j : Fin (k + 2), i < j → p i ⬝ᵥ r j = 0 ∧ r j ⬝ᵥ r i = 0 ∧ p j ⬝ᵥ A *ᵥ p i = 0)
    (hcon2 : (span ℝ $ range (fun (i : Fin (k + 2)) => r i.val)) =
      (span ℝ $ range (fun (i : Fin (k + 2)) => p i.val))) :
    (span ℝ $ range (fun (i : Fin (k + 2 + 1)) => r i.val)) =
      (span ℝ $ range (fun (i : Fin (k + 2 + 1)) => p i.val)):= by
  ext x; repeat rw [mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨d, hd⟩
    let d':=fun (i : Fin (k + 2)) => d (Fin.ofNat (k+2+1) i.val)
    have hxrw :x=∑ i, d' i • r ↑i+ d (Fin.ofNat (k+2+1) k+2) • r (k+2) := by
      simp[d',←hd];rw [Fin.sum_univ_castSucc]
      simp [Fin.castSucc,Fin.last,Fin.add_def]
    have yin: (∑ i, d' i • r ↑i)  ∈ (span ℝ $ range (fun (i : Fin (k + 2 )) => r i.val)):=by
      simp[mem_span_range_iff_exists_fun]
    rw[hcon2,mem_span_range_iff_exists_fun] at yin
    rcases yin with ⟨c',hc'⟩
    let c:=fun (i : Fin (k +2+1)) =>  if i.val<k+1 then c' (Fin.ofNat (k+2) i.val) else (if i.val=k+1 then
    ((c' (Fin.ofNat (k+2) (k+1)) -d (Fin.ofNat (k+2+1) (k+2))  •  β (k+2))) else d (Fin.ofNat (k+2+1) (k+2)) )
    use c;rw[hxrw,←hc'];unfold c
    have: r (k+2)=p (k+2)-β (k+2) •p (k+1):=by
      simp[pk_eq]
    rw[this,smul_sub]
    rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
    rw [Finset.sum_range_succ]
    simp [Fin.ofNat]
    sorry
  · sorry

-- thm 5.2.1
theorem ortho_k (hA : A.PosDef) (k : ℕ) :
    (∀  (i j : Fin (k+2)), i < j → p i ⬝ᵥ r j = 0 ∧ r j ⬝ᵥ r i = 0 ∧ p j ⬝ᵥ A *ᵥ p i = 0) ∧
    (span ℝ $ range (fun (i : Fin (k+2)) => r i.val)) =
    (span ℝ $ range (fun (i : Fin (k+2)) => p i.val)) := by
  induction' k with k hk
  constructor
  · intro i j hij
    have hi: i = 0 ∧ j = 1 := by
      let i1 := i.val
      let j1 := j.val
      have : i1 = 0 ∧ j1 = 1 := by
        have : i1 < j1 := hij
        by_cases hi1 : i1 = 0
        · exact ⟨hi1, by linarith [j.isLt]⟩
        exfalso; push_neg at hi1
        linarith [Nat.zero_lt_of_ne_zero hi1, j.isLt]
      rcases this with ⟨h1, h2⟩
      simp [i1, j1] at h1 h2
      exact ⟨h1, Fin.eq_of_val_eq h2⟩
    simp [hi.1, hi.2]
    exact ⟨ortho_pr_k_eq_1 A x0 b hA, ortho_rr_k_eq_1 A x0 b hA,
        ortho_pAp_k_eq_1 A x0 b hA⟩
  exact span_eq_k_eq_1 A x0 b
  constructor
  swap
  · exact ortho_k_4 A x0 b hA k hk.1 hk.2
  intro i j hij
  constructor
  · exact ortho_k_1 A x0 b hA k hk.1 i j hij
  constructor
  · exact ortho_k_2 A x0 b hA k hk.1 hk.2 i j hij
  exact ortho_k_3 A x0 b hA k hk.1 hk.2 i j hij


-- #check span
-- #check mem_span_set'

end conjugate_gradient
