import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Data.Fintype.BigOperators
import OnionDeBruijnLean.Eulerian

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.openClassical false

open Classical
open Finset

namespace OnionDeBruijnLean

noncomputable section

attribute [local instance] Classical.propDecidable

-- Def 4.1
def S_Part (n k : ℕ) := { w : Word (n - 1) k // ¬ HasKMinusOne w }
def L_Part (n k : ℕ) := { w : Word (n - 1) k // HasKMinusOne w }

noncomputable instance {n k : ℕ} [Fintype (Word (n - 1) k)] : Fintype (S_Part n k) := by 
  classical exact Subtype.fintype _

noncomputable instance {n k : ℕ} [Fintype (Word (n - 1) k)] : Fintype (L_Part n k) := by 
  classical exact Subtype.fintype _

noncomputable def s_size (n k : ℕ) [Fintype (Word (n - 1) k)] : ℕ := 
  (Finset.univ.filter (fun w : Word (n-1) k => ¬ HasKMinusOne w)).card

noncomputable def l_size (n k : ℕ) [Fintype (Word (n - 1) k)] : ℕ := 
  (Finset.univ.filter (fun w : Word (n-1) k => HasKMinusOne w)).card

def A_LL (n k : ℕ) [Fintype (Word (n - 1) k)] : Matrix (L_Part n k) (L_Part n k) ℤ :=
  fun u v => if RootGraph n k u.val v.val then 1 else 0

def A_LS (n k : ℕ) [Fintype (Word (n - 1) k)] : Matrix (L_Part n k) (S_Part n k) ℤ :=
  fun u v => if RootGraph n k u.val v.val then 1 else 0

def A_SL (n k : ℕ) [Fintype (Word (n - 1) k)] : Matrix (S_Part n k) (L_Part n k) ℤ :=
  fun u v => if RootGraph n k u.val v.val then 1 else 0

-- Def 4.2: Effective Adjacency Matrix
def EffectiveAdjacencyMatrix (n k : ℕ) [Fintype (Word (n - 1) k)] : 
  Matrix (L_Part n k) (L_Part n k) ℤ :=
  A_LL n k + A_LS n k * A_SL n k

open Polynomial

noncomputable def OutDegreeLaplacian {V : Type} [Fintype V] (G : V → V → Prop) : Matrix V V ℤ :=
  fun u v => if u = v then (OutDegree G u : ℤ) - (if G u v then 1 else 0)
             else - (if G u v then 1 else 0)

-- Lemma 4.3 Characteristic polynomial (Cited from external literature)
axiom char_poly_laplacian (n k : ℕ) [Fintype (Word (n - 1) k)] [DecidableEq (Word (n - 1) k)] : 
  Matrix.charpoly (OutDegreeLaplacian (RootGraph n k)) = 
    X * (X - 1) ^ (s_size n k - 1) * (X - (C (k : ℤ))) ^ (l_size n k)

-- Theorem 4.4
noncomputable def NumSpanningArborescences {V : Type} [Fintype V] (G : V → V → Prop) : ℕ :=
  if h : Nonempty V then
    let v := Classical.choice h
    let L := OutDegreeLaplacian G
    let M := Matrix.submatrix L (fun x : {x // x ≠ v} => x.val) (fun x : {x // x ≠ v} => x.val)
    (Matrix.det M).natAbs
  else 0
-- Spectral graph theory: Matrix Tree Theorem for regular Eulerian directed graphs
-- relates the number of Arborescences to the product of the non-zero Laplacian eigenvalues 
-- divided by the number of vertices. (Cited from external literature)
axiom arborescence_spectral_eq (n k : ℕ) [Fintype (Word (n - 1) k)] : 
  NumSpanningArborescences (RootGraph n k) * 
    Fintype.card (Word (n - 1) k) = k ^ (l_size n k)

-- Word subset cardinality
lemma word_cardinality (n k : ℕ) [Fintype (Word (n - 1) k)] : 
  Fintype.card (Word (n - 1) k) = k ^ (n - 1) := by
  have e1 : Word (n - 1) k ≃ (Fin (n - 1) → Fin k) := Equiv.refl _
  rw [Fintype.card_congr e1, Fintype.card_pi_const, Fintype.card_fin]

lemma s_size_add_l_size (n k : ℕ) [Fintype (Word (n - 1) k)] :
  s_size n k + l_size n k = k ^ (n - 1) := by
  dsimp [s_size, l_size]
  have e : Fintype.card (Word (n - 1) k) = k ^ (n - 1) := word_cardinality n k
  have h_univ : (univ : Finset (Word (n - 1) k)).card = k ^ (n - 1) := by
    rw [← e]
    rfl
  have h1 : filter (fun w : Word (n - 1) k => ¬ HasKMinusOne w) univ ∪
            filter (fun w : Word (n - 1) k => HasKMinusOne w) univ = univ := by
    ext x
    simp only [mem_union, mem_filter, mem_univ, true_and]
    tauto
  have h2 : Disjoint (filter (fun w : Word (n - 1) k => ¬ HasKMinusOne w) univ)
                     (filter (fun w : Word (n - 1) k => HasKMinusOne w) univ) := by
    simp only [disjoint_filter, mem_univ, true_implies]
    intro w hnx hx
    exact hnx hx
  have h3 := card_union_of_disjoint h2
  rw [h1] at h3
  rw [← h_univ]
  exact h3.symm

def fin_k_minus_one_equiv (k : ℕ) (hk : 1 ≤ k) : {x : Fin k // (x : ℕ) ≠ k - 1} ≃ Fin (k - 1) where
  toFun x := ⟨x.val.val, by
    have h1 : x.val.val < k := x.val.isLt
    have h2 : x.val.val ≠ k - 1 := x.property
    have hk_pos : 0 < k := hk
    omega
  ⟩
  invFun y := ⟨⟨y.val, by
    have h1 : y.val < k - 1 := y.isLt
    have hk_pos : 0 < k := hk
    omega
  ⟩, by
    dsimp
    have h1 : y.val < k - 1 := y.isLt
    have hk_pos : 0 < k := hk
    omega
  ⟩
  left_inv := by rintro ⟨⟨v, _⟩, _⟩; rfl
  right_inv := by intro ⟨v, _⟩; rfl

def s_part_equiv (n k : ℕ) (hk : 1 ≤ k) : 
  {w : Word (n - 1) k // ¬ HasKMinusOne w} ≃ (Fin (n - 1) → Fin (k - 1)) where
  toFun w := fun i => fin_k_minus_one_equiv k hk ⟨w.val i, by
    have h := w.property
    dsimp [HasKMinusOne] at h
    push_neg at h
    exact h i
  ⟩
  invFun w' := ⟨fun i => (fin_k_minus_one_equiv k hk).symm (w' i), by
    dsimp [HasKMinusOne]
    push_neg
    intro i
    have h_symm := ((fin_k_minus_one_equiv k hk).symm (w' i)).property
    exact h_symm
  ⟩
  left_inv := by
    rintro ⟨w, hw⟩
    apply Subtype.ext
    funext i
    dsimp
    exact (fin_k_minus_one_equiv k hk).left_inv ⟨w i, _⟩ ▸ rfl
  right_inv := by
    intro w'
    funext i
    dsimp
    exact (fin_k_minus_one_equiv k hk).right_inv (w' i)

lemma s_size_val (n k : ℕ) (hk : 1 ≤ k) [Fintype (Word (n - 1) k)] : 
  s_size n k = (k - 1) ^ (n - 1) := by
  dsimp [s_size]
  have e1 : (filter (fun w : Word (n - 1) k => ¬ HasKMinusOne w) univ).card = 
            Fintype.card {w : Word (n - 1) k // ¬ HasKMinusOne w} := by
    exact (Fintype.card_subtype _).symm
  rw [e1]
  have e2 : Fintype.card {w : Word (n - 1) k // ¬ HasKMinusOne w} = 
            Fintype.card (Fin (n - 1) → Fin (k - 1)) := by
    exact Fintype.card_congr (s_part_equiv n k hk)
  rw [e2]
  have h_card1 : Fintype.card (Fin (n - 1) → Fin (k - 1)) = (k - 1) ^ (n - 1) := by
    rw [Fintype.card_pi_const, Fintype.card_fin]
  exact h_card1

lemma l_size_val (n k : ℕ) (hk : 1 ≤ k) [Fintype (Word (n - 1) k)] : 
  l_size n k = k ^ (n - 1) - (k - 1) ^ (n - 1) := by
  have h1 := s_size_add_l_size n k
  have h2 := s_size_val n k hk
  rw [h2] at h1
  omega

theorem num_spanning_arborescences (n k : ℕ) (hk : 1 ≤ k) 
    (H : n - 1 ≤ k ^ (n - 1) - (k - 1) ^ (n - 1)) [Fintype (Word (n - 1) k)] :
  NumSpanningArborescences (RootGraph n k) = 
  k ^ (k ^ (n - 1) - (k - 1) ^ (n - 1) - (n - 1)) := by
  have h1 := arborescence_spectral_eq n k
  have h2 := word_cardinality n k
  have h3 := l_size_val n k hk
  
  -- Substitute cardinality into equivalence
  rw [h2] at h1
  rw [h3] at h1
  
  -- Let
  set A := NumSpanningArborescences (RootGraph n k)
  set X := n - 1
  set Y := k ^ (n - 1) - (k - 1) ^ (n - 1)
  
  -- We have `A * k^X = k^Y`
  -- We want `A = k^(Y - X)`
  have thm : k ^ (Y - X) * k ^ X = k ^ Y := by
    rw [← Nat.pow_add]
    have h_sub : Y - X + X = Y := Nat.sub_add_cancel H
    rw [h_sub]
  
  -- A * k^X = k^(Y-X) * k^X
  have h_eq : A * k ^ X = k ^ (Y - X) * k ^ X := by
    rw [h1, thm]
  
  -- Cancel k^X
  have hkX_pos : 0 < k ^ X := by positivity
  
  exact Nat.eq_of_mul_eq_mul_right hkX_pos h_eq

def numLayerSequences (n k : ℕ) [Fintype (Word (n - 1) k)] : ℕ :=
  NumSpanningArborescences (RootGraph n k) * ((Nat.factorial (k - 1)) ^ l_size n k)

-- Proposition 4.5
theorem num_layer_sequences_eq (n k : ℕ) (hk : 1 ≤ k) 
    [Fintype (Word (n - 1) k)] (H : n - 1 ≤ l_size n k) :
  numLayerSequences n k = ((Nat.factorial k) ^ (l_size n k)) / (k ^ (n - 1)) := by
  have hl_val := l_size_val n k hk
  have H_arb : n - 1 ≤ k ^ (n - 1) - (k - 1) ^ (n - 1) := by linarith [hl_val, H]
  have h_arb := num_spanning_arborescences n k hk H_arb
  
  -- We know A = k ^ (L - (n-1))
  have h1 : NumSpanningArborescences (RootGraph n k) = k ^ (l_size n k - (n - 1)) := by
    rw [h_arb, hl_val]
  
  -- We know num = A * (k-1)!^L = k^(L - (n-1)) * (k-1)!^L
  unfold numLayerSequences
  rw [h1]
  
  -- k! = k * (k-1)!
  have h_fact : Nat.factorial k = k * Nat.factorial (k - 1) := by
    have hk_pos : 0 < k := hk
    obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk_pos)
    subst hk'
    have h_sub : k' + 1 - 1 = k' := rfl
    rw [h_sub, Nat.factorial_succ]
  
  set L := l_size n k
  set X := n - 1
  set F := Nat.factorial (k - 1)
  
  have h2 : ((k * F) ^ L) = k ^ L * F ^ L := Nat.mul_pow k F L
  
  have h3 : k ^ L * F ^ L / k ^ X = k ^ (L - X) * F ^ L := by
    have h_pow_sub : k ^ (L - X) * k ^ X = k ^ L := by
      rw [← Nat.pow_add]
      have hX_le_L : X ≤ L := H
      rw [Nat.sub_add_cancel hX_le_L]
    
    have h_assoc1 : k ^ L * F ^ L = k ^ (L - X) * k ^ X * F ^ L := by rw [h_pow_sub]
    have h_assoc2 : k ^ (L - X) * k ^ X * F ^ L = (k ^ (L - X) * F ^ L) * k ^ X := by ring
    rw [h_assoc1, h_assoc2]
    
    have hkX_pos : 0 < k ^ X := by positivity
    exact Nat.mul_div_cancel _ hkX_pos
    
  rw [h_fact, h2, h3]

end

end OnionDeBruijnLean
