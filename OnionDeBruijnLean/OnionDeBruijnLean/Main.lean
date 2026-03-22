import OnionDeBruijnLean.Laplacian
import OnionDeBruijnLean.Spectrum
import Mathlib.Data.Fintype.BigOperators

open Finset

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace OnionDeBruijnLean

noncomputable section

instance {n k : ℕ} : Fintype (Word n k) := Pi.instFintype

--------------------------------------------------------------------------------
-- 1. Standard De Bruijn and Onion Sequences (Theorem 5.1)
--------------------------------------------------------------------------------

-- Def standard de Bruijn sequences
def numDBSequences (n k : ℕ) : ℕ :=
  ((Nat.factorial k) ^ (k ^ (n - 1))) / (k ^ n)

def numOnionSequences (n m : ℕ) : ℕ :=
  ∏ k ∈ Finset.Ico 2 (m + 1), numLayerSequences n k

-- Theorem 5.1
theorem onion_sequence_count (n m : ℕ) (hn : 2 ≤ n) (H : ∀ k ∈ Finset.Ico 2 (m + 1), n - 1 ≤ card_L n k) : 
  numOnionSequences n m = 
  ∏ k ∈ Finset.Ico 2 (m + 1), 
    (((Nat.factorial k) ^ (k ^ (n - 1) - (k - 1) ^ (n - 1))) / (k ^ (n - 1))) := by
  unfold numOnionSequences
  apply prod_congr rfl
  intro k hk
  have h_bound : n - 1 ≤ card_L n k := H k hk
  have hk_pos : 2 ≤ k := by
    rw [mem_Ico] at hk
    omega
  have h_prop := num_layer_sequences_eq n k hn hk_pos h_bound
  rw [h_prop]
  have hl_val := l_size_val n k hk_pos
  rw [hl_val]


--------------------------------------------------------------------------------
-- 2. Exponential Combinatorial Divisibility Bounds
--------------------------------------------------------------------------------

lemma dvd_pow_dvd {a b : ℕ} (h : a ∣ b) (n : ℕ) : a^n ∣ b^n := by
  induction n with
  | zero => exact dvd_rfl
  | succ n ih =>
    have h_pow1 : a^(n+1) = a^n * a := by rw [Nat.pow_succ]
    have h_pow2 : b^(n+1) = b^n * b := by rw [Nat.pow_succ]
    rw [h_pow1, h_pow2]
    exact mul_dvd_mul ih h

lemma n_le_m_pow_n_sub_one (n k : ℕ) (hk : 2 ≤ k) : n ≤ k ^ (n - 1) := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ x =>
    change x + 1 ≤ k ^ x
    induction x with
    | zero => exact Nat.le_refl 1
    | succ x ih =>
      calc
        (x + 1) + 1 ≤ k^x + 1 := Nat.add_le_add_right ih 1
        _ ≤ k^x + k^x := Nat.add_le_add_left (Nat.one_le_pow _ _ (by omega)) _
        _ = 2 * k^x := by omega
        _ ≤ k * k^x := Nat.mul_le_mul_right (k^x) hk
        _ = k^(x+1) := by rw [Nat.pow_succ']

lemma m_sub_one_pow_add_x_le_m_pow (x k : ℕ) (hk : 2 ≤ k) : (k - 1) ^ x + x ≤ k ^ x := by
  induction x with
  | zero => exact Nat.le_refl 1
  | succ x ih =>
    have hk1 : 1 ≤ k - 1 := by omega
    have hpow_pos : 1 ≤ (k - 1) ^ x := Nat.one_le_pow _ _ hk1
    have hkx : x ≤ k * x := by
      calc x = 1 * x := by omega
           _ ≤ k * x := Nat.mul_le_mul_right x (by omega)
    
    have H1 : (k - 1) ^ (x + 1) + x + 1 = (k - 1) * (k - 1) ^ x + x + 1 := by rw [Nat.pow_succ']
    have H2 : (k - 1) * (k - 1) ^ x + x + 1 ≤ (k - 1) * (k - 1) ^ x + (k - 1) ^ x + k * x := by omega
    have H3 : (k - 1) * (k - 1) ^ x + (k - 1) ^ x + k * x = ((k - 1) + 1) * (k - 1) ^ x + k * x := by
      calc (k - 1) * (k - 1) ^ x + (k - 1) ^ x + k * x 
        = (k - 1) * (k - 1) ^ x + 1 * (k - 1) ^ x + k * x := by rw [Nat.one_mul]
        _ = ((k - 1) + 1) * (k - 1) ^ x + k * x := by rw [← Nat.add_mul]
    have H4 : ((k - 1) + 1) * (k - 1) ^ x + k * x = k * (k - 1) ^ x + k * x := by
      have h_add : (k - 1) + 1 = k := by omega
      rw [h_add]
    have H5 : k * (k - 1) ^ x + k * x = k * ((k - 1) ^ x + x) := by rw [← Nat.mul_add]
    have H6 : k * ((k - 1) ^ x + x) ≤ k * k ^ x := Nat.mul_le_mul_left k ih
    have H7 : k * k ^ x = k ^ (x + 1) := by rw [Nat.pow_succ']
    
    calc
      (k - 1) ^ (x + 1) + (x + 1) = (k - 1) ^ (x + 1) + x + 1 := by omega
      _ = (k - 1) * (k - 1) ^ x + x + 1 := H1
      _ ≤ (k - 1) * (k - 1) ^ x + (k - 1) ^ x + k * x := H2
      _ = ((k - 1) + 1) * (k - 1) ^ x + k * x := H3
      _ = k * (k - 1) ^ x + k * x := H4
      _ = k * ((k - 1) ^ x + x) := H5
      _ ≤ k * k ^ x := H6
      _ = k ^ (x + 1) := H7

lemma n_le_m_pow_sub_m_sub_one_pow (x k : ℕ) (hk : 2 ≤ k) : x ≤ k^x - (k-1)^x := by
  have h := m_sub_one_pow_add_x_le_m_pow x k hk
  omega

lemma db_divides (n k : ℕ) (hk : 1 ≤ k) : k^n ∣ ((Nat.factorial k) ^ (k ^ (n - 1))) := by
  by_cases h : k = 1
  · subst h; simp
  · have hk2 : 2 ≤ k := by omega
    have h1 : k ∣ Nat.factorial k := Nat.dvd_factorial hk (le_refl k)
    have h2 : k^n ∣ (Nat.factorial k)^n := dvd_pow_dvd h1 n
    by_cases hn : n = 0
    · subst hn
      rw [Nat.pow_zero]
      exact one_dvd _
    · have h3 : n ≤ k ^ (n - 1) := n_le_m_pow_n_sub_one n k hk2
      have h4 : (Nat.factorial k)^n ∣ (Nat.factorial k)^(k ^ (n - 1)) := 
        Nat.pow_dvd_pow _ h3
      exact Nat.dvd_trans h2 h4

lemma layer_divides (n k : ℕ) (hk : 1 ≤ k) : k^(n-1) ∣ ((Nat.factorial k) ^ (k ^ (n - 1) - (k - 1) ^ (n - 1))) := by
  by_cases h : k = 1
  · subst h; simp
  · have hk2 : 2 ≤ k := by omega
    have h1 : k ∣ Nat.factorial k := Nat.dvd_factorial hk (le_refl k)
    have h2 : k^(n-1) ∣ (Nat.factorial k)^(n-1) := dvd_pow_dvd h1 (n-1)
    by_cases hn : n = 0
    · subst hn; simp
    · have h3 : n - 1 ≤ k ^ (n - 1) - (k - 1) ^ (n - 1) := n_le_m_pow_sub_m_sub_one_pow (n-1) k hk2
      have h4 : (Nat.factorial k)^(n-1) ∣ (Nat.factorial k)^(k ^ (n - 1) - (k - 1) ^ (n - 1)) := 
        Nat.pow_dvd_pow _ h3
      exact Nat.dvd_trans h2 h4

--------------------------------------------------------------------------------
-- 3. Component Exponential Boundary Sizes (Proposition 5.3)
--------------------------------------------------------------------------------

lemma exp_bound (n k : ℕ) (_hn : 2 ≤ n) (hk : 1 ≤ k) :
  (k - 1) ^ (n - 1) ≤ k ^ (n - 1) := by
  apply Nat.pow_le_pow_left
  omega

lemma layer_ratio_algebra_helper {F E1 E2 D k : ℕ} 
  (hD_layer : D ∣ F^(E1 - E2))
  (hD_db : k * D ∣ F^E1)
  (h_pow_add : F^E1 = F^(E1 - E2) * F^E2)
  (hk : 0 < k)
  (hD : 0 < D)
  (hF2 : 0 < F^E2) :
  F^(E1 - E2) / D = (F^E1 / (k * D) * k) / F^E2 := by
  have hkD : 0 < k * D := Nat.mul_pos hk hD
  have h1 : F^E1 / (k * D) * k = F^E1 / D := by
    rcases hD_db with ⟨K, hK⟩
    rw [hK]
    have H1 : k * D * K / (k * D) = K := Nat.mul_div_cancel_left K hkD
    rw [H1]
    have H2 : k * D * K = D * (k * K) := by ring
    rw [H2]
    rw [Nat.mul_div_cancel_left (k * K) hD]
    ring
  rw [h1]
  rcases hD_layer with ⟨J, hJ⟩
  have hJ2 : F^(E1 - E2) / D = J := by
    rw [hJ]
    exact Nat.mul_div_cancel_left J hD
  rw [hJ2]
  have h2 : F^E1 = D * (J * F^E2) := by
    calc
      F^E1 = F^(E1 - E2) * F^E2 := h_pow_add
      _ = (D * J) * F^E2 := by rw [hJ]
      _ = D * (J * F^E2) := by ring
  rw [h2]
  have h3 : D * (J * F^E2) / D = J * F^E2 := Nat.mul_div_cancel_left (J * F^E2) hD
  rw [h3]
  have h4 : J * F^E2 = F^E2 * J := by ring
  rw [h4]
  rw [Nat.mul_div_cancel_left J hF2]

-- Algebraic exponential reduction property connecting the two defined sequences
lemma layer_ratio_algebra (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
  (((Nat.factorial k) ^ (k ^ (n - 1) - (k - 1) ^ (n - 1))) / (k ^ (n - 1))) = 
  (((((Nat.factorial k) ^ (k ^ (n - 1))) / (k ^ n)) * k) / ((Nat.factorial k) ^ ((k - 1) ^ (n - 1)))) := by
  have hk_pos : 0 < k := hk
  have hD_pos : 0 < k ^ (n - 1) := by positivity
  have hF_pos : 0 < Nat.factorial k := Nat.factorial_pos k
  have hF2_pos : 0 < (Nat.factorial k) ^ ((k - 1) ^ (n - 1)) := by positivity
  
  have hD_layer := layer_divides n k hk
  have hD_db := db_divides n k hk
  have h_pow_add : (Nat.factorial k) ^ (k ^ (n - 1)) = 
    (Nat.factorial k) ^ (k ^ (n - 1) - (k - 1) ^ (n - 1)) * (Nat.factorial k) ^ ((k - 1) ^ (n - 1)) := by
    rw [← Nat.pow_add]
    congr 1
    have h_sub := exp_bound n k hn hk
    omega
  
  have h_md : k * k ^ (n - 1) = k ^ n := by
    cases n with
    | zero => exact False.elim (by omega)
    | succ x =>
      have h_x : x + 1 - 1 = x := rfl
      rw [h_x]
      rw [Nat.pow_succ']
  
  have hD_db' : k * k ^ (n - 1) ∣ (Nat.factorial k) ^ (k ^ (n - 1)) := by
    rw [h_md]
    exact hD_db
  have H := layer_ratio_algebra_helper hD_layer hD_db' h_pow_add hk_pos hD_pos hF2_pos
  rw [h_md] at H
  exact H

--------------------------------------------------------------------------------
-- 4. Burnside Lemma Reduction (Corollary 5.2)
--------------------------------------------------------------------------------

-- Relies on the exact `Nat` divisibility of De Bruijn sequences (Burnside's lemma)
theorem layer_ratio_db (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) [Fintype (Word (n - 1) k)] (H : n - 1 ≤ card_L n k) :
  numLayerSequences n k = (numDBSequences n k * k) / ((Nat.factorial k) ^ ((k - 1) ^ (n - 1))) := by
  have hk1 : 1 ≤ k := by omega
  rw [num_layer_sequences_eq n k hn hk H]
  rw [l_size_val n k hk]
  unfold numDBSequences
  exact layer_ratio_algebra n k hn hk1

end

end OnionDeBruijnLean
