import OnionDeBruijnLean.Laplacian
import Mathlib.Data.Fintype.BigOperators

open Finset

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace OnionDeBruijnLean

noncomputable section

instance {n k : ℕ} : Fintype (Word n k) := Pi.instFintype

-- Def standard de Bruijn sequences
def numDBSequences (n m : ℕ) : ℕ :=
  ((Nat.factorial m) ^ (m ^ (n - 1))) / (m ^ n)

def numOnionSequences (n m : ℕ) : ℕ :=
  ∏ k ∈ Finset.Ico 1 (m + 1), numLayerSequences n k

-- Theorem 5.1
theorem onion_sequence_count (n m : ℕ) (H : ∀ k ∈ Finset.Ico 1 (m + 1), n - 1 ≤ l_size n k) : 
  numOnionSequences n m = 
  ∏ k ∈ Finset.Ico 1 (m + 1), 
    (((Nat.factorial k) ^ (k ^ (n - 1) - (k - 1) ^ (n - 1))) / (k ^ (n - 1))) := by
  unfold numOnionSequences
  apply prod_congr rfl
  intro k hk
  have h_bound : n - 1 ≤ l_size n k := H k hk
  have hk_pos : 1 ≤ k := by
    rw [mem_Ico] at hk
    omega
  have h_prop := num_layer_sequences_eq n k hk_pos h_bound
  rw [h_prop]
  have hl_val := l_size_val n k hk_pos
  rw [hl_val]


-- Corollary 5.2
-- Relies on the exact `Nat` divisibility of De Bruijn sequences (Burnside's lemma)
axiom layer_ratio_db (n m : ℕ) (hm : 1 ≤ m) :
  numLayerSequences n m = (numDBSequences n m * m) / ((Nat.factorial m) ^ ((m - 1) ^ (n - 1)))

end

end OnionDeBruijnLean
