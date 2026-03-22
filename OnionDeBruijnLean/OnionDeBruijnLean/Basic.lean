import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Basic

namespace OnionDeBruijnLean

--------------------------------------------------------------------------------
-- 1. Words and De Bruijn Edges
--------------------------------------------------------------------------------

-- Let k be the alphabet size. A word of length n is Fin n → Fin k.
def Word (n k : ℕ) := Fin n → Fin k

-- A word x over [k] is in the layer if it contains at least one (k-1).
def HasKMinusOne {n k : ℕ} (w : Word n k) : Prop :=
  ∃ i : Fin n, (w i).val = k - 1

def LayerVertex (n k : ℕ) := { w : Word n k // HasKMinusOne w }

-- De Bruijn edge: u_{2..n} = v_{1..n-1}
def DB {n k : ℕ} (u v : Word n k) : Prop :=
  ∀ i : Fin (n - 1), u ⟨i.val + 1, by omega⟩ = v ⟨i.val, by omega⟩

def DBGraph (n k : ℕ) : Word n k → Word n k → Prop := DB

--------------------------------------------------------------------------------
-- 2. Layer Subsets and Graphs
--------------------------------------------------------------------------------

-- The Layer Graph
def Lay (n k : ℕ) : LayerVertex n k → LayerVertex n k → Prop :=
  fun u v => DB u.val v.val

--------------------------------------------------------------------------------
-- 3. Layer and Onion Sequences
--------------------------------------------------------------------------------

def IsLayerSequence (n k : ℕ) [Fintype (LayerVertex n k)] (seq : List (LayerVertex n k)) : Prop :=
  seq.length = Fintype.card (LayerVertex n k) ∧
  seq.Nodup ∧
  List.IsChain (Lay n k) (seq ++ seq.take 1)

def IsOnionSequence (n m : ℕ) [∀ j : Fin m, Fintype (LayerVertex n (j.val + 1))] 
    (seqs : ∀ j : Fin m, List (LayerVertex n (j.val + 1))) : Prop :=
  ∀ j : Fin m, IsLayerSequence n (j.val + 1) (seqs j)

-- Total counts


end OnionDeBruijnLean
