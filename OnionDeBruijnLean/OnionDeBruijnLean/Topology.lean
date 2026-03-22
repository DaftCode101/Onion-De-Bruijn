import OnionDeBruijnLean.Basic

namespace OnionDeBruijnLean

--------------------------------------------------------------------------------
-- 1. Layer Degree Imbalances (Observation 2.1)
--------------------------------------------------------------------------------

theorem lay_degree_imbalance (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) : 
  ∃ (v : LayerVertex n k), 
    (∃! e_out, Lay n k v e_out) ∧ 
    (∃ (in_edges : Fin k → LayerVertex n k), Function.Injective in_edges ∧ 
      ∀ u, Lay n k u v ↔ ∃ i, in_edges i = u) := by
  have hk_pos : 0 < k := by omega
  have hk_lt : k - 1 < k := Nat.pred_lt hk_pos.ne'
  let k_minus_one : Fin k := ⟨k - 1, hk_lt⟩
  let zero_fin : Fin k := ⟨0, hk_pos⟩
  let v_word : Word n k := fun i => if i.val = 0 then k_minus_one else zero_fin
  
  have hv_layer : HasKMinusOne v_word := by
    exact ⟨⟨0, by omega⟩, by rfl⟩
  let v : LayerVertex n k := ⟨v_word, hv_layer⟩
  use v
  constructor
  · let e_out_word : Word n k := fun i => 
      if i.val = n - 1 then k_minus_one else zero_fin
    have he_out_layer : HasKMinusOne e_out_word := by
      exact ⟨⟨n - 1, by omega⟩, by dsimp [e_out_word]; rw [if_pos rfl]⟩
    let e_out : LayerVertex n k := ⟨e_out_word, he_out_layer⟩
    use e_out
    dsimp [Lay, DB]
    constructor
    · intro i
      dsimp [v, v_word, e_out, e_out_word, Lay, DB]
      have h1 : (i.val + 1) ≠ 0 := by omega
      have h2 : i.val ≠ n - 1 := by omega
      change (if (i.val + 1) = 0 then k_minus_one else zero_fin) =
        if i.val = n - 1 then k_minus_one else zero_fin
      rw [if_neg h1, if_neg h2]
    · intro y hy
      apply Subtype.ext
      apply funext
      intro i
      dsimp [e_out, e_out_word]
      by_cases hi : i.val = n - 1
      · rw [if_pos hi]
        obtain ⟨j, hj⟩ := y.property
        by_cases hj_eq : j.val = n - 1
        · have heq : i = j := by apply Fin.ext; omega
          rw [heq]
          apply Fin.ext
          exact hj
        · have h_lt : j.val < n - 1 := by omega
          have h_edge := hy ⟨j.val, h_lt⟩
          have eq1 : (y.val j).val =
            (y.val ⟨(⟨j.val, h_lt⟩ : Fin (n-1)).val, by omega⟩).val := by rfl
          have eq2 : (y.val ⟨(⟨j.val, h_lt⟩ : Fin (n-1)).val, by omega⟩).val =
            (v.val ⟨(⟨j.val, h_lt⟩ : Fin (n-1)).val + 1, by omega⟩).val := by rw [h_edge.symm]
          have eq3 : (v.val ⟨(⟨j.val, h_lt⟩ : Fin (n-1)).val + 1, by omega⟩).val =
            zero_fin.val := rfl
          have h_contra : k - 1 = zero_fin.val := by
            rw [←hj, eq1, eq2, eq3]
          dsimp [zero_fin] at h_contra
          omega
      · rw [if_neg hi]
        have h_lt : i.val < n - 1 := by omega
        have h_edge := hy ⟨i.val, h_lt⟩
        have eq1 : y.val i =
            y.val ⟨(⟨i.val, h_lt⟩ : Fin (n-1)).val, by omega⟩ := by rfl
        have eq2 : y.val ⟨(⟨i.val, h_lt⟩ : Fin (n-1)).val, by omega⟩ =
            v.val ⟨(⟨i.val, h_lt⟩ : Fin (n-1)).val + 1, by omega⟩ := h_edge.symm
        have eq3 : v.val ⟨(⟨i.val, h_lt⟩ : Fin (n-1)).val + 1, by omega⟩ =
            zero_fin := rfl
        rw [eq1, eq2, eq3]
  · let in_edge_word (c : Fin k) : Word n k := fun i => 
      if i.val = 0 then c else if i.val = 1 then k_minus_one else zero_fin
    have hin_layer : ∀ c, HasKMinusOne (in_edge_word c) := by
      intro c
      exact ⟨⟨1, by omega⟩, rfl⟩
    let in_edges : Fin k → LayerVertex n k := fun c => ⟨in_edge_word c, hin_layer c⟩
    use in_edges
    constructor
    · intro c1 c2 hc
      have hval : (in_edges c1).val = (in_edges c2).val := congrArg Subtype.val hc
      have hn_pos : 0 < n := by omega
      have h0 : (in_edges c1).val ⟨0, hn_pos⟩ = (in_edges c2).val ⟨0, hn_pos⟩ :=
        congrFun hval ⟨0, hn_pos⟩
      have eq_c1 : (in_edges c1).val ⟨0, hn_pos⟩ = c1 := rfl
      have eq_c2 : (in_edges c2).val ⟨0, hn_pos⟩ = c2 := rfl
      rw [eq_c1, eq_c2] at h0
      exact h0
    · intro u
      constructor
      · intro hu
        have hn_pos : 0 < n := by omega
        use u.val ⟨0, hn_pos⟩
        apply Subtype.ext
        apply funext
        intro i
        dsimp [in_edges, in_edge_word, Lay, DB] at *
        by_cases h0 : i.val = 0
        · have h_eq : i = ⟨0, hn_pos⟩ := by apply Fin.ext; omega
          rw [if_pos h0, h_eq]
        · rw [if_neg h0]
          have h_sub : i.val - 1 < n - 1 := by omega
          have h_sub_n : i.val - 1 + 1 < n := by omega
          have h_edge := hu ⟨i.val - 1, h_sub⟩
          have h_idx_val : i.val = i.val - 1 + 1 := by omega
          have h_idx : i = ⟨i.val - 1 + 1, h_sub_n⟩ := Fin.ext h_idx_val
          have eq1 : u.val i = u.val ⟨i.val - 1 + 1, h_sub_n⟩ := congrArg u.val h_idx
          rw [eq1, h_edge]
          dsimp [v, v_word]
          by_cases h1 : i.val = 1
          · have h_zero : i.val - 1 = 0 := by omega
            rw [if_pos h_zero, if_pos h1]
          · have h_nz : i.val - 1 ≠ 0 := by omega
            rw [if_neg h_nz, if_neg h1]
      · intro ⟨c, hc⟩
        rw [←hc]
        intro i
        dsimp [in_edges, in_edge_word, v, v_word, Lay, DB]
        by_cases h0 : i.val = 0
        · have hs1 : i.val + 1 = 1 := by omega
          rw [if_pos h0, if_pos hs1]
        · have hs2 : i.val + 1 ≠ 1 := by omega
          rw [if_neg h0, if_neg hs2]

--------------------------------------------------------------------------------
-- 2. Heuchenne's Condition (Theorem 2.2)
--------------------------------------------------------------------------------

def SatisfiesHeuchenne {V : Type} (G : V → V → Prop) : Prop :=
  ∀ a b c d : V, G a c → G b c → G b d → G a d

lemma lay_satisfies_heuchenne (n k : ℕ) : SatisfiesHeuchenne (Lay n k) := by
  intro a b c d hac hbc hbd i
  have h1 := hac i
  have h2 := hbc i
  have h3 := hbd i
  rw [h1, ← h2, h3]

end OnionDeBruijnLean
