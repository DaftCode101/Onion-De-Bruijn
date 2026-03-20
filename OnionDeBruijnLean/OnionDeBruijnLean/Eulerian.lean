import OnionDeBruijnLean.Basic
import OnionDeBruijnLean.Topology
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Card

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.openClassical false

namespace OnionDeBruijnLean
open Classical
open Finset

-- Def 3.1: The fundamental root graph G(n,k)
def RootGraph (n k : ℕ) (u v : Word (n - 1) k) : Prop :=
  DBEdge u v ∧ (HasKMinusOne u ∨ HasKMinusOne v)

noncomputable def InDegree {V : Type} [Fintype V] (G : V → V → Prop) (v : V) : ℕ :=
  (Finset.univ.filter (fun u => G u v)).card

noncomputable def OutDegree {V : Type} [Fintype V] (G : V → V → Prop) (v : V) : ℕ :=
  (Finset.univ.filter (fun u => G v u)).card

-- Definition of a graph being Eulerian
def IsEulerian {V : Type} [Fintype V] (G : V → V → Prop) : Prop :=
  ∀ v : V, InDegree G v = OutDegree G v

def prepend_char {m k : ℕ} (c : Fin k) (v : Word m k) : Word m k :=
  fun i => if h : i.val = 0 then c else v ⟨i.val - 1, by omega⟩

def append_char {m k : ℕ} (v : Word m k) (c : Fin k) : Word m k :=
  fun i => if h : i.val = m - 1 then c else v ⟨i.val + 1, by omega⟩

lemma is_in_edge {m k : ℕ} (c : Fin k) (v : Word m k) : DBEdge (prepend_char c v) v := by
  intro i
  simp [prepend_char]

lemma is_out_edge {m k : ℕ} (v : Word m k) (c : Fin k) : DBEdge v (append_char v c) := by
  intro i
  have h : (i : ℕ) ≠ m - 1 := by omega
  simp [append_char, h]

noncomputable def out_edges_equiv (n k : ℕ) (hn : 2 ≤ n) (v : Word (n - 1) k) : 
  {u : Word (n - 1) k // DBEdge v u} ≃ Fin k where
  toFun u := u.val ⟨n - 2, by omega⟩
  invFun c := ⟨append_char v c, is_out_edge v c⟩
  left_inv := by
    rintro ⟨u, hu⟩
    dsimp
    apply Subtype.ext
    funext i
    dsimp [append_char]
    split_ifs with h
    · have eq : i = ⟨n - 2, by omega⟩ := Fin.ext h
      rw [eq]
    · have j_val_lt : (i : ℕ) < n - 2 := by omega
      have hu_inst := hu ⟨i.val, j_val_lt⟩
      change v ⟨i.val + 1, by omega⟩ = u i at hu_inst
      exact hu_inst
  right_inv := by
    intro c
    have h : n - 2 = n - 1 - 1 := by omega
    simp [append_char, h]

noncomputable def in_edges_equiv (n k : ℕ) (hn : 2 ≤ n) (v : Word (n - 1) k) : 
  {u : Word (n - 1) k // DBEdge u v} ≃ Fin k where
  toFun u := u.val ⟨0, by omega⟩
  invFun c := ⟨prepend_char c v, is_in_edge c v⟩
  left_inv := by
    rintro ⟨u, hu⟩
    dsimp
    apply Subtype.ext
    funext i
    dsimp [prepend_char]
    split_ifs with h
    · have eq : i = ⟨0, by omega⟩ := Fin.ext h
      rw [eq]
    · have hi_pos : 1 ≤ (i : ℕ) := Nat.pos_of_ne_zero h
      have j_val_lt : (i : ℕ) - 1 < n - 2 := by omega
      have hu_inst := hu ⟨i.val - 1, j_val_lt⟩
      have eqi : i = ⟨(i : ℕ) - 1 + 1, by omega⟩ := Fin.ext (Nat.sub_add_cancel hi_pos).symm
      have eq_u : u i = u ⟨(i : ℕ) - 1 + 1, by omega⟩ := congrArg u eqi
      have eq_v : v ⟨(i : ℕ) - 1, by omega⟩ = v ⟨(⟨i.val - 1, j_val_lt⟩ : Fin (n - 2)).val, by omega⟩ := rfl
      rw [eq_u, eq_v]
      exact hu_inst.symm
  right_inv := by
    intro c
    simp [prepend_char]



lemma has_k_minus_one_append {n k : ℕ} (hn : 2 ≤ n) (v : Word (n - 1) k) 
    (c : Fin k) (h : ¬HasKMinusOne v) :
  HasKMinusOne (append_char v c) ↔ (c : ℕ) = k - 1 := by
  constructor
  · rintro ⟨i, hi⟩
    dsimp [append_char] at hi
    split_ifs at hi with heq
    · exact hi
    · exfalso
      apply h
      exact ⟨⟨i.val + 1, by omega⟩, hi⟩
  · intro hc
    have hn2 : n - 2 < n - 1 := by omega
    use ⟨n - 2, hn2⟩
    dsimp [append_char]
    split_ifs with heq
    · exact hc
    · exfalso; omega

lemma has_k_minus_one_prepend {n k : ℕ} (hn : 2 ≤ n) (v : Word (n - 1) k) 
    (c : Fin k) (h : ¬HasKMinusOne v) :
  HasKMinusOne (prepend_char c v) ↔ (c : ℕ) = k - 1 := by
  constructor
  · rintro ⟨i, hi⟩
    dsimp [prepend_char] at hi
    split_ifs at hi with heq
    · exact hi
    · exfalso
      apply h
      have j_val_lt : (i : ℕ) - 1 < n - 1 := by omega
      exact ⟨⟨(i : ℕ) - 1, j_val_lt⟩, hi⟩
  · intro hc
    have hz : 0 < n - 1 := by omega
    use ⟨0, hz⟩
    dsimp [prepend_char]
    exact hc

noncomputable def case2_out_equiv (n k : ℕ) (hn : 2 ≤ n) (v : Word (n - 1) k) 
    (h : ¬HasKMinusOne v) :
  {u : Word (n - 1) k // DBEdge v u ∧ HasKMinusOne u} ≃ {c : Fin k // (c : ℕ) = k - 1} where
  toFun u := ⟨out_edges_equiv n k hn v ⟨u.val, u.property.1⟩, by
    have eq_u : append_char v (out_edges_equiv n k hn v ⟨u.val, u.property.1⟩) = u.val := by
      have h_left := (out_edges_equiv n k hn v).left_inv ⟨u.val, u.property.1⟩
      exact congrArg Subtype.val h_left
    have hu_k : HasKMinusOne u.val := u.property.2
    rw [←eq_u] at hu_k
    exact (has_k_minus_one_append hn v _ h).mp hu_k
  ⟩
  invFun c := ⟨append_char v c.val, by
    have h1 := is_out_edge v c.val
    have h2 := (has_k_minus_one_append hn v c.val h).mpr c.property
    exact ⟨h1, h2⟩
  ⟩
  left_inv := by
    rintro ⟨u, hu1, hu2⟩
    apply Subtype.ext
    dsimp
    have h_left := (out_edges_equiv n k hn v).left_inv ⟨u, hu1⟩
    exact congrArg Subtype.val h_left
  right_inv := by
    rintro ⟨c, hc⟩
    apply Subtype.ext
    dsimp
    exact (out_edges_equiv n k hn v).right_inv c

noncomputable def case2_in_equiv (n k : ℕ) (hn : 2 ≤ n) (v : Word (n - 1) k) 
    (h : ¬HasKMinusOne v) :
  {u : Word (n - 1) k // DBEdge u v ∧ HasKMinusOne u} ≃ {c : Fin k // (c : ℕ) = k - 1} where
  toFun u := ⟨in_edges_equiv n k hn v ⟨u.val, u.property.1⟩, by
    have eq_u : prepend_char (in_edges_equiv n k hn v ⟨u.val, u.property.1⟩) v = u.val := by
      have h_left := (in_edges_equiv n k hn v).left_inv ⟨u.val, u.property.1⟩
      exact congrArg Subtype.val h_left
    have hu_k : HasKMinusOne u.val := u.property.2
    rw [←eq_u] at hu_k
    exact (has_k_minus_one_prepend hn v _ h).mp hu_k
  ⟩
  invFun c := ⟨prepend_char c.val v, by
    have h1 := is_in_edge c.val v
    have h2 := (has_k_minus_one_prepend hn v c.val h).mpr c.property
    exact ⟨h1, h2⟩
  ⟩
  left_inv := by
    rintro ⟨u, hu1, hu2⟩
    apply Subtype.ext
    dsimp
    have h_left := (in_edges_equiv n k hn v).left_inv ⟨u, hu1⟩
    exact congrArg Subtype.val h_left
  right_inv := by
    rintro ⟨c, hc⟩
    apply Subtype.ext
    dsimp
    exact (in_edges_equiv n k hn v).right_inv c

-- Lemma 3.2
lemma root_graph_eulerian (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) [Fintype (Word (n - 1) k)] : 
  IsEulerian (RootGraph n k) := by
  intro v
  by_cases h : HasKMinusOne v
  · -- Case 1
    have h_out : OutDegree (RootGraph n k) v = k := by
      dsimp [OutDegree]
      have eq1 : filter (fun u => RootGraph n k v u) univ = filter (fun u => DBEdge v u) univ := by
        apply filter_congr
        intro u _
        dsimp [RootGraph]
        simp [h]
      rw [eq1]
      have eq2 : (filter (fun u => DBEdge v u) univ).card = Fintype.card {u // DBEdge v u} := by
        exact (Fintype.card_subtype _).symm
      rw [eq2]
      have eq3 : Fintype.card {u // DBEdge v u} = Fintype.card (Fin k) := by
        exact Fintype.card_congr (out_edges_equiv n k hn v)
      rw [eq3]
      exact Fintype.card_fin k
    have h_in : InDegree (RootGraph n k) v = k := by
      dsimp [InDegree]
      have eq1 : filter (fun u => RootGraph n k u v) univ = filter (fun u => DBEdge u v) univ := by
        apply filter_congr
        intro u _
        dsimp [RootGraph]
        simp [h]
      rw [eq1]
      have eq2 : (filter (fun u => DBEdge u v) univ).card = Fintype.card {u // DBEdge u v} := by
        exact (Fintype.card_subtype _).symm
      rw [eq2]
      have eq3 : Fintype.card {u // DBEdge u v} = Fintype.card (Fin k) := by
        exact Fintype.card_congr (in_edges_equiv n k hn v)
      rw [eq3]
      exact Fintype.card_fin k
    rw [h_out, h_in]
  · -- Case 2
    have h_out : OutDegree (RootGraph n k) v = 1 := by
      dsimp [OutDegree]
      have eq1 : filter (fun u => RootGraph n k v u) univ = 
                 filter (fun u => DBEdge v u ∧ HasKMinusOne u) univ := by
        apply filter_congr
        intro u _
        dsimp [RootGraph]
        simp [h]
      rw [eq1]
      have eq2 : (filter (fun u => DBEdge v u ∧ HasKMinusOne u) univ).card = 
                 Fintype.card {u // DBEdge v u ∧ HasKMinusOne u} := by
        exact (Fintype.card_subtype _).symm
      rw [eq2]
      have eq3 : Fintype.card {u // DBEdge v u ∧ HasKMinusOne u} = 
                 Fintype.card {c : Fin k // (c : ℕ) = k - 1} := by
        exact Fintype.card_congr (case2_out_equiv n k hn v h)
      rw [eq3]
      have eq4 : Fintype.card {c : Fin k // (c : ℕ) = k - 1} = 1 := by
        have e : {c : Fin k // (c : ℕ) = k - 1} ≃ Unit := {
          toFun := fun _ => ()
          invFun := fun _ => ⟨⟨k - 1, by omega⟩, rfl⟩
          left_inv := by rintro ⟨c, hc⟩; apply Subtype.ext; apply Fin.ext; exact hc.symm
          right_inv := by intro x; rfl
        }
        rw [Fintype.card_congr e, Fintype.card_unit]
      exact eq4
    have h_in : InDegree (RootGraph n k) v = 1 := by
      dsimp [InDegree]
      have eq1 : filter (fun u => RootGraph n k u v) univ = 
                 filter (fun u => DBEdge u v ∧ HasKMinusOne u) univ := by
        apply filter_congr
        intro u _
        dsimp [RootGraph]
        simp [h]
      rw [eq1]
      have eq2 : (filter (fun u => DBEdge u v ∧ HasKMinusOne u) univ).card = 
                 Fintype.card {u // DBEdge u v ∧ HasKMinusOne u} := by
        exact (Fintype.card_subtype _).symm
      rw [eq2]
      have eq3 : Fintype.card {u // DBEdge u v ∧ HasKMinusOne u} = 
                 Fintype.card {c : Fin k // (c : ℕ) = k - 1} := by
        exact Fintype.card_congr (case2_in_equiv n k hn v h)
      rw [eq3]
      have eq4 : Fintype.card {c : Fin k // (c : ℕ) = k - 1} = 1 := by
        have e : {c : Fin k // (c : ℕ) = k - 1} ≃ Unit := {
          toFun := fun _ => ()
          invFun := fun _ => ⟨⟨k - 1, by omega⟩, rfl⟩
          left_inv := by rintro ⟨c, hc⟩; apply Subtype.ext; apply Fin.ext; exact hc.symm
          right_inv := by intro x; rfl
        }
        rw [Fintype.card_congr e, Fintype.card_unit]
      exact eq4
    rw [h_out, h_in]

-- Definition of Line Graph
def LineGraph {V : Type} (G : V → V → Prop) : 
  {e : V × V // G e.1 e.2} → {e : V × V // G e.1 e.2} → Prop :=
  fun e1 e2 => e1.val.2 = e2.val.1

-- L(G(n,k)) ≅ Lay(n,k)
def RelIsomorphic {V W : Type} (G : V → V → Prop) (H : W → W → Prop) : Prop :=
  ∃ f : V ≃ W, ∀ u v, G u v ↔ H (f u) (f v)

def glue {n k : ℕ} (hn : 2 ≤ n) (u v : Word (n - 1) k) (_h : DBEdge u v) : Word n k :=
  fun i => if hi : i.val < n - 1 then u ⟨i.val, hi⟩ else v ⟨i.val - 1, by omega⟩

def split_left {n k : ℕ} (hn : 2 ≤ n) (w : Word n k) : Word (n - 1) k :=
  fun i => w ⟨i.val, by omega⟩

def split_right {n k : ℕ} (hn : 2 ≤ n) (w : Word n k) : Word (n - 1) k :=
  fun i => w ⟨i.val + 1, by omega⟩

lemma split_is_edge {n k : ℕ} (hn : 2 ≤ n) (w : Word n k) : 
  DBEdge (split_left hn w) (split_right hn w) := by
  intro i
  dsimp [split_left, split_right]

lemma glue_split_left {n k : ℕ} (hn : 2 ≤ n) (u v : Word (n - 1) k) (h : DBEdge u v) :
  split_left hn (glue hn u v h) = u := by
  funext i
  dsimp [split_left, glue]
  have hi_lt : i.val < n - 1 := i.isLt
  rw [dif_pos hi_lt]

lemma glue_split_right {n k : ℕ} (hn : 2 ≤ n) (u v : Word (n - 1) k) (h : DBEdge u v) :
  split_right hn (glue hn u v h) = v := by
  funext i
  dsimp [split_right, glue]
  have hi_n := i.isLt
  by_cases h_lt : i.val + 1 < n - 1
  · rw [dif_pos h_lt]
    have h_edge : u ⟨i.val + 1, by omega⟩ = v ⟨i.val, by omega⟩ := h ⟨i.val, by omega⟩
    exact h_edge
  · rw [dif_neg h_lt]

lemma split_glue {n k : ℕ} (hn : 2 ≤ n) (w : Word n k) :
  glue hn (split_left hn w) (split_right hn w) (split_is_edge hn w) = w := by
  funext i
  dsimp [glue, split_left, split_right]
  by_cases h_lt : i.val < n - 1
  · rw [dif_pos h_lt]
  · rw [dif_neg h_lt]
    have heq : i.val - 1 + 1 = i.val := by omega
    congr 1; apply Fin.ext; exact heq

lemma has_k_minus_one_glue {n k : ℕ} (hn : 2 ≤ n) (u v : Word (n - 1) k) (h : DBEdge u v) :
  HasKMinusOne (glue hn u v h) ↔ HasKMinusOne u ∨ HasKMinusOne v := by
  constructor
  · rintro ⟨i, hi⟩
    dsimp [glue] at hi
    split_ifs at hi
    · left; exact ⟨⟨i.val, by omega⟩, hi⟩
    · right; exact ⟨⟨i.val - 1, by omega⟩, hi⟩
  · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
    · use ⟨i.val, by omega⟩
      dsimp [glue]
      have hi_lt : i.val < n - 1 := i.isLt
      rw [dif_pos hi_lt]
      exact hi
    · by_cases h_j : j.val < n - 2
      · use ⟨j.val + 1, by omega⟩
        dsimp [glue]
        have hj_lt : j.val + 1 < n - 1 := by omega
        rw [dif_pos hj_lt]
        have h_edge := h ⟨j.val, by omega⟩
        have eq_val : (u ⟨j.val + 1, hj_lt⟩).val = (v ⟨j.val, by omega⟩).val := 
          congrArg Fin.val h_edge
        rw [eq_val]
        exact hj
      · use ⟨j.val + 1, by omega⟩
        dsimp [glue]
        have hj_nlt : ¬(j.val + 1 < n - 1) := by omega
        rw [dif_neg hj_nlt]
        exact hj

lemma has_k_minus_one_split {n k : ℕ} (hn : 2 ≤ n) (w : Word n k) :
  HasKMinusOne (split_left hn w) ∨ HasKMinusOne (split_right hn w) ↔ HasKMinusOne w := by
  constructor
  · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
    · exact ⟨⟨i.val, by omega⟩, hi⟩
    · exact ⟨⟨j.val + 1, by omega⟩, hj⟩
  · rintro ⟨i, hi⟩
    by_cases h_lt : i.val < n - 1
    · left
      use ⟨i.val, h_lt⟩
      exact hi
    · right
      have hz : i.val = n - 1 := by omega
      use ⟨i.val - 1, by omega⟩
      have heq : i.val - 1 + 1 = i.val := by omega
      have h1 : (split_right hn w ⟨i.val - 1, by omega⟩).val = (w i).val := by
        dsimp [split_right]
        have h_idx : (⟨i.val - 1 + 1, by omega⟩ : Fin n) = i := by apply Fin.ext; exact heq
        rw [h_idx]
      rw [h1]
      exact hi

def layer_equiv_root_edges (n k : ℕ) (hn : 2 ≤ n) : 
  {e : Word (n - 1) k × Word (n - 1) k // RootGraph n k e.1 e.2} ≃ LayerVertex n k where
  toFun e := ⟨glue hn e.val.1 e.val.2 e.property.1, by
    have h1 := e.property.2
    exact (has_k_minus_one_glue hn e.val.1 e.val.2 e.property.1).mpr h1
  ⟩
  invFun w := ⟨(split_left hn w.val, split_right hn w.val), by
    dsimp [RootGraph]
    have h1 := split_is_edge hn w.val
    have h2 := (has_k_minus_one_split hn w.val).mpr w.property
    exact ⟨h1, h2⟩
  ⟩
  left_inv := by
    rintro ⟨⟨u, v⟩, prop⟩
    apply Subtype.ext
    apply Prod.ext
    · exact glue_split_left hn u v prop.1
    · exact glue_split_right hn u v prop.1
  right_inv := by
    rintro ⟨w, prop⟩
    apply Subtype.ext
    exact split_glue hn w

lemma db_edge_iff_split {n k : ℕ} (hn : 2 ≤ n) (w1 w2 : Word n k) :
  DBEdge w1 w2 ↔ split_right hn w1 = split_left hn w2 := by
  constructor
  · intro h
    funext i
    dsimp [split_right, split_left]
    exact h i
  · intro h i
    have h_eq := congrFun h i
    exact h_eq

-- Lemma 3.3
theorem layer_is_line_graph (n k : ℕ) (hn : 2 ≤ n) :
  RelIsomorphic (LineGraph (RootGraph n k)) (Lay n k) := by
  use layer_equiv_root_edges n k hn
  intro e1 e2
  dsimp [LineGraph, Lay, layer_equiv_root_edges]
  rw [db_edge_iff_split hn]
  rw [glue_split_right, glue_split_left]

end OnionDeBruijnLean
