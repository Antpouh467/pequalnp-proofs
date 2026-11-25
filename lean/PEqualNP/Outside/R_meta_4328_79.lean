import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Reduction of L-meta-4328 to two open hypotheses.
-- normalN1: a circuit of size at most 124 as in the gap can be replaced by one of no larger
--   size that accepts every edge pair, rejects every singleton, and in which every AND gate
--   is 1 only on inputs that contain an edge.
-- orBound: such a circuit has at least 104 OR gates, that is the edge count minus one.
-- Checked in this file: such a circuit has at least 21 AND gates, the vertex cover number
--   of the PG(2,4) incidence graph; with orBound the size is at least 125.
-- Evidence from exhaustive optimal and optimal plus one circuits for C6, K13, P4, P5, P6,
--   S22 and a spider graph: the orBound analogue had 0 failures in 11 corpora, minimum
--   slack 0, so the bound is tight; every corpus graph has an optimal circuit of this form.
-- Known false on these corpora: a single gate deletion or replacement always normalises;
--   the number of tops of AND chains is at least the cover number; the pairwise core of the
--   block lemma for three or more leaves; the block lemma with one common label per side;
--   greedy charging schemes for the OR count.
set_option maxRecDepth 32768 in
set_option maxHeartbeats 40000000 in
theorem PEqualNP.Outside.R_meta_4328_79
    (normalN1 : ∀ (C : Circuit), Monotone2 C → C.size ≤ (124 : ℕ) →
            (∀ (u v : Fin (42 : ℕ)), (↑u < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑v ∧ (↑v + (21 : ℕ) - ↑u) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) → C.eval (List.ofFn fun (w : Fin (42 : ℕ)) => Decidable.decide (w = u ∨ w = v)) = Bool.true) →
      (∀ (x : Fin (42 : ℕ) → Bool), (∀ (u : Fin (42 : ℕ)), x u = Bool.true ↔ ∀ (v : Fin (42 : ℕ)), x v = Bool.true → ¬((↑u < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑v ∧ (↑v + (21 : ℕ) - ↑u) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∨ (↑v < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑u ∧ (↑u + (21 : ℕ) - ↑v) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]))) → C.eval (List.ofFn x) = Bool.false) →
      ∃ (D : Circuit), Monotone2 D ∧ D.size ≤ C.size ∧ (∀ (u v : Fin (42 : ℕ)), (↑u < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑v ∧ (↑v + (21 : ℕ) - ↑u) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) → D.eval (List.ofFn fun (w : Fin (42 : ℕ)) => Decidable.decide (w = u ∨ w = v)) = Bool.true) ∧
        (∀ (u : Fin (42 : ℕ)), D.eval (List.ofFn fun (w : Fin (42 : ℕ)) => Decidable.decide (w = u)) = Bool.false) ∧
        (∀ (j : ℕ) (g : Gate), D.gates[j]? = some g → g.op = GateOp.and → ∀ (x : Fin (42 : ℕ) → Bool), (D.wires (List.ofFn x)).getD ((42 : ℕ) + j) Bool.false = Bool.true → ∃ (u v : Fin (42 : ℕ)), (↑u < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑v ∧ (↑v + (21 : ℕ) - ↑u) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x u = Bool.true ∧ x v = Bool.true))
    (orBound : ∀ (D : Circuit), Monotone2 D →
      (∀ (u v : Fin (42 : ℕ)), (↑u < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑v ∧ (↑v + (21 : ℕ) - ↑u) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) → D.eval (List.ofFn fun (w : Fin (42 : ℕ)) => Decidable.decide (w = u ∨ w = v)) = Bool.true) →
      (∀ (u : Fin (42 : ℕ)), D.eval (List.ofFn fun (w : Fin (42 : ℕ)) => Decidable.decide (w = u)) = Bool.false) →
      (∀ (j : ℕ) (g : Gate), D.gates[j]? = some g → g.op = GateOp.and → ∀ (x : Fin (42 : ℕ) → Bool), (D.wires (List.ofFn x)).getD ((42 : ℕ) + j) Bool.false = Bool.true → ∃ (u v : Fin (42 : ℕ)), (↑u < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑v ∧ (↑v + (21 : ℕ) - ↑u) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x u = Bool.true ∧ x v = Bool.true) →
      ∃ (G : Finset ℕ), (104 : ℕ) ≤ G.card ∧ ∀ j ∈ G, ∃ (g : Gate), D.gates[j]? = some g ∧ g.op = GateOp.or) :
    have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : (Fin (42 : ℕ) → Bool) → Prop := fun (x2 : Fin (42 : ℕ) → Bool) => ∀ (x3 : Fin (42 : ℕ)), x2 x3 = Bool.true ↔ ∀ (x4 : Fin (42 : ℕ)), x2 x4 = Bool.true → ¬(x1 x3 x4 ∨ x1 x4 x3); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x3.size ≤ (124 : ℕ) → (∃ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x3.wires (List.ofFn fun (x8 : Fin (42 : ℕ)) => Decidable.decide (↑x8 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x6) Bool.false = Bool.true) → (∀ (x7 x8 : Fin (42 : ℕ)), x1 x7 x8 → x3.eval (List.ofFn fun (x10 : Fin (42 : ℕ)) => Decidable.decide (x10 = x7 ∨ x10 = x8)) = Bool.true) → (∀ (x8 : Fin (42 : ℕ) → Bool), x2 x8 → x3.eval (List.ofFn x8) = Bool.false) → False := by
  have hEvAnd : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have hEvOr : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have AF_fold_len : ∀ (gs : List Gate), ∀ w : List Bool, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length = w.length + gs.length := by
    clear normalN1 orBound
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih => intro w; simp only [List.foldl_cons]; rw [ih]; simp; omega
  have AF_fold_head : ∀ (gs : List Gate), ∀ (w : List Bool) (i : ℕ), i < w.length → (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false = w.getD i false := by
    clear normalN1 orBound AF_fold_len
    intro gs
    induction gs with
    | nil => intro w i _; simp
    | cons g gs ih =>
      intro w i hi
      simp only [List.foldl_cons]
      rw [ih _ i (by simp; omega)]
      rw [List.getD_append _ _ _ _ hi]
  have AF_fold_or : ∀ (gs : List Gate), ∀ (wx wy wz : List Bool), wx.length = wy.length → wz.length = wx.length → (∀ i, wz.getD i false = (wx.getD i false || wy.getD i false)) → (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → (∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wz).getD (wz.length + j) false = false) → ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wz).getD i false = ((gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wx).getD i false || (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wy).getD i false) := by
    clear normalN1 orBound AF_fold_len
    intro gs
    induction gs with
    | nil => intro wx wy wz _ _ hz _ _ i; simpa using hz i
    | cons g gs ih =>
      intro wx wy wz hxy hzx hz hops hand
      simp only [List.foldl_cons]
      have hg := hops g (List.mem_cons_self ..)
      have hnew : g.op.eval (g.inputs.map fun i => wz.getD i false)
          = (g.op.eval (g.inputs.map fun i => wx.getD i false)
            || g.op.eval (g.inputs.map fun i => wy.getD i false)) := by
        rcases hg with hg | hg
        · have h0 := hand 0 g rfl hg
          simp only [List.foldl_cons, Nat.add_zero] at h0
          rw [AF_fold_head gs _ _ (by simp)] at h0
          rw [List.getD_append_right _ _ _ _ (le_refl _)] at h0
          simp only [Nat.sub_self, List.getD_cons_zero] at h0
          rw [h0]
          rw [hg] at h0 ⊢
          simp only [hEvAnd, hEvOr, List.all_eq_false, List.mem_map] at h0 ⊢
          obtain ⟨b, ⟨i, hi, rfl⟩, hb⟩ := h0
          simp only [id, hz i] at hb
          have hb' : wx.getD i false = false ∧ wy.getD i false = false := by
            cases h1 : wx.getD i false <;> cases h2 : wy.getD i false <;> simp_all
          have hx : (List.all (g.inputs.map fun i => wx.getD i false) id) = false := by
            rw [List.all_eq_false]; exact ⟨_, List.mem_map.2 ⟨i, hi, rfl⟩, by simpa [id] using hb'.1⟩
          have hy : (List.all (g.inputs.map fun i => wy.getD i false) id) = false := by
            rw [List.all_eq_false]; exact ⟨_, List.mem_map.2 ⟨i, hi, rfl⟩, by simpa [id] using hb'.2⟩
          rw [hx, hy]; rfl
        · rw [hg]
          simp only [hEvAnd, hEvOr, List.any_map]
          clear hand ih hops
          generalize g.inputs = l
          induction l with
          | nil => rfl
          | cons a l ihl =>
            simp only [List.any_cons, Function.comp, id, hz a, ihl]
            cases wx.getD a false <;> cases wy.getD a false <;> simp
      apply ih
      · simp [hxy]
      · simp [hzx]
      · intro i
        by_cases hi : i < wz.length
        · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by omega),
            List.getD_append _ _ _ _ (by omega)]
          exact hz i
        · rcases Nat.lt_or_ge i (wz.length + 1) with h1 | h1
          · have : i = wz.length := by omega
            subst this
            rw [List.getD_append_right _ _ _ _ (le_refl _), List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega)]
            simp only [Nat.sub_self, hzx, hxy, List.getD_cons_zero]
            rw [← hxy] at *
            simpa [hzx] using hnew
          · simp only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega),
              List.getElem?_eq_none (by simp; omega)]
            rfl
      · intro g' hg'; exact hops g' (List.mem_cons_of_mem _ hg')
      · intro j g' hj hop
        have := hand (j + 1) g' (by simpa using hj) hop
        simp only [List.foldl_cons] at this
        rw [show wz.length + (j + 1) = (wz ++ [g.op.eval (g.inputs.map fun i => wz.getD i false)]).length + j by
          simp; omega] at this
        exact this
  have AF_A1 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x y : List Bool), (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → x.length = y.length → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → (C.wires (List.zipWith (fun a b => a || b) x y)).getD (x.length + j) false = false) → ∀ i : ℕ, (C.wires (List.zipWith (fun a b => a || b) x y)).getD i false = ((C.wires x).getD i false || (C.wires y).getD i false) := by
    clear normalN1 orBound AF_fold_len AF_fold_head
    intro C x y hops hlen hand i
    have hz : ∀ i, (List.zipWith (fun a b => a || b) x y).getD i false = (x.getD i false || y.getD i false) := by
      intro i
      by_cases hi : i < x.length
      · have hi2 : i < y.length := by omega
        have hi3 : i < (List.zipWith (fun a b => a || b) x y).length := by simp [hlen]; omega
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi2, List.getElem?_eq_getElem hi3,
          List.getElem_zipWith]
        rfl
      · have hi2 : ¬ i < y.length := by omega
        have hi3 : ¬ i < (List.zipWith (fun a b => a || b) x y).length := by simp [hlen]; omega
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
        rfl
    have hzl : (List.zipWith (fun a b => a || b) x y).length = x.length := by simp [hlen]
    exact AF_fold_or C.gates x y _ hlen hzl hz hops (by
      intro j g hj hop; rw [hzl]; exact hand j g hj hop) i
  have AF_fold_mono : ∀ (gs : List Gate), ∀ (wx wy : List Bool), wx.length = wy.length → (∀ i, wx.getD i false = true → wy.getD i false = true) → (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wx).getD i false = true → (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wy).getD i false = true := by
    clear normalN1 orBound AF_fold_len AF_fold_head AF_fold_or AF_A1
    intro gs
    induction gs with
    | nil => intro wx wy _ h _ i; simpa using h i
    | cons g gs ih =>
      intro wx wy hxy hle hops
      simp only [List.foldl_cons]
      have hnew : g.op.eval (g.inputs.map fun i => wx.getD i false) = true →
          g.op.eval (g.inputs.map fun i => wy.getD i false) = true := by
        rcases hops g (List.mem_cons_self ..) with hg | hg
        · rw [hg]
          simp only [hEvAnd, hEvOr, List.all_map, List.all_eq_true, Function.comp, id]
          intro h i hi; exact hle i (h i hi)
        · rw [hg]
          simp only [hEvAnd, hEvOr, List.any_map, List.any_eq_true, Function.comp, id]
          rintro ⟨i, hi, h⟩; exact ⟨i, hi, hle i h⟩
      apply ih
      · simp [hxy]
      · intro i hi
        by_cases h1 : i < wx.length
        · rw [List.getD_append _ _ _ _ h1] at hi
          rw [List.getD_append _ _ _ _ (by omega)]
          exact hle i hi
        · rcases Nat.lt_or_ge i (wx.length + 1) with h2 | h2
          · have : i = wx.length := by omega
            subst this
            rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
            rw [List.getD_append_right _ _ _ _ (by omega)]
            simp only [Nat.sub_self, List.getD_cons_zero] at hi
            rw [hxy, Nat.sub_self, List.getD_cons_zero]
            exact hnew hi
          · simp only [List.getD_eq_getElem?_getD] at hi
            rw [List.getElem?_eq_none (by simp; omega)] at hi
            simp at hi
      · intro g' hg'; exact hops g' (List.mem_cons_of_mem _ hg')
  have AF_A0 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x y : List Bool), (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → x.length = y.length → (∀ i : ℕ, x.getD i false = true → y.getD i false = true) → ∀ i : ℕ, (C.wires x).getD i false = true → (C.wires y).getD i false = true := by
    clear normalN1 orBound AF_fold_len AF_fold_head AF_fold_or AF_A1
    intro C x y hops hlen hle i hi
    exact AF_fold_mono C.gates x y hlen hle hops i hi
  have AF_A4 : let E := fun (u v : Fin 42) => u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ); ∀ u u2 w w2 : Fin 42, E u w → E u w2 → E u2 w → E u2 w2 → u = u2 ∨ w = w2 := by
    clear normalN1 orBound AF_fold_len AF_fold_head AF_fold_or AF_A1 AF_fold_mono AF_A0
    dsimp only
    intro u u2 w w2 h1 h2 h3 h4
    obtain ⟨hu, hw, h1⟩ := h1
    obtain ⟨-, hw2, h2⟩ := h2
    obtain ⟨hu2, -, h3⟩ := h3
    obtain ⟨-, -, h4⟩ := h4
    have bw : w.val < 42 := w.isLt
    have bw2 : w2.val < 42 := w2.isLt
    rw [Fin.ext_iff, Fin.ext_iff]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h1 h2 h3 h4
    rcases h1 with h1 | h1 | h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 | h2 | h2 <;>
      rcases h3 with h3 | h3 | h3 | h3 | h3 <;> rcases h4 with h4 | h4 | h4 | h4 | h4 <;> omega
  have AF_B1b : let E := fun (u v : Fin 42) => u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ); ∀ (c c2 : Fin 42) (L : Finset (Fin 42)), c ≠ c2 → 2 ≤ L.card → (∀ v ∈ L, E c v ∨ E v c) → (∀ v ∈ L, E c2 v ∨ E v c2) → False := by
    clear normalN1 orBound AF_fold_len AF_fold_head AF_fold_or AF_A1 AF_fold_mono AF_A0
    intro E c c2 L hne hcard h1 h2
    obtain ⟨v, hv, v2, hv2, hvv⟩ := Finset.one_lt_card.1 (by omega : 1 < L.card)
    have H := AF_A4
    have a1 := h1 v hv
    have a2 := h1 v2 hv2
    have b1 := h2 v hv
    have b2 := h2 v2 hv2
    simp only [E] at a1 a2 b1 b2 H
    rcases a1 with a1 | a1 <;> rcases a2 with a2 | a2 <;> rcases b1 with b1 | b1 <;> rcases b2 with b2 | b2
    · rcases H c c2 v v2 a1 a2 b1 b2 with h | h
      · exact absurd h hne
      · exact absurd h hvv
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rcases H v v2 c c2 a1 b1 a2 b2 with h | h
      · exact absurd h hvv
      · exact absurd h hne
  have AF_A5 : let E := fun (u v : Fin 42) => u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ); ∀ S : Finset (Fin 42), (∀ u v : Fin 42, E u v → u ∈ S ∨ v ∈ S) → 21 ≤ S.card := by
    clear normalN1 orBound AF_fold_len AF_fold_head AF_fold_or AF_A1 AF_fold_mono AF_A0 AF_A4 AF_B1b
    dsimp only
    intro S hS
    have h_main : 21 ≤ S.card := by
      classical
      have h₁ : ∀ (i : Fin 21), (⟨i.val, by omega⟩ : Fin 42) ∈ S ∨ (⟨i.val + 21, by omega⟩ : Fin 42) ∈ S := by
        intro i
        have h₂ : (⟨i.val, by omega⟩ : Fin 42).val < 21 ∧ 21 ≤ (⟨i.val + 21, by omega⟩ : Fin 42).val ∧ ((⟨i.val + 21, by omega⟩ : Fin 42).val + 21 - (⟨i.val, by omega⟩ : Fin 42).val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) := by
          constructor
          ·
            simp [Fin.val_mk]
            <;> omega
          constructor
          ·
            simp [Fin.val_mk]
            <;> omega
          ·
            simp [Fin.val_mk, List.mem_cons, List.mem_nil_iff]
            <;> norm_num <;> omega
        have h₃ : (⟨i.val, by omega⟩ : Fin 42) ∈ S ∨ (⟨i.val + 21, by omega⟩ : Fin 42) ∈ S := hS (⟨i.val, by omega⟩ : Fin 42) (⟨i.val + 21, by omega⟩ : Fin 42) h₂
        exact h₃

      let f : Fin 21 → Fin 42 := fun i => if (⟨i.val, by omega⟩ : Fin 42) ∈ S then (⟨i.val, by omega⟩ : Fin 42) else (⟨i.val + 21, by omega⟩ : Fin 42)

      have h₂ : ∀ (i : Fin 21), f i ∈ S := by
        intro i
        by_cases h : (⟨i.val, by omega⟩ : Fin 42) ∈ S
        ·
          simp [f, h]
        ·
          have h₃ : (⟨i.val, by omega⟩ : Fin 42) ∈ S ∨ (⟨i.val + 21, by omega⟩ : Fin 42) ∈ S := h₁ i
          cases h₃ with
          | inl h₃ =>
            exfalso
            exact h h₃
          | inr h₃ =>
            simp [f, h]
            exact h₃

      have h₃ : Function.Injective f := by
        intro i j h₄
        dsimp [f] at h₄
        have h₅ : i.val < 21 := i.is_lt
        have h₆ : j.val < 21 := j.is_lt
        split_ifs at h₄ <;> simp [Fin.ext_iff, Fin.val_mk] at h₄ ⊢ <;>
        (try omega) <;>
        (try {
          apply Fin.ext
          <;> omega
        })

      have h₄ : 21 ≤ S.card := by
        have h₅ : (Finset.image f (Finset.univ : Finset (Fin 21))).card = 21 := by
          rw [Finset.card_image_of_injective _ h₃]
          <;> simp [Finset.card_univ, Fintype.card_fin]
        have h₆ : (Finset.image f (Finset.univ : Finset (Fin 21))) ⊆ S := by
          intro x hx
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
          obtain ⟨i, _, rfl⟩ := hx
          exact h₂ i
        have h₇ : (Finset.image f (Finset.univ : Finset (Fin 21))).card ≤ S.card := Finset.card_mono h₆
        omega

      exact h₄

    exact h_main
  have AF_A6 : let E := fun (u v : Fin 42) => u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ); ∀ (G : Finset ℕ) (c : ℕ → Fin 42), (∀ u v : Fin 42, E u v → ∃ g ∈ G, c g = u ∨ c g = v) → 21 ≤ G.card := by
    clear normalN1 orBound AF_fold_len AF_fold_head AF_fold_or AF_A1 AF_fold_mono AF_A0 AF_A4 AF_B1b
    intro E G c h
    have hcov : ∀ u v : Fin 42, E u v → u ∈ G.image c ∨ v ∈ G.image c := by
      intro u v huv
      obtain ⟨g, hg, hc⟩ := h u v huv
      rcases hc with hc | hc
      · exact Or.inl (Finset.mem_image.2 ⟨g, hg, hc⟩)
      · exact Or.inr (Finset.mem_image.2 ⟨g, hg, hc⟩)
    exact le_trans (AF_A5 (G.image c) hcov) Finset.card_image_le
  have AF_take_head : ∀ (C : Circuit) (x : List Bool) (j i : ℕ) (hj : j ≤ C.gates.length) (hi : i < x.length + j), (C.wires x).getD i false = ((C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false := by
    clear normalN1 orBound AF_fold_or AF_A1 AF_fold_mono AF_A0 AF_A4 AF_B1b AF_A5 AF_A6
    intro C x j i hj hi
    unfold Circuit.wires
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.foldl_append]
    apply AF_fold_head
    rw [AF_fold_len, List.length_take]; omega
  have AF_gate_val : ∀ (C : Circuit) (x : List Bool) (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g), (C.wires x).getD (x.length + j) false = g.op.eval (g.inputs.map fun i => ((C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false) := by
    clear normalN1 orBound AF_fold_or AF_A1 AF_fold_mono AF_A0 AF_A4 AF_B1b AF_A5 AF_A6 AF_take_head
    intro C x j g hg
    rw [List.getElem?_eq_some_iff] at hg
    obtain ⟨hj, hgj⟩ := hg
    have hsplit : C.gates = C.gates.take j ++ g :: C.gates.drop (j+1) := by
      conv_lhs => rw [← List.take_append_drop j C.gates]
      rw [List.drop_eq_getElem_cons hj, hgj]
    have hlen : ((C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length = x.length + j := by
      rw [AF_fold_len, List.length_take]; omega
    have hw : C.wires x = (C.gates.drop (j+1)).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (((C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x) ++
          [g.op.eval (g.inputs.map fun i =>
            ((C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false)]) := by
      unfold Circuit.wires
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    rw [hw, AF_fold_head _ _ _ (by rw [List.length_append, hlen]; simp)]
    rw [List.getD_append_right _ _ _ _ (by rw [hlen]), hlen, Nat.sub_self, List.getD_cons_zero]
  have AF_getD_ofFn : ∀ (f : Fin 42 → Bool) (i : ℕ), (List.ofFn f).getD i false = if h : i < 42 then f ⟨i, h⟩ else false := by
    clear normalN1 orBound AF_fold_len AF_fold_head AF_fold_or AF_A1 AF_fold_mono AF_A0 AF_A4 AF_B1b AF_A5 AF_A6 AF_take_head AF_gate_val
    intro f i
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    split <;> simp_all
  have hAfull : let E := fun (u v : Fin 42) => u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ); ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → (∀ u v : Fin 42, E u v → C.eval (List.ofFn fun w : Fin 42 => decide (w = u ∨ w = v)) = true) → (∀ u : Fin 42, C.eval (List.ofFn fun w : Fin 42 => decide (w = u)) = false) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x : Fin 42 → Bool, (C.wires (List.ofFn x)).getD (42 + j) false = true → ∃ u v : Fin 42, E u v ∧ x u = true ∧ x v = true) → ∃ G : Finset ℕ, 21 ≤ G.card ∧ ∀ j ∈ G, ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and := by
    clear normalN1 orBound AF_fold_len AF_fold_head AF_fold_or AF_fold_mono AF_A4 AF_A5
    intro E C hmono hacc hrej hN1
    classical
    have hops : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      intro g hg
      have := (hmono g hg).1
      simpa using this
    have hEne : ∀ a b : Fin 42, E a b → a ≠ b := by
      intro a b h hab; subst hab; obtain ⟨h1, h2, -⟩ := h; omega
    have hzip : ∀ u v : Fin 42, (List.ofFn fun w : Fin 42 => decide (w = u ∨ w = v)) =
        List.zipWith (fun a b => a || b) (List.ofFn fun w : Fin 42 => decide (w = u)) (List.ofFn fun w : Fin 42 => decide (w = v)) := by
      intro u v
      apply List.ext_getElem
      · simp
      · intro n h1 h2
        simp [List.getElem_zipWith, Bool.decide_or]
    have hsing : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u : Fin 42,
        (C.wires (List.ofFn fun w : Fin 42 => decide (w = u))).getD (42 + j) false = false := by
      intro j g hg hop u
      by_contra hne
      obtain ⟨a, b, hab, ha, hb⟩ := hN1 j g hg hop _ (by simpa only [Bool.not_eq_false] using hne)
      simp only [decide_eq_true_eq] at ha hb
      exact hEne a b hab (ha.trans hb.symm)
    have hex : ∀ u v : Fin 42, E u v → ∃ j, ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧
        g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (C.wires (List.ofFn fun w : Fin 42 => decide (w = u ∨ w = v))).getD (42 + j) false = true := by
      intro u v huv
      by_contra hne
      push Not at hne
      have key := AF_A1 C (List.ofFn fun w : Fin 42 => decide (w = u)) (List.ofFn fun w : Fin 42 => decide (w = v))
        hops (by simp) (by
          intro j g hj hop
          have := hne j g hj hop
          rw [← hzip u v, List.length_ofFn]; simpa only [ne_eq, Bool.not_eq_true] using this) C.output
      have h1 := hacc u v huv
      have h2 := hrej u
      have h3 := hrej v
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval at h1 h2 h3
      rw [hzip u v, key, h2, h3] at h1
      simp at h1
    let fj : Fin 42 → Fin 42 → ℕ := fun u v => if h : E u v then Nat.find (hex u v h) else 0
    let W : ℕ → List Bool → List Bool := fun j x =>
      (C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
    let Ls : ℕ → ℕ → Finset (Fin 42) := fun j i =>
      Finset.univ.filter (fun w : Fin 42 => (W j (List.ofFn fun z : Fin 42 => decide (z = w))).getD i false = true)
    let cen : ℕ → Fin 42 := fun j =>
      (C.gates[j]?).elim 0 (fun g => if (Ls j (g.inputs.getD 0 0)).card = 1 then (Ls j (g.inputs.getD 0 0)).toList.headD 0
          else (Ls j (g.inputs.getD 1 0)).toList.headD 0)
    let G : Finset ℕ := ((Finset.univ : Finset (Fin 42 × Fin 42)).filter (fun p => E p.1 p.2)).image (fun p => fj p.1 p.2)
    have hhead : ∀ (S : Finset (Fin 42)) (s : Fin 42), S.card = 1 → s ∈ S → S.toList.headD 0 = s := by
      intro S s hS hs
      obtain ⟨t, rfl⟩ := Finset.card_eq_one.1 hS
      rw [Finset.mem_singleton] at hs; subst hs
      simp
    have hcov : ∀ u v : Fin 42, E u v → cen (fj u v) = u ∨ cen (fj u v) = v := by
      intro u v huv
      have hfj : fj u v = Nat.find (hex u v huv) := by simp only [fj, dif_pos huv]
      rw [hfj]
      obtain ⟨g0, hg0, hop0, hfire⟩ := Nat.find_spec (hex u v huv)
      have hmin := fun j (hj : j < Nat.find (hex u v huv)) => Nat.find_min (hex u v huv) hj
      set j0 := Nat.find (hex u v huv) with hj0
      have hj0len : j0 < C.gates.length := by
        rcases Nat.lt_or_ge j0 C.gates.length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at hg0; cases hg0
      have hval : ∀ x : List Bool, x.length = 42 → (C.wires x).getD (42 + j0) false =
          g0.op.eval (g0.inputs.map fun i => (W j0 x).getD i false) := by
        intro x hx
        have := AF_gate_val C x j0 g0 hg0
        rw [hx] at this; exact this
      have hlin : ∀ i, (W j0 (List.ofFn fun w : Fin 42 => decide (w = u ∨ w = v))).getD i false =
          ((W j0 (List.ofFn fun w : Fin 42 => decide (w = u))).getD i false ||
            (W j0 (List.ofFn fun w : Fin 42 => decide (w = v))).getD i false) := by
        intro i
        have := AF_A1 ⟨C.gates.take j0, 0⟩ (List.ofFn fun w : Fin 42 => decide (w = u))
          (List.ofFn fun w : Fin 42 => decide (w = v))
          (by intro g hg; exact hops g (List.mem_of_mem_take hg)) (by simp) (by
            intro j g hj hop
            have hjlt : j < j0 := by
              have := (List.getElem?_eq_some_iff.1 hj).1
              simp at this; omega
            have hgj : C.gates[j]? = some g := by
              rw [List.getElem?_take] at hj; simpa [hjlt] using hj
            have hnot := hmin j hjlt
            push Not at hnot
            have h2 := hnot g hgj hop
            have h3 := AF_take_head C (List.ofFn fun w : Fin 42 => decide (w = u ∨ w = v)) j0 (42 + j) hj0len.le
              (by rw [List.length_ofFn]; omega)
            have h4 : ((C.gates.take j0).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
                (List.ofFn fun w : Fin 42 => decide (w = u ∨ w = v))).getD (42 + j) false = false := by
              rw [← h3]; simpa only [ne_eq, Bool.not_eq_true] using h2
            rw [← hzip u v, List.length_ofFn]
            exact h4) i
        rw [← hzip u v] at this
        exact this
      have hlen1 : ∀ x : Fin 42 → Bool, (List.ofFn x).length = 42 := by intro x; simp
      have vz := hval (List.ofFn fun w : Fin 42 => decide (w = u ∨ w = v)) (hlen1 _)
      rw [hfire, hop0] at vz
      have vu := hval _ (hlen1 (fun w : Fin 42 => decide (w = u)))
      rw [hsing j0 g0 hg0 hop0 u, hop0] at vu
      have vv := hval _ (hlen1 (fun w : Fin 42 => decide (w = v)))
      rw [hsing j0 g0 hg0 hop0 v, hop0] at vv
      have hlen2 : g0.inputs.length ≤ 2 := (hmono g0 (List.mem_of_getElem? hg0)).2
      have hadj : ∀ a b : ℕ, g0.inputs = [a, b] → ∀ p ∈ Ls j0 a, ∀ q ∈ Ls j0 b, E p q ∨ E q p := by
        intro a b hin p hp q hq
        simp only [Ls, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
        have mono : ∀ (r : Fin 42) (i : ℕ), (W j0 (List.ofFn fun z : Fin 42 => decide (z = r))).getD i false = true →
            r = p ∨ r = q →
            (W j0 (List.ofFn fun z : Fin 42 => decide (z = p ∨ z = q))).getD i false = true := by
          intro r i hr hrpq
          exact AF_A0 ⟨C.gates.take j0, 0⟩ _ _ (by intro g hg; exact hops g (List.mem_of_mem_take hg)) (by simp)
            (by
              intro k hk
              rw [AF_getD_ofFn] at hk ⊢
              split at hk
              · rename_i hk42
                rw [dif_pos hk42]
                simp only [decide_eq_true_eq] at hk ⊢
                rcases hrpq with h | h <;> subst h
                · exact Or.inl hk
                · exact Or.inr hk
              · simp at hk) i hr
        have hf : (C.wires (List.ofFn fun z : Fin 42 => decide (z = p ∨ z = q))).getD (42 + j0) false = true := by
          rw [hval _ (hlen1 _), hop0, hin]
          simp only [hEvAnd, hEvOr, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
            Bool.and_true, Bool.and_eq_true]
          exact ⟨mono p a hp (Or.inl rfl), mono q b hq (Or.inr rfl)⟩
        obtain ⟨a', b', hab, ha, hb⟩ := hN1 j0 g0 hg0 hop0 _ hf
        simp only [decide_eq_true_eq] at ha hb
        have hne := hEne a' b' hab
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact absurd rfl hne
        · exact Or.inl hab
        · exact Or.inr hab
        · exact absurd rfl hne
      have hfin : ∀ a b : ℕ, g0.inputs = [a, b] → ∀ p q : Fin 42, p ∈ Ls j0 a → q ∈ Ls j0 b →
          cen j0 = p ∨ cen j0 = q := by
        intro a b hin p q hp hq
        have hc : cen j0 = if (Ls j0 a).card = 1 then (Ls j0 a).toList.headD 0 else (Ls j0 b).toList.headD 0 := by
          simp only [cen, hg0, Option.elim_some, hin, List.getD_cons_zero, List.getD_cons_succ]
        rw [hc]
        by_cases h1 : (Ls j0 a).card = 1
        · rw [if_pos h1]; exact Or.inl (hhead _ _ h1 hp)
        · rw [if_neg h1]
          right
          apply hhead _ _ _ hq
          have ha2 : 1 < (Ls j0 a).card := by
            have := Finset.card_pos.2 ⟨p, hp⟩; omega
          by_contra hb1
          have hb2 : 2 ≤ (Ls j0 b).card := by
            have := Finset.card_pos.2 ⟨q, hq⟩; omega
          obtain ⟨p', hp', hpp'⟩ := Finset.exists_mem_ne ha2 p
          exact AF_B1b p p' (Ls j0 b) (Ne.symm hpp') hb2 (fun r hr => hadj a b hin p hp r hr)
            (fun r hr => hadj a b hin p' hp' r hr)
      rcases hin : g0.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      · rw [hin] at vu; simp [hEvAnd, hEvOr] at vu
      · rw [hin] at vz vu vv
        simp only [hEvAnd, hEvOr, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
          Bool.and_true] at vz vu vv
        rw [hlin a, ← vu, ← vv] at vz
        simp at vz
      · rw [hin] at vz vu vv
        simp only [hEvAnd, hEvOr, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
          Bool.and_true] at vz vu vv
        rw [hlin a, hlin b] at vz
        have memL : ∀ (r : Fin 42) (i : ℕ), (W j0 (List.ofFn fun z : Fin 42 => decide (z = r))).getD i false = true →
            r ∈ Ls j0 i := by
          intro r i h; simp only [Ls, Finset.mem_filter, Finset.mem_univ, true_and]; exact h
        generalize hau : (W j0 (List.ofFn fun z : Fin 42 => decide (z = u))).getD a false = au at vz vu
        generalize hav : (W j0 (List.ofFn fun z : Fin 42 => decide (z = v))).getD a false = av at vz vv
        generalize hbu : (W j0 (List.ofFn fun z : Fin 42 => decide (z = u))).getD b false = bu at vz vu
        generalize hbv : (W j0 (List.ofFn fun z : Fin 42 => decide (z = v))).getD b false = bv at vz vv
        cases au <;> cases av <;> cases bu <;> cases bv <;> simp at vz vu vv
        all_goals first
          | exact hfin a b hin u v (memL u a hau) (memL v b hbv)
          | exact (hfin a b hin v u (memL v a hav) (memL u b hbu)).symm
      · rw [hin] at hlen2; simp at hlen2
    refine ⟨G, ?_, ?_⟩
    · apply AF_A6 G cen
      intro u v huv
      refine ⟨fj u v, ?_, hcov u v huv⟩
      simp only [G, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(u, v), huv, rfl⟩
    · intro j hj
      simp only [G, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨⟨u, v⟩, huv, rfl⟩ := hj
      simp only [fj, dif_pos huv]
      obtain ⟨g, hg, hop, -⟩ := Nat.find_spec (hex u v huv)
      exact ⟨g, hg, hop⟩
  intro x1 x2 C hmono hsize hS hacc hrej
  obtain ⟨D, hDm, hDs, hDacc, hDrej, hDN1⟩ := normalN1 C hmono hsize hacc hrej
  obtain ⟨GA, hGA, hGAop⟩ := hAfull D hDm hDacc hDrej hDN1
  obtain ⟨GO, hGO, hGOop⟩ := orBound D hDm hDacc hDrej hDN1
  have hdisj : Disjoint GA GO := by
    rw [Finset.disjoint_left]
    intro j ha hb
    obtain ⟨g, hg, hop⟩ := hGAop j ha
    obtain ⟨g', hg', hop'⟩ := hGOop j hb
    rw [hg] at hg'
    cases hg'
    rw [hop] at hop'
    cases hop'
  have hsub : GA ∪ GO ⊆ Finset.range D.gates.length := by
    intro j hj
    rw [Finset.mem_union] at hj
    have hex : ∃ g : Gate, D.gates[j]? = some g := by
      rcases hj with h | h
      · obtain ⟨g, hg, -⟩ := hGAop j h; exact ⟨g, hg⟩
      · obtain ⟨g, hg, -⟩ := hGOop j h; exact ⟨g, hg⟩
    obtain ⟨g, hg⟩ := hex
    rw [Finset.mem_range]
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hg
    cases hg
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_range] at hc
  have hsz : D.size = D.gates.length := rfl
  omega
