import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_654_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma circuit_eval_eq (C : Circuit) (inp : List Bool) :
    C.eval inp = (C.gates.foldl step inp).getD C.output false := rfl

private def mapWire {N M : ℕ} (σ : Fin N → Fin M) (w : ℕ) : ℕ :=
  if h : w < N then (σ ⟨w, h⟩).val else M + (w - N)

private def mapGate {N M : ℕ} (σ : Fin N → Fin M) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (mapWire σ)⟩

private def remapCircuit {N M : ℕ} (σ : Fin N → Fin M) (C : Circuit) : Circuit :=
  ⟨C.gates.map (mapGate σ), mapWire σ C.output⟩

private lemma remap_fanInTwo {N M : ℕ} (σ : Fin N → Fin M) (C : Circuit) (hC : FanInTwo C) :
    FanInTwo (remapCircuit σ C) := by
  intro g hg
  simp only [remapCircuit, List.mem_map] at hg
  rcases hg with ⟨g₀, hg₀, rfl⟩
  obtain ⟨hop, hlen⟩ := hC g₀ hg₀
  exact ⟨hop, by simp only [mapGate, List.length_map]; exact hlen⟩

private lemma remap_size {N M : ℕ} (σ : Fin N → Fin M) (C : Circuit) :
    (remapCircuit σ C).size = C.size := by
  simp only [Circuit.size, remapCircuit, List.length_map]

private lemma remap_fold_getD {N M : ℕ} (σ : Fin N → Fin M) (x : Fin M → Bool)
    (gs : List Gate) :
    ∀ (w : ℕ),
      ((gs.map (mapGate σ)).foldl step (List.ofFn x)).getD (mapWire σ w) false =
      (gs.foldl step (List.ofFn (fun i : Fin N => x (σ i)))).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    simp only [List.map_nil, List.foldl_nil]
    by_cases hw : w < N
    · simp only [mapWire, hw, ↓reduceDIte, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
        (σ ⟨w, hw⟩).isLt, Option.getD_some]
    · simp only [mapWire, hw, ↓reduceDIte]
      rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]
      rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]
  | append_singleton gs g ih =>
    intro w
    simp only [List.map_append, List.map_singleton, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set w1 := (gs.map (mapGate σ)).foldl step (List.ofFn x)
    set w0 := gs.foldl step (List.ofFn (fun i : Fin N => x (σ i)))
    have hl1 : w1.length = M + gs.length := by
      simp only [w1, fold_length, List.length_ofFn, List.length_map]
    have hl0 : w0.length = N + gs.length := by
      simp only [w0, fold_length, List.length_ofFn]
    have hgeval : (mapGate σ g).op.eval ((mapGate σ g).inputs.map fun i => w1.getD i false) =
        g.op.eval (g.inputs.map fun i => w0.getD i false) := by
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact ih i
    by_cases hw : w < N + gs.length
    · have hmw : mapWire σ w < M + gs.length := by
        simp only [mapWire]
        split_ifs with h1
        · exact Nat.lt_of_lt_of_le (σ ⟨w, h1⟩).isLt (Nat.le_add_right M gs.length)
        · omega
      simp only [step, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega : mapWire σ w < w1.length),
        List.getElem?_append_left (by omega : w < w0.length)]
      simpa only [List.getD_eq_getElem?_getD] using ih w
    · by_cases hweq : w = N + gs.length
      · subst hweq
        have hmw : mapWire σ (N + gs.length) = M + gs.length := by
          simp only [mapWire, show ¬(N + gs.length < N) by omega, ↓reduceDIte]
          omega
        rw [hmw]
        simp only [step, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by omega : w1.length ≤ M + gs.length),
          List.getElem?_append_right (by omega : w0.length ≤ N + gs.length),
          hl1, hl0, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        exact hgeval
      · have hmw : M + gs.length + 1 ≤ mapWire σ w := by
          simp only [mapWire, show ¬(w < N) by omega, ↓reduceDIte]
          omega
        rw [List.getD_eq_default _ _ (by simp only [step, List.length_append, List.length_cons, List.length_nil, hl1]; omega)]
        rw [List.getD_eq_default _ _ (by simp only [step, List.length_append, List.length_cons, List.length_nil, hl0]; omega)]

private lemma remap_eval {N M : ℕ} (σ : Fin N → Fin M) (C : Circuit) (x : Fin M → Bool) :
    (remapCircuit σ C).eval (List.ofFn x) = C.eval (List.ofFn (fun i : Fin N => x (σ i))) := by
  exact remap_fold_getD σ x C.gates C.output

private def addTriple (M : ℕ) (C : Circuit) (c l r : Fin M) : Circuit :=
  let m := C.gates.length
  let outW := if C.output < M + m then C.output else M + m + 2
  ⟨C.gates ++ [⟨GateOp.or, [l.val, r.val]⟩,
               ⟨GateOp.and, [c.val, M + m]⟩,
               ⟨GateOp.or, [outW, M + m + 1]⟩],
   M + m + 2⟩

private lemma addTriple_fanInTwo (M : ℕ) (C : Circuit) (hC : FanInTwo C) (c l r : Fin M) :
    FanInTwo (addTriple M C c l r) := by
  intro g hg
  simp only [addTriple, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with hg | rfl | rfl | rfl
  · exact hC g hg
  · exact ⟨by simp, by simp⟩
  · exact ⟨by simp, by simp⟩
  · exact ⟨by simp, by simp⟩

private lemma addTriple_size (M : ℕ) (C : Circuit) (c l r : Fin M) :
    (addTriple M C c l r).size = C.size + 3 := by
  simp only [Circuit.size, addTriple, List.length_append, List.length_cons, List.length_nil]

private lemma addTriple_eval (M : ℕ) (C : Circuit) (c l r : Fin M) (x : Fin M → Bool) :
    (addTriple M C c l r).eval (List.ofFn x) =
      (C.eval (List.ofFn x) || (x c && (x l || x r))) := by
  rw [circuit_eval_eq, circuit_eval_eq]
  simp only [addTriple, List.foldl_append, List.foldl_cons, List.foldl_nil]
  set m := C.gates.length
  set outW := if C.output < M + m then C.output else M + m + 2
  set w0 := C.gates.foldl step (List.ofFn x)
  have hl0 : w0.length = M + m := by
    simp only [w0, fold_length, List.length_ofFn, m]
  have hget_in : ∀ (a : Fin M), w0.getD a.val false = x a := by
    intro a
    rw [show w0 = C.gates.foldl step (List.ofFn x) from rfl]
    rw [fold_getD_lt C.gates (List.ofFn x) a.val (by rw [List.length_ofFn]; exact a.isLt)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, a.isLt, ↓reduceDIte, Option.getD_some]
  set v1 := x l || x r
  have hw1 : step w0 ⟨GateOp.or, [l.val, r.val]⟩ = w0 ++ [v1] := by
    simp only [step, List.map_cons, List.map_nil, hget_in l, hget_in r, GateOp.eval,
      List.any_cons, List.any_nil, Bool.or_false, id_eq, v1]
  rw [hw1]
  have hw1_c : (w0 ++ [v1]).getD c.val false = x c := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : c.val < w0.length),
      ← List.getD_eq_getElem?_getD, hget_in c]
  have hw1_v1 : (w0 ++ [v1]).getD (M + m) false = v1 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : w0.length ≤ M + m),
      hl0, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  set v2 := x c && v1
  have hw2 : step (w0 ++ [v1]) ⟨GateOp.and, [c.val, M + m]⟩ = w0 ++ [v1] ++ [v2] := by
    simp only [step, List.map_cons, List.map_nil, hw1_c, hw1_v1, GateOp.eval,
      List.all_cons, List.all_nil, Bool.and_true, id_eq, v2]
  rw [hw2]
  have hw2_len : (w0 ++ [v1] ++ [v2]).length = M + m + 2 := by
    simp only [List.length_append, List.length_cons, List.length_nil, hl0]
  have hw2_out : (w0 ++ [v1] ++ [v2]).getD outW false = w0.getD C.output false := by
    by_cases hlt : C.output < M + m
    · have hout : outW = C.output := by simp only [outW, hlt, ↓reduceIte]
      rw [hout]
      rw [List.getD_eq_getElem?_getD, List.append_assoc,
        List.getElem?_append_left (by omega : C.output < w0.length),
        ← List.getD_eq_getElem?_getD]
    · have hout : outW = M + m + 2 := by simp only [outW, hlt, ↓reduceIte]
      rw [hout]
      rw [List.getD_eq_default _ _ (by omega)]
      rw [List.getD_eq_default _ _ (by omega)]
  have hw2_v2 : (w0 ++ [v1] ++ [v2]).getD (M + m + 1) false = v2 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right
      (by simp only [List.length_append, List.length_cons, List.length_nil, hl0]; omega : (w0 ++ [v1]).length ≤ M + m + 1),
      List.length_append, List.length_cons, List.length_nil, hl0, Nat.sub_self,
      List.getElem?_cons_zero, Option.getD_some]
  have hw3 : step (w0 ++ [v1] ++ [v2]) ⟨GateOp.or, [outW, M + m + 1]⟩ =
      (w0 ++ [v1] ++ [v2]) ++ [w0.getD C.output false || v2] := by
    simp only [step, List.map_cons, List.map_nil, hw2_out, hw2_v2, GateOp.eval,
      List.any_cons, List.any_nil, Bool.or_false, id_eq]
  rw [hw3]
  simp only [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega : (w0 ++ [v1] ++ [v2]).length ≤ M + m + 2),
    hw2_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

private lemma addTriples_exists (M : ℕ) (C : Circuit) (hC : FanInTwo C)
    (ts : List (Fin M × Fin M × Fin M)) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = C.size + 3 * ts.length ∧
      ∀ x : Fin M → Bool,
        D.eval (List.ofFn x) =
          (C.eval (List.ofFn x) || decide (∃ t ∈ ts, x t.1 = true ∧ (x t.2.1 = true ∨ x t.2.2 = true))) := by
  induction ts with
  | nil =>
    exact ⟨C, hC, by simp, fun x => by simp⟩
  | cons t ts ih =>
    rcases ih with ⟨D, hD, hsz, hev⟩
    refine ⟨addTriple M D t.1 t.2.1 t.2.2, addTriple_fanInTwo M D hD t.1 t.2.1 t.2.2, ?_, ?_⟩
    · rw [addTriple_size, hsz, List.length_cons]; omega
    · intro x
      rw [addTriple_eval, hev x]
      cases h1 : C.eval (List.ofFn x) <;>
      cases h2 : x t.1 <;>
      cases h3 : x t.2.1 <;>
      cases h4 : x t.2.2 <;>
      simp [h2, h3, h4]

private def pathPred (N h : ℕ) (u v : Fin N) (x : Fin (N + 2 * h + 1) → Bool) : Prop :=
  ∃ i : Fin (2 * h + 1), x (Fin.natAdd N i) = true ∧
    ((i.val = 0 ∧ x (Fin.castAdd (2 * h + 1) u) = true) ∨
     (i.val + 1 = 2 * h + 1 ∧ x (Fin.castAdd (2 * h + 1) v) = true) ∨
     ∃ j : Fin (2 * h + 1), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true)

private def mkIdx (h : ℕ) (a : ℕ) (ha : a < 2 * h + 1) : Fin (2 * h + 1) := ⟨a, ha⟩

private def evenTriple (N h : ℕ) (u v : Fin N) (k : Fin (h + 1)) :
    Fin (N + 2 * h + 1) × Fin (N + 2 * h + 1) × Fin (N + 2 * h + 1) :=
  let c : Fin (N + 2 * h + 1) := Fin.natAdd N (mkIdx h (2 * k.val) (by omega))
  let l : Fin (N + 2 * h + 1) :=
    if hk : k.val = 0 then Fin.castAdd (2 * h + 1) u
    else Fin.natAdd N (mkIdx h (2 * k.val - 1) (by omega))
  let r : Fin (N + 2 * h + 1) :=
    if hk : k.val = h then Fin.castAdd (2 * h + 1) v
    else Fin.natAdd N (mkIdx h (2 * k.val + 1) (by omega))
  (c, l, r)

private def evenTriples (N h : ℕ) (u v : Fin N) :
    List (Fin (N + 2 * h + 1) × Fin (N + 2 * h + 1) × Fin (N + 2 * h + 1)) :=
  (List.finRange (h + 1)).map (evenTriple N h u v)

private lemma evenTriples_iff (N h : ℕ) (u v : Fin N) (x : Fin (N + 2 * h + 1) → Bool) :
    (∃ t ∈ evenTriples N h u v, x t.1 = true ∧ (x t.2.1 = true ∨ x t.2.2 = true)) ↔
      pathPred N h u v x := by
  constructor
  · rintro ⟨t, ht, hc, hlr⟩
    simp only [evenTriples, List.mem_map, List.mem_finRange, true_and] at ht
    rcases ht with ⟨k, rfl⟩
    simp only [evenTriple] at hc hlr
    rcases hlr with hl | hr
    · by_cases hk : k.val = 0
      · simp only [hk, ↓reduceDIte] at hl
        refine ⟨mkIdx h (2 * k.val) (by omega), hc, Or.inl ⟨by simp [mkIdx, hk], hl⟩⟩
      · simp only [hk, ↓reduceDIte] at hl
        refine ⟨mkIdx h (2 * k.val - 1) (by omega), hl,
          Or.inr (Or.inr ⟨mkIdx h (2 * k.val) (by omega), by simp [mkIdx]; omega, hc⟩)⟩
    · by_cases hk : k.val = h
      · simp only [hk, ↓reduceDIte] at hr
        refine ⟨mkIdx h (2 * k.val) (by omega), hc, Or.inr (Or.inl ⟨by simp [mkIdx]; omega, hr⟩)⟩
      · simp only [hk, ↓reduceDIte] at hr
        refine ⟨mkIdx h (2 * k.val) (by omega), hc,
          Or.inr (Or.inr ⟨mkIdx h (2 * k.val + 1) (by omega), by simp [mkIdx], hr⟩)⟩
  · rintro ⟨i, hi, hcase⟩
    rcases hcase with ⟨hi0, hu⟩ | ⟨hih, hv⟩ | ⟨j, hji, hj⟩
    · refine ⟨evenTriple N h u v ⟨0, by omega⟩,
        List.mem_map.2 ⟨⟨0, by omega⟩, List.mem_finRange _, rfl⟩, ?_, Or.inl ?_⟩
      · simp only [evenTriple]
        convert hi using 2; ext; simp only [Fin.val_natAdd, mkIdx, hi0]
      · simp only [evenTriple, ↓reduceDIte]; exact hu
    · refine ⟨evenTriple N h u v ⟨h, by omega⟩,
        List.mem_map.2 ⟨⟨h, by omega⟩, List.mem_finRange _, rfl⟩, ?_, Or.inr ?_⟩
      · simp only [evenTriple]
        convert hi using 2; ext; simp [Fin.natAdd, mkIdx]; omega
      · simp only [evenTriple, ↓reduceDIte]; exact hv
    · by_cases hpar : i.val % 2 = 0
      · let k : Fin (h + 1) := ⟨i.val / 2, by omega⟩
        have hkh : k.val ≠ h := by simp only [k]; omega
        refine ⟨evenTriple N h u v k, List.mem_map.2 ⟨k, List.mem_finRange _, rfl⟩, ?_, Or.inr ?_⟩
        · simp only [evenTriple]
          convert hi using 2; ext; simp [Fin.natAdd, mkIdx, k]; omega
        · simp only [evenTriple, hkh, ↓reduceDIte]
          convert hj using 2; ext; simp [Fin.natAdd, mkIdx, k]; omega
      · let k : Fin (h + 1) := ⟨(i.val + 1) / 2, by omega⟩
        have hk0 : k.val ≠ 0 := by simp only [k]; omega
        refine ⟨evenTriple N h u v k, List.mem_map.2 ⟨k, List.mem_finRange _, rfl⟩, ?_, Or.inl ?_⟩
        · simp only [evenTriple]
          convert hj using 2; ext; simp [Fin.natAdd, mkIdx, k]; omega
        · simp only [evenTriple, hk0, ↓reduceDIte]
          convert hi using 2; ext; simp [Fin.natAdd, mkIdx, k]; omega

private def oddTriple (N h : ℕ) (k : Fin h) :
    Fin (N + 2 * h + 1) × Fin (N + 2 * h + 1) × Fin (N + 2 * h + 1) :=
  (Fin.natAdd N (mkIdx h (2 * k.val + 1) (by omega)),
   Fin.natAdd N (mkIdx h (2 * k.val) (by omega)),
   Fin.natAdd N (mkIdx h (2 * k.val + 2) (by omega)))

private def oddTriples (N h : ℕ) :
    List (Fin (N + 2 * h + 1) × Fin (N + 2 * h + 1) × Fin (N + 2 * h + 1)) :=
  (List.finRange h).map (oddTriple N h)

private lemma oddTriples_iff (N h : ℕ) (u v : Fin N) (x : Fin (N + 2 * h + 1) → Bool) :
    ((x (Fin.castAdd (2 * h + 1) u) = true ∧ x (Fin.natAdd N (mkIdx h 0 (by omega))) = true) ∨
     (x (Fin.castAdd (2 * h + 1) v) = true ∧ x (Fin.natAdd N (mkIdx h (2 * h) (by omega))) = true) ∨
     ∃ t ∈ oddTriples N h, x t.1 = true ∧ (x t.2.1 = true ∨ x t.2.2 = true)) ↔
      pathPred N h u v x := by
  constructor
  · rintro (⟨hu, h0⟩ | ⟨hv, hh⟩ | ⟨t, ht, hc, hlr⟩)
    · exact ⟨mkIdx h 0 (by omega), h0, Or.inl ⟨rfl, hu⟩⟩
    · exact ⟨mkIdx h (2 * h) (by omega), hh, Or.inr (Or.inl ⟨by simp [mkIdx], hv⟩)⟩
    · simp only [oddTriples, List.mem_map, List.mem_finRange, true_and] at ht
      rcases ht with ⟨k, rfl⟩
      simp only [oddTriple] at hc hlr
      rcases hlr with hl | hr
      · exact ⟨mkIdx h (2 * k.val) (by omega), hl,
          Or.inr (Or.inr ⟨mkIdx h (2 * k.val + 1) (by omega), by simp [mkIdx], hc⟩)⟩
      · exact ⟨mkIdx h (2 * k.val + 1) (by omega), hc,
          Or.inr (Or.inr ⟨mkIdx h (2 * k.val + 2) (by omega), by simp [mkIdx], hr⟩)⟩
  · rintro ⟨i, hi, hcase⟩
    rcases hcase with ⟨hi0, hu⟩ | ⟨hih, hv⟩ | ⟨j, hji, hj⟩
    · left
      refine ⟨hu, ?_⟩
      convert hi using 2; ext; simp only [Fin.val_natAdd, mkIdx, hi0]
    · right; left
      refine ⟨hv, ?_⟩
      convert hi using 2; ext; simp [Fin.natAdd, mkIdx]; omega
    · right; right
      by_cases hpar : i.val % 2 = 0
      · let k : Fin h := ⟨i.val / 2, by omega⟩
        refine ⟨oddTriple N h k, List.mem_map.2 ⟨k, List.mem_finRange _, rfl⟩, ?_, Or.inl ?_⟩
        · simp only [oddTriple]; convert hj using 2; ext; simp [Fin.natAdd, mkIdx, k]; omega
        · simp only [oddTriple]; convert hi using 2; ext; simp [Fin.natAdd, mkIdx, k]; omega
      · let k : Fin h := ⟨i.val / 2, by omega⟩
        refine ⟨oddTriple N h k, List.mem_map.2 ⟨k, List.mem_finRange _, rfl⟩, ?_, Or.inr ?_⟩
        · simp only [oddTriple]; convert hi using 2; ext; simp [Fin.natAdd, mkIdx, k]; omega
        · simp only [oddTriple]; convert hj using 2; ext; simp [Fin.natAdd, mkIdx, k]; omega

end PEqualNP.Outside.L_meta_654_aux

theorem PEqualNP.Outside.L_meta_654 :
    ∀ (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool), ∀ s : ℕ,
      (PEqualNP.MetaComplexity.HasCircuitSize N g s →
        PEqualNP.MetaComplexity.HasCircuitSize (N + (2 * h + 1))
          (fun x : Fin (N + 2 * h + 1) → Bool =>
            g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) ||
              decide (∃ i : Fin (2 * h + 1), x (Fin.natAdd N i) = true ∧
                ((i.val = 0 ∧ x (Fin.castAdd (2 * h + 1) u) = true) ∨
                 (i.val + 1 = 2 * h + 1 ∧ x (Fin.castAdd (2 * h + 1) v) = true) ∨
                 ∃ j : Fin (2 * h + 1), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true)))
          (3 * h + s + 3)) ∧
      (PEqualNP.MetaComplexity.HasCircuitSize (N + 2)
          (fun x : Fin (N + 2) → Bool =>
            g (fun i : Fin N => x (Fin.castAdd 2 i)) ||
              (x (Fin.castAdd 2 u) && x (Fin.natAdd N (0 : Fin 2))) ||
              (x (Fin.castAdd 2 v) && x (Fin.natAdd N (1 : Fin 2)))) s →
        PEqualNP.MetaComplexity.HasCircuitSize (N + (2 * h + 1))
          (fun x : Fin (N + 2 * h + 1) → Bool =>
            g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) ||
              decide (∃ i : Fin (2 * h + 1), x (Fin.natAdd N i) = true ∧
                ((i.val = 0 ∧ x (Fin.castAdd (2 * h + 1) u) = true) ∨
                 (i.val + 1 = 2 * h + 1 ∧ x (Fin.castAdd (2 * h + 1) v) = true) ∨
                 ∃ j : Fin (2 * h + 1), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true)))
          (3 * h + s)) := by
  intro N h u v g s
  open PEqualNP.Outside.L_meta_654_aux in
  constructor
  · rintro ⟨C, hC, hsz, hev⟩
    let σ : Fin N → Fin (N + 2 * h + 1) := fun i => Fin.castAdd (2 * h + 1) i
    let C1 := remapCircuit σ C
    have hC1 : PEqualNP.MetaComplexity.FanInTwo C1 := remap_fanInTwo σ C hC
    obtain ⟨D, hD, hDsz, hDev⟩ := addTriples_exists (N + 2 * h + 1) C1 hC1 (evenTriples N h u v)
    refine ⟨D, hD, ?_, ?_⟩
    · rw [hDsz, remap_size]
      simp only [evenTriples, List.length_map, List.length_finRange]
      omega
    · intro x
      rw [hDev x, remap_eval, hev]
      congr 1
      apply Bool.eq_iff_iff.2
      simp only [decide_eq_true_eq]
      exact evenTriples_iff N h u v x
  · rintro ⟨C, hC, hsz, hev⟩
    let σ : Fin (N + 2) → Fin (N + 2 * h + 1) := fun i =>
      if hi : i.val < N then Fin.castAdd (2 * h + 1) ⟨i.val, hi⟩
      else if i.val = N then Fin.natAdd N (mkIdx h 0 (by omega))
      else Fin.natAdd N (mkIdx h (2 * h) (by omega))
    let C1 := remapCircuit σ C
    have hC1 : PEqualNP.MetaComplexity.FanInTwo C1 := remap_fanInTwo σ C hC
    obtain ⟨D, hD, hDsz, hDev⟩ := addTriples_exists (N + 2 * h + 1) C1 hC1 (oddTriples N h)
    refine ⟨D, hD, ?_, ?_⟩
    · rw [hDsz, remap_size]
      simp only [oddTriples, List.length_map, List.length_finRange]
      omega
    · intro x
      rw [hDev x, remap_eval, hev]
      have hσ_in : (fun i : Fin N => x (σ (Fin.castAdd 2 i))) =
          (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) := by
        funext i
        simp only [σ, Fin.val_castAdd, i.isLt, ↓reduceDIte]
      have hσ_u : σ (Fin.castAdd 2 u) = Fin.castAdd (2 * h + 1) u := by
        simp only [σ, Fin.val_castAdd, u.isLt, ↓reduceDIte]
      have hσ_v : σ (Fin.castAdd 2 v) = Fin.castAdd (2 * h + 1) v := by
        simp only [σ, Fin.val_castAdd, v.isLt, ↓reduceDIte]
      have hσ_0 : σ (Fin.natAdd N (0 : Fin 2)) = Fin.natAdd N (mkIdx h 0 (by omega)) := by
        simp only [σ, Fin.val_natAdd, Fin.val_zero, Nat.add_zero, Nat.lt_irrefl, ↓reduceDIte, ↓reduceIte]
      have hσ_1 : σ (Fin.natAdd N (1 : Fin 2)) = Fin.natAdd N (mkIdx h (2 * h) (by omega)) := by
        simp only [σ, Fin.val_natAdd, Fin.val_one, show ¬(N + 1 < N) by omega,
          show ¬(N + 1 = N) by omega, ↓reduceDIte, ↓reduceIte]
      dsimp only
      rw [hσ_in, hσ_u, hσ_v, hσ_0, hσ_1]
      have hiff := oddTriples_iff N h u v x
      cases hg : g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i))
      · simp only [Bool.false_or]
        apply Bool.eq_iff_iff.2
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        simpa only [or_assoc, pathPred] using hiff
      · simp only [Bool.true_or]
