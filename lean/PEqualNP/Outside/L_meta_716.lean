import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_716

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

private def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

private def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

private lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) :
    (L ++ [S]).getD L.length d = S := by
  simp

private lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (stepW W g) (stepW W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [stepW]; omega, by simp [stepW]; omega, ?_⟩
  intro w
  simp only [stepW, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    have hL : (W' ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]).getD (wmap n m π w) false =
        W'.getD (wmap n m π w) false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
    have hR : (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]).getD w false =
        W.getD w false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hw, ← List.getD_eq_getElem?_getD]
    rw [hL, hR]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split <;> omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split <;> omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl stepW W) ((gs.map (relGate n m π)).foldl stepW W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

private lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · next h =>
    have hp := (π ⟨w, h⟩).isLt
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [h, hp]
  · next h =>
    have hL : (List.ofFn x).getD (w - n + m) false = false :=
      List.getD_eq_default _ _ (by simp)
    have hR : (List.ofFn (x ∘ π)).getD w false = false :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [hL, hR]

private lemma relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

private lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

private lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

private lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

private lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

private lemma xorStep (v : List Bool) (i j : ℕ) (hi : i < v.length) (hj : j < v.length) :
    (wiresFrom [⟨GateOp.or, [i, j]⟩, ⟨GateOp.and, [i, j]⟩, ⟨GateOp.not, [v.length + 1]⟩,
      ⟨GateOp.and, [v.length, v.length + 2]⟩] v).getD (v.length + 3) false
      = xor (v.getD i false) (v.getD j false) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hi, A _ _ hj]
  cases v[i]?.getD false <;> cases v[j]?.getD false <;> rfl

private lemma nxorStep (v : List Bool) (i j : ℕ) (hi : i < v.length) (hj : j < v.length) :
    (wiresFrom [⟨GateOp.or, [i, j]⟩, ⟨GateOp.not, [v.length]⟩, ⟨GateOp.and, [i, j]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = xor (v.getD i false) (!(v.getD j false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hi, A _ _ hj]
  cases v[i]?.getD false <;> cases v[j]?.getD false <;> rfl

private lemma getD_ofFn_last (n : ℕ) (x : Fin (n + 1) → Bool) :
    (List.ofFn x).getD n false = x (Fin.last n) := by
  have hn : n < (List.ofFn x).length := by simp
  rw [List.getD_eq_getElem _ _ hn, List.getElem_ofFn]
  rfl

private lemma xor_fresh_of_pos (n s : ℕ) (g : (Fin n → Bool) → Bool)
    (hc : HasCircuitSize n g s) :
    HasCircuitSize (n + 1)
      (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc)))
      (s + 4) := by
  obtain ⟨C, ok, hsz, hev⟩ := relabel_size (Fin.castSucc : Fin n → Fin (n + 1)) g s hc
  let M := n + 1 + C.gates.length
  by_cases ho : C.output < M
  · refine ⟨⟨C.gates ++ [⟨GateOp.or, [n, C.output]⟩, ⟨GateOp.and, [n, C.output]⟩,
        ⟨GateOp.not, [M + 1]⟩, ⟨GateOp.and, [M, M + 2]⟩], M + 3⟩, ?_, ?_, ?_⟩
    · intro g0 hg0
      rcases List.mem_append.1 hg0 with hg0 | hg0
      · exact ok g0 hg0
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg0
        rcases hg0 with rfl | rfl | rfl | rfl <;> simp
    · simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil] at hsz ⊢
      omega
    · intro x
      simp only [Circuit.eval, wires_eq, wiresFrom_append]
      set v := wiresFrom C.gates (List.ofFn x) with hv
      have lv : v.length = M := by
        rw [hv, length_wiresFrom, List.length_ofFn]
      have hn : n < v.length := by omega
      have hcout : C.output < v.length := by omega
      have h1 : (wiresFrom [⟨GateOp.or, [n, C.output]⟩, ⟨GateOp.and, [n, C.output]⟩,
          ⟨GateOp.not, [M + 1]⟩, ⟨GateOp.and, [M, M + 2]⟩] v).getD (M + 3) false
          = xor (v.getD n false) (v.getD C.output false) := by
        rw [← lv]
        exact xorStep v n C.output hn hcout
      rw [h1]
      have hvn : v.getD n false = x (Fin.last n) := by
        rw [hv, getD_wiresFrom _ _ _ (by simp), getD_ofFn_last]
      have hvo : v.getD C.output false = g (fun i : Fin n => x i.castSucc) := by
        simpa [Circuit.eval, wires_eq, hv, Function.comp_def] using hev x
      rw [hvn, hvo]
  · refine ⟨⟨[], n⟩, by intro g0 hg0; simp at hg0, by simp [Circuit.size], ?_⟩
    intro x
    have hg0 : g (fun i : Fin n => x i.castSucc) = false := by
      have h1 := hev x
      simp only [Circuit.eval, wires_eq, Function.comp_def] at h1
      rw [← h1]
      apply List.getD_eq_default
      rw [length_wiresFrom, List.length_ofFn]
      omega
    simp only [Circuit.eval, Circuit.wires, List.foldl_nil, hg0, getD_ofFn_last, Bool.xor_false]

private lemma xor_fresh_of_neg (n s : ℕ) (g : (Fin n → Bool) → Bool)
    (hc : HasCircuitSize n (fun y : Fin n → Bool => !(g y)) s) :
    HasCircuitSize (n + 1)
      (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc)))
      (s + 4) := by
  obtain ⟨C, ok, hsz, hev⟩ :=
    relabel_size (Fin.castSucc : Fin n → Fin (n + 1)) (fun y : Fin n → Bool => !(g y)) s hc
  let M := n + 1 + C.gates.length
  by_cases ho : C.output < M
  · refine ⟨⟨C.gates ++ [⟨GateOp.or, [n, C.output]⟩, ⟨GateOp.not, [M]⟩,
        ⟨GateOp.and, [n, C.output]⟩, ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3⟩, ?_, ?_, ?_⟩
    · intro g0 hg0
      rcases List.mem_append.1 hg0 with hg0 | hg0
      · exact ok g0 hg0
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg0
        rcases hg0 with rfl | rfl | rfl | rfl <;> simp
    · simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil] at hsz ⊢
      omega
    · intro x
      simp only [Circuit.eval, wires_eq, wiresFrom_append]
      set v := wiresFrom C.gates (List.ofFn x) with hv
      have lv : v.length = M := by
        rw [hv, length_wiresFrom, List.length_ofFn]
      have hn : n < v.length := by omega
      have hcout : C.output < v.length := by omega
      have h1 : (wiresFrom [⟨GateOp.or, [n, C.output]⟩, ⟨GateOp.not, [M]⟩,
          ⟨GateOp.and, [n, C.output]⟩, ⟨GateOp.or, [M + 1, M + 2]⟩] v).getD (M + 3) false
          = xor (v.getD n false) (!(v.getD C.output false)) := by
        rw [← lv]
        exact nxorStep v n C.output hn hcout
      rw [h1]
      have hvn : v.getD n false = x (Fin.last n) := by
        rw [hv, getD_wiresFrom _ _ _ (by simp), getD_ofFn_last]
      have hvo : v.getD C.output false = !(g (fun i : Fin n => x i.castSucc)) := by
        simpa [Circuit.eval, wires_eq, hv, Function.comp_def] using hev x
      rw [hvn, hvo, Bool.not_not]
  · refine ⟨⟨[⟨GateOp.not, [n]⟩], n + 1⟩, ?_, by simp [Circuit.size], ?_⟩
    · intro g0 hg0
      simp only [List.mem_singleton] at hg0
      subst hg0
      simp
    · intro x
      have hg1 : g (fun i : Fin n => x i.castSucc) = true := by
        have h1 := hev x
        simp only [Circuit.eval, wires_eq, Function.comp_def] at h1
        have h2 : (wiresFrom C.gates (List.ofFn x)).getD C.output false = false := by
          apply List.getD_eq_default
          rw [length_wiresFrom, List.length_ofFn]
          omega
        rw [h2] at h1
        cases h3 : g (fun i : Fin n => x i.castSucc) <;> simp_all
      have hlen := getD_snoc_eq (List.ofFn x) (!x (Fin.last n)) false
      rw [List.length_ofFn] at hlen
      simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, List.map_cons,
        List.map_nil, getD_ofFn_last, GateOp.eval, List.headD_cons, hg1, Bool.xor_true]
      exact hlen

end PEqualNP.Outside.L_meta_716

theorem PEqualNP.Outside.L_meta_716 : ∀ (n s : ℕ) (g : (Fin n → Bool) → Bool), (PEqualNP.MetaComplexity.HasCircuitSize n g s → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => !(g y)) s → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4)) := by
  intro n s g
  exact ⟨PEqualNP.Outside.L_meta_716.xor_fresh_of_pos n s g,
    PEqualNP.Outside.L_meta_716.xor_fresh_of_neg n s g⟩
