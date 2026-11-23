import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_707

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue U B F i v1 = sideTrue U B F i v2 := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩

private lemma gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi d1 d2 hd1 hd2
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
    simp only [gateValFuel]
    have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U k1 j = C.gateValFuel U k2 j := by
      intro j hji
      exact ih j (by omega) k1 k2 (by omega) (by omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have heq : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_indep C U C.size i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private def substVars {n k : ℕ} (i0 : Fin k) (B0 : Finset (Fin n))
    (B : Finset (Fin n)) (G : Finset (Fin k)) : Finset (Fin n) :=
  if i0 ∈ G then B ∪ B0 else B

private def substGates {k : ℕ} (i0 : Fin k) (F0 : Finset (Fin k))
    (G : Finset (Fin k)) : Finset (Fin k) :=
  if i0 ∈ G then (G.erase i0) ∪ F0 else G

private def substCircuit {n : ℕ} (C : AndCountCircuit n) (i0 : Fin C.size)
    (B0 : Finset (Fin n)) (F0 : Finset (Fin C.size)) : AndCountCircuit n where
  size := C.size
  leftVars i := substVars i0 B0 (C.leftVars i) (C.leftGates i)
  leftGates i := substGates i0 F0 (C.leftGates i)
  rightVars i := substVars i0 B0 (C.rightVars i) (C.rightGates i)
  rightGates i := substGates i0 F0 (C.rightGates i)
  outVars := substVars i0 B0 C.outVars C.outGates
  outGates := substGates i0 F0 C.outGates

private lemma subst_wf {n : ℕ} (C : AndCountCircuit n) (hWF : C.WellFormed)
    (i0 : Fin C.size) (B0 : Finset (Fin n)) (F0 : Finset (Fin C.size))
    (hF0 : ∀ j ∈ F0, j < i0) :
    (substCircuit C i0 B0 F0).WellFormed := by
  intro i
  constructor
  · intro j hj
    change j ∈ substGates i0 F0 (C.leftGates i) at hj
    unfold substGates at hj
    split_ifs at hj with hi0
    · have hi0lt : i0 < i := (hWF i).1 i0 hi0
      rcases Finset.mem_union.mp hj with hje | hjf
      · exact (hWF i).1 j (Finset.mem_of_mem_erase hje)
      · exact lt_trans (hF0 j hjf) hi0lt
    · exact (hWF i).1 j hj
  · intro j hj
    change j ∈ substGates i0 F0 (C.rightGates i) at hj
    unfold substGates at hj
    split_ifs at hj with hi0
    · have hi0lt : i0 < i := (hWF i).2 i0 hi0
      rcases Finset.mem_union.mp hj with hje | hjf
      · exact (hWF i).2 j (Finset.mem_of_mem_erase hje)
      · exact lt_trans (hF0 j hjf) hi0lt
    · exact (hWF i).2 j hj

private lemma subst_sideTrue {n : ℕ} (C : AndCountCircuit n)
    (i0 : Fin C.size) (B0 : Finset (Fin n)) (F0 : Finset (Fin C.size))
    (hF0 : ∀ j ∈ F0, j < i0) (U : Finset (Fin n))
    (hi0 : C.gateVal U i0 = true ↔ ((∃ v ∈ B0, v ∈ U) ∨ ∃ j ∈ F0, C.gateVal U j = true))
    (B : Finset (Fin n)) (G : Finset (Fin C.size)) (i : Fin C.size)
    (hG : ∀ j ∈ G, j < i)
    (val : Fin C.size → Bool) (hval : ∀ j < i, val j = C.gateVal U j) :
    sideTrue U (substVars i0 B0 B G) (substGates i0 F0 G) i val =
      sideTrue U B G i (C.gateVal U) := by
  unfold sideTrue substVars substGates
  split_ifs with hmem
  · have hi0lt : i0 < i := hG i0 hmem
    refine decide_eq_decide.mpr ?_
    constructor
    · rintro (⟨v, hv, hvU⟩ | ⟨j, hj, hji, hjv⟩)
      · rcases Finset.mem_union.mp hv with hvB | hvB0
        · exact Or.inl ⟨v, hvB, hvU⟩
        · exact Or.inr ⟨i0, hmem, hi0lt, hi0.mpr (Or.inl ⟨v, hvB0, hvU⟩)⟩
      · rw [hval j hji] at hjv
        rcases Finset.mem_union.mp hj with hje | hjF0
        · exact Or.inr ⟨j, Finset.mem_of_mem_erase hje, hji, hjv⟩
        · exact Or.inr ⟨i0, hmem, hi0lt, hi0.mpr (Or.inr ⟨j, hjF0, hjv⟩)⟩
    · rintro (⟨v, hvB, hvU⟩ | ⟨j, hjG, hji, hjv⟩)
      · exact Or.inl ⟨v, Finset.mem_union_left _ hvB, hvU⟩
      · by_cases hji0 : j = i0
        · subst hji0
          rcases hi0.mp hjv with ⟨v, hvB0, hvU⟩ | ⟨k, hkF0, hkv⟩
          · exact Or.inl ⟨v, Finset.mem_union_right _ hvB0, hvU⟩
          · have hki : k < i := lt_trans (hF0 k hkF0) hji
            exact Or.inr ⟨k, Finset.mem_union_right _ hkF0, hki, by rwa [hval k hki]⟩
        · exact Or.inr ⟨j, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hji0, hjG⟩),
            hji, by rwa [hval j hji]⟩
  · refine decide_eq_decide.mpr ?_
    constructor
    · rintro (hv | ⟨j, hjG, hji, hjv⟩)
      · exact Or.inl hv
      · exact Or.inr ⟨j, hjG, hji, by rwa [← hval j hji]⟩
    · rintro (hv | ⟨j, hjG, hji, hjv⟩)
      · exact Or.inl hv
      · exact Or.inr ⟨j, hjG, hji, by rwa [hval j hji]⟩

private lemma subst_gateVal {n : ℕ} (C : AndCountCircuit n) (hWF : C.WellFormed)
    (i0 : Fin C.size) (B0 : Finset (Fin n)) (F0 : Finset (Fin C.size))
    (hF0 : ∀ j ∈ F0, j < i0) (U : Finset (Fin n))
    (hi0 : C.gateVal U i0 = true ↔ ((∃ v ∈ B0, v ∈ U) ∨ ∃ j ∈ F0, C.gateVal U j = true)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      (substCircuit C i0 B0 F0).gateVal U i = C.gateVal U i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    rw [gateVal_unfold (substCircuit C i0 B0 F0) U i, gateVal_unfold C U i]
    have hval : ∀ j : Fin C.size, j < i →
        (substCircuit C i0 B0 F0).gateVal U j = C.gateVal U j :=
      fun j hji => ih j (by omega)
    change (sideTrue U (substVars i0 B0 (C.leftVars i) (C.leftGates i))
          (substGates i0 F0 (C.leftGates i)) i ((substCircuit C i0 B0 F0).gateVal U) &&
        sideTrue U (substVars i0 B0 (C.rightVars i) (C.rightGates i))
          (substGates i0 F0 (C.rightGates i)) i ((substCircuit C i0 B0 F0).gateVal U)) =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U))
    rw [subst_sideTrue C i0 B0 F0 hF0 U hi0 (C.leftVars i) (C.leftGates i) i (hWF i).1 _ hval,
        subst_sideTrue C i0 B0 F0 hF0 U hi0 (C.rightVars i) (C.rightGates i) i (hWF i).2 _ hval]

private lemma subst_eval {n : ℕ} (C : AndCountCircuit n) (hWF : C.WellFormed)
    (i0 : Fin C.size) (B0 : Finset (Fin n)) (F0 : Finset (Fin C.size))
    (hF0 : ∀ j ∈ F0, j < i0) (U : Finset (Fin n))
    (hi0 : C.gateVal U i0 = true ↔ ((∃ v ∈ B0, v ∈ U) ∨ ∃ j ∈ F0, C.gateVal U j = true)) :
    (substCircuit C i0 B0 F0).eval U = C.eval U := by
  unfold AndCountCircuit.eval
  refine decide_eq_decide.mpr ?_
  change ((∃ v ∈ substVars i0 B0 C.outVars C.outGates, v ∈ U) ∨
      ∃ j ∈ substGates i0 F0 C.outGates, (substCircuit C i0 B0 F0).gateVal U j = true) ↔
    ((∃ v ∈ C.outVars, v ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true)
  have hgv : ∀ j : Fin C.size, (substCircuit C i0 B0 F0).gateVal U j = C.gateVal U j :=
    fun j => subst_gateVal C hWF i0 B0 F0 hF0 U hi0 C.size j j.isLt
  unfold substVars substGates
  split_ifs with hmem
  · constructor
    · rintro (⟨v, hv, hvU⟩ | ⟨j, hj, hjv⟩)
      · rcases Finset.mem_union.mp hv with hvO | hvB0
        · exact Or.inl ⟨v, hvO, hvU⟩
        · exact Or.inr ⟨i0, hmem, hi0.mpr (Or.inl ⟨v, hvB0, hvU⟩)⟩
      · rw [hgv j] at hjv
        rcases Finset.mem_union.mp hj with hje | hjF0
        · exact Or.inr ⟨j, Finset.mem_of_mem_erase hje, hjv⟩
        · exact Or.inr ⟨i0, hmem, hi0.mpr (Or.inr ⟨j, hjF0, hjv⟩)⟩
    · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
      · exact Or.inl ⟨v, Finset.mem_union_left _ hvO, hvU⟩
      · by_cases hji0 : j = i0
        · subst hji0
          rcases hi0.mp hjv with ⟨v, hvB0, hvU⟩ | ⟨k, hkF0, hkv⟩
          · exact Or.inl ⟨v, Finset.mem_union_right _ hvB0, hvU⟩
          · exact Or.inr ⟨k, Finset.mem_union_right _ hkF0, by rwa [hgv k]⟩
        · exact Or.inr ⟨j, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hji0, hjO⟩),
            by rwa [hgv j]⟩
  · constructor
    · rintro (hv | ⟨j, hjO, hjv⟩)
      · exact Or.inl hv
      · exact Or.inr ⟨j, hjO, by rwa [← hgv j]⟩
    · rintro (hv | ⟨j, hjO, hjv⟩)
      · exact Or.inl hv
      · exact Or.inr ⟨j, hjO, by rwa [hgv j]⟩

private lemma substGates_not_mem {k : ℕ} (i0 : Fin k) (F0 : Finset (Fin k))
    (hF0 : ∀ j ∈ F0, j < i0) (G : Finset (Fin k)) :
    i0 ∉ substGates i0 F0 G := by
  unfold substGates
  split_ifs with h
  · intro hmem
    rcases Finset.mem_union.mp hmem with h1 | h2
    · exact (Finset.mem_erase.mp h1).1 rfl
    · exact lt_irrefl i0 (hF0 i0 h2)
  · exact h

private lemma substGates_preserve_not_mem {k : ℕ} (i0 a : Fin k) (F0 : Finset (Fin k))
    (haF0 : a ∉ F0) (G : Finset (Fin k)) (haG : a ∉ G) :
    a ∉ substGates i0 F0 G := by
  unfold substGates
  split_ifs with h
  · intro hmem
    rcases Finset.mem_union.mp hmem with h1 | h2
    · exact haG (Finset.mem_of_mem_erase h1)
    · exact haF0 h2
  · exact haG

private def restrictCircuit {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size)) :
    AndCountCircuit n where
  size := K.card
  leftVars i := C.leftVars (K.orderEmbOfFin rfl i)
  leftGates i := Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.leftGates (K.orderEmbOfFin rfl i))
  rightVars i := C.rightVars (K.orderEmbOfFin rfl i)
  rightGates i := Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.rightGates (K.orderEmbOfFin rfl i))
  outVars := C.outVars
  outGates := Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.outGates)

private lemma restrict_mem_leftGates {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (i j : Fin K.card) :
    j ∈ (restrictCircuit C K).leftGates i ↔
      K.orderEmbOfFin rfl j ∈ C.leftGates (K.orderEmbOfFin rfl i) := by
  change j ∈ Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.leftGates (K.orderEmbOfFin rfl i)) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

private lemma restrict_mem_rightGates {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (i j : Fin K.card) :
    j ∈ (restrictCircuit C K).rightGates i ↔
      K.orderEmbOfFin rfl j ∈ C.rightGates (K.orderEmbOfFin rfl i) := by
  change j ∈ Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.rightGates (K.orderEmbOfFin rfl i)) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

private lemma restrict_mem_outGates {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (j : Fin K.card) :
    j ∈ (restrictCircuit C K).outGates ↔ K.orderEmbOfFin rfl j ∈ C.outGates := by
  change j ∈ Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.outGates) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

private lemma restrict_wf {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (hWF : C.WellFormed) : (restrictCircuit C K).WellFormed := by
  intro i
  constructor
  · intro j hj
    have hj' := (restrict_mem_leftGates C K i j).mp hj
    exact (K.orderEmbOfFin rfl).lt_iff_lt.mp ((hWF (K.orderEmbOfFin rfl i)).1 _ hj')
  · intro j hj
    have hj' := (restrict_mem_rightGates C K i j).mp hj
    exact (K.orderEmbOfFin rfl).lt_iff_lt.mp ((hWF (K.orderEmbOfFin rfl i)).2 _ hj')

private lemma restrict_gateVal_eq {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (hK : ∀ i : Fin C.size, (∀ j ∈ C.leftGates i, j ∈ K) ∧ (∀ j ∈ C.rightGates i, j ∈ K))
    (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin K.card), i.val < m →
      (restrictCircuit C K).gateVal U i = C.gateVal U (K.orderEmbOfFin rfl i) := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    rw [gateVal_unfold (restrictCircuit C K) U i, gateVal_unfold C U (K.orderEmbOfFin rfl i)]
    congr 1
    · unfold sideTrue
      refine decide_eq_decide.mpr ?_
      constructor
      · rintro (hv | ⟨j, hjF, hji, hjv⟩)
        · exact Or.inl hv
        · exact Or.inr ⟨K.orderEmbOfFin rfl j, (restrict_mem_leftGates C K i j).mp hjF,
            (K.orderEmbOfFin rfl).lt_iff_lt.mpr hji, by rwa [← ih j (by omega)]⟩
      · rintro (hv | ⟨j, hjF, hji, hjv⟩)
        · exact Or.inl hv
        · have hjK : j ∈ K := (hK (K.orderEmbOfFin rfl i)).1 j hjF
          have hjr : j ∈ Set.range (K.orderEmbOfFin rfl) := by
            rw [Finset.range_orderEmbOfFin]
            exact hjK
          obtain ⟨j', hj'⟩ := hjr
          have hj'lt : j' < i := (K.orderEmbOfFin rfl).lt_iff_lt.mp (by rw [hj']; exact hji)
          refine Or.inr ⟨j', (restrict_mem_leftGates C K i j').mpr (by rw [hj']; exact hjF),
            hj'lt, ?_⟩
          rw [ih j' (by omega), hj']
          exact hjv
    · unfold sideTrue
      refine decide_eq_decide.mpr ?_
      constructor
      · rintro (hv | ⟨j, hjF, hji, hjv⟩)
        · exact Or.inl hv
        · exact Or.inr ⟨K.orderEmbOfFin rfl j, (restrict_mem_rightGates C K i j).mp hjF,
            (K.orderEmbOfFin rfl).lt_iff_lt.mpr hji, by rwa [← ih j (by omega)]⟩
      · rintro (hv | ⟨j, hjF, hji, hjv⟩)
        · exact Or.inl hv
        · have hjK : j ∈ K := (hK (K.orderEmbOfFin rfl i)).2 j hjF
          have hjr : j ∈ Set.range (K.orderEmbOfFin rfl) := by
            rw [Finset.range_orderEmbOfFin]
            exact hjK
          obtain ⟨j', hj'⟩ := hjr
          have hj'lt : j' < i := (K.orderEmbOfFin rfl).lt_iff_lt.mp (by rw [hj']; exact hji)
          refine Or.inr ⟨j', (restrict_mem_rightGates C K i j').mpr (by rw [hj']; exact hjF),
            hj'lt, ?_⟩
          rw [ih j' (by omega), hj']
          exact hjv

private lemma restrict_eval_eq {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (hK : ∀ i : Fin C.size, (∀ j ∈ C.leftGates i, j ∈ K) ∧ (∀ j ∈ C.rightGates i, j ∈ K))
    (hOut : ∀ j ∈ C.outGates, j ∈ K) (U : Finset (Fin n)) :
    (restrictCircuit C K).eval U = C.eval U := by
  unfold AndCountCircuit.eval
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjO, hjv⟩)
    · exact Or.inl hv
    · refine Or.inr ⟨K.orderEmbOfFin rfl j, (restrict_mem_outGates C K j).mp hjO, ?_⟩
      rwa [← restrict_gateVal_eq C K hK U K.card j j.isLt]
  · rintro (hv | ⟨j, hjO, hjv⟩)
    · exact Or.inl hv
    · have hjK : j ∈ K := hOut j hjO
      have hjr : j ∈ Set.range (K.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact hjK
      obtain ⟨j', hj'⟩ := hjr
      refine Or.inr ⟨j', (restrict_mem_outGates C K j').mpr (by rw [hj']; exact hjO), ?_⟩
      rw [restrict_gateVal_eq C K hK U K.card j' j'.isLt, hj']
      exact hjv

private lemma unuse_all {n : ℕ} (C0 : AndCountCircuit n) (hWF0 : C0.WellFormed)
    (D : Set (Finset (Fin n))) :
    ∀ (m : ℕ) (S : Finset (Fin C0.size)), S.card = m →
      (∀ i ∈ S, ∃ B : Finset (Fin n), ∃ F : Finset (Fin C0.size), (∀ j ∈ F, j < i) ∧
        ∀ U ∈ D, C0.gateVal U i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C0.gateVal U j = true)) →
      ∃ (lVars rVars : Fin C0.size → Finset (Fin n))
        (lGates rGates : Fin C0.size → Finset (Fin C0.size))
        (oVars : Finset (Fin n)) (oGates : Finset (Fin C0.size)),
        let C : AndCountCircuit n := ⟨C0.size, lVars, lGates, rVars, rGates, oVars, oGates⟩
        C.WellFormed ∧
        (∀ U ∈ D, C.eval U = C0.eval U) ∧
        (∀ U ∈ D, ∀ j : Fin C0.size, C.gateVal U j = C0.gateVal U j) ∧
        (∀ i ∈ S, (∀ a : Fin C0.size, i ∉ lGates a ∧ i ∉ rGates a) ∧ i ∉ oGates) := by
  intro m
  induction m with
  | zero =>
    intro S hcard _
    have hS : S = ∅ := Finset.card_eq_zero.mp hcard
    subst hS
    refine ⟨C0.leftVars, C0.rightVars, C0.leftGates, C0.rightGates, C0.outVars, C0.outGates,
      hWF0, fun _ _ => rfl, fun _ _ _ => rfl, ?_⟩
    intro i hi
    simp at hi
  | succ m ih =>
    intro S hcard hS
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    let i0 := S.min' hne
    have hi0S : i0 ∈ S := Finset.min'_mem S hne
    have hcard' : (S.erase i0).card = m := by
      have := Finset.card_erase_add_one hi0S
      omega
    have hS' : ∀ i ∈ S.erase i0, ∃ B : Finset (Fin n), ∃ F : Finset (Fin C0.size), (∀ j ∈ F, j < i) ∧
        ∀ U ∈ D, C0.gateVal U i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C0.gateVal U j = true) :=
      fun i hi => hS i (Finset.mem_of_mem_erase hi)
    obtain ⟨lV, rV, lG, rG, oV, oG, hWF, hev, hgv, hun⟩ := ih (S.erase i0) hcard' hS'
    let C : AndCountCircuit n := ⟨C0.size, lV, lG, rV, rG, oV, oG⟩
    obtain ⟨B0, F0, hF0lt, hD0⟩ := hS i0 hi0S
    refine ⟨fun i => substVars i0 B0 (lV i) (lG i),
      fun i => substVars i0 B0 (rV i) (rG i),
      fun i => substGates i0 F0 (lG i),
      fun i => substGates i0 F0 (rG i),
      substVars i0 B0 oV oG,
      substGates i0 F0 oG,
      subst_wf C hWF i0 B0 F0 hF0lt, ?_, ?_, ?_⟩
    · intro U hU
      have hi0C : C.gateVal U i0 = true ↔ ((∃ v ∈ B0, v ∈ U) ∨ ∃ j ∈ F0, C.gateVal U j = true) := by
        rw [hgv U hU i0, hD0 U hU]
        constructor
        · rintro (hv | ⟨j, hjF0, hjv⟩)
          · exact Or.inl hv
          · exact Or.inr ⟨j, hjF0, by rwa [hgv U hU j]⟩
        · rintro (hv | ⟨j, hjF0, hjv⟩)
          · exact Or.inl hv
          · exact Or.inr ⟨j, hjF0, by rwa [← hgv U hU j]⟩
      change (substCircuit C i0 B0 F0).eval U = C0.eval U
      rw [subst_eval C hWF i0 B0 F0 hF0lt U hi0C, hev U hU]
    · intro U hU j
      have hi0C : C.gateVal U i0 = true ↔ ((∃ v ∈ B0, v ∈ U) ∨ ∃ j ∈ F0, C.gateVal U j = true) := by
        rw [hgv U hU i0, hD0 U hU]
        constructor
        · rintro (hv | ⟨k, hkF0, hkv⟩)
          · exact Or.inl hv
          · exact Or.inr ⟨k, hkF0, by rwa [hgv U hU k]⟩
        · rintro (hv | ⟨k, hkF0, hkv⟩)
          · exact Or.inl hv
          · exact Or.inr ⟨k, hkF0, by rwa [← hgv U hU k]⟩
      change (substCircuit C i0 B0 F0).gateVal U j = C0.gateVal U j
      rw [subst_gateVal C hWF i0 B0 F0 hF0lt U hi0C C.size j j.isLt, hgv U hU j]
    · intro i hi
      by_cases hii0 : i = i0
      · subst hii0
        refine ⟨fun a => ⟨substGates_not_mem i0 F0 hF0lt (lG a),
          substGates_not_mem i0 F0 hF0lt (rG a)⟩,
          substGates_not_mem i0 F0 hF0lt oG⟩
      · have hiS' : i ∈ S.erase i0 := Finset.mem_erase.mpr ⟨hii0, hi⟩
        have hlt : i < i0 → False := by
          intro hlt
          exact not_le_of_gt hlt (Finset.min'_le S i hi)
        have hiF0 : i ∉ F0 := fun hmem => hlt (hF0lt i hmem)
        refine ⟨fun a => ⟨substGates_preserve_not_mem i0 i F0 hiF0 (lG a) ((hun i hiS').1 a).1,
          substGates_preserve_not_mem i0 i F0 hiF0 (rG a) ((hun i hiS').1 a).2⟩,
          substGates_preserve_not_mem i0 i F0 hiF0 oG (hun i hiS').2⟩

end PEqualNP.Outside.L_meta_707

theorem PEqualNP.Outside.L_meta_707 : ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n), C.WellFormed →
    ∀ (D : Set (Finset (Fin n))) (S : Finset (Fin C.size)),
      (∀ i ∈ S, ∃ B : Finset (Fin n), ∃ F : Finset (Fin C.size), (∀ j ∈ F, j < i) ∧
        ∀ U ∈ D, C.gateVal U i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true)) →
      ∃ C' : PEqualNP.AndCount.AndCountCircuit n, C'.WellFormed ∧ C'.size + S.card ≤ C.size ∧
        ∀ U ∈ D, C'.eval U = C.eval U := by
  intro n C0 hWF0 D S hS
  obtain ⟨lV, rV, lG, rG, oV, oG, hWF, hev, _, hun⟩ :=
    PEqualNP.Outside.L_meta_707.unuse_all C0 hWF0 D S.card S rfl hS
  let C : PEqualNP.AndCount.AndCountCircuit n := ⟨C0.size, lV, lG, rV, rG, oV, oG⟩
  let K : Finset (Fin C.size) := Finset.univ \ S
  have hK : ∀ a : Fin C.size,
      (∀ j ∈ C.leftGates a, j ∈ K) ∧ (∀ j ∈ C.rightGates a, j ∈ K) := by
    intro a
    constructor
    · intro j hj
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, fun hjS => ((hun j hjS).1 a).1 hj⟩
    · intro j hj
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, fun hjS => ((hun j hjS).1 a).2 hj⟩
  have hOut : ∀ j ∈ C.outGates, j ∈ K := by
    intro j hj
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, fun hjS => (hun j hjS).2 hj⟩
  refine ⟨PEqualNP.Outside.L_meta_707.restrictCircuit C K,
    PEqualNP.Outside.L_meta_707.restrict_wf C K hWF, ?_, ?_⟩
  · change K.card + S.card ≤ C0.size
    have hcard : K.card + S.card = (Finset.univ : Finset (Fin C0.size)).card :=
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    omega
  · intro U hU
    rw [PEqualNP.Outside.L_meta_707.restrict_eval_eq C K hK hOut U]
    exact hev U hU
