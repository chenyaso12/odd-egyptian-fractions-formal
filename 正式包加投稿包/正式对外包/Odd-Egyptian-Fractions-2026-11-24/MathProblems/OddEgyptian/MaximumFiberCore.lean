module

public import MathProblems.OddEgyptian.Counting
public import MathProblems.OddEgyptian.StructuredFamilies
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian
namespace MaximumFiberCore

open Finset

/-- Two equally large halves, separated in the natural order. -/
private theorem ordered_halves (Y : Finset ℕ) : ∃ L H : Finset ℕ,
    L ⊆ Y ∧ H ⊆ Y ∧ L.card = Y.card / 2 ∧ H.card = Y.card / 2 ∧
    ∀ i ∈ L, ∀ j ∈ H, i < j := by
  let n := Y.card/2
  let e := Y.orderEmbOfFin rfl
  let low (i : Fin n) : Fin Y.card := ⟨i.val, by have := i.isLt; dsimp [n] at *; omega⟩
  let high (i : Fin n) : Fin Y.card := ⟨n+i.val, by have := i.isLt; dsimp [n] at *; omega⟩
  let l : Fin n ↪ ℕ := ⟨fun i => e (low i), fun i j h => Fin.ext (congrArg (fun t : Fin Y.card => t.val) (e.injective h))⟩
  let h : Fin n ↪ ℕ := ⟨fun i => e (high i), by
    intro i j eq
    have he : n+i.val=n+j.val := congrArg Fin.val (e.injective eq)
    exact Fin.ext (by omega)⟩
  refine ⟨univ.map l,univ.map h, ?_, ?_, by simp [n], by simp [n], ?_⟩
  · intro i hi
    obtain ⟨a,_,rfl⟩ := mem_map.mp hi
    exact orderEmbOfFin_mem Y rfl (low a)
  · intro i hi
    obtain ⟨a,_,rfl⟩ := mem_map.mp hi
    exact orderEmbOfFin_mem Y rfl (high a)
  · intro i hi j hj
    obtain ⟨a,_,rfl⟩ := mem_map.mp hi
    obtain ⟨b,_,rfl⟩ := mem_map.mp hj
    apply e.strictMono
    change a.val < n+b.val
    omega

private def tails (v : ℕ → ℕ) (i : ℕ) : Finset ℕ := {v i,i}

private structure Family (P Y : Finset ℕ) (v : ℕ → ℕ) : Prop where
  below : ∀ i ∈ Y, ∀ p ∈ P, p < v i
  order : ∀ i ∈ Y, v i < i
  rep : ∀ i ∈ Y, Represents 1 (P ∪ tails v i)

private theorem Family.disj {P Y : Finset ℕ} {v : ℕ → ℕ} (h : Family P Y v)
    {i : ℕ} (hi : i ∈ Y) : Disjoint P (tails v i) := by
  apply disjoint_left.mpr
  intro p hp ht
  have hpv := h.below i hi p hp
  have hvi := h.order i hi
  simp only [tails,mem_insert,mem_singleton] at ht
  omega

private theorem Family.cardTail {P Y : Finset ℕ} {v : ℕ → ℕ} (h : Family P Y v)
    {i : ℕ} (hi : i ∈ Y) : (tails v i).card = 2 := by
  simp [tails, (h.order i hi).ne]

private theorem Family.left_inj {P Y : Finset ℕ} {v : ℕ → ℕ} (h : Family P Y v) : Set.InjOn v Y := by
  have sum (i : ℕ) (hi : i ∈ Y) :
      (∑ x ∈ P, (1:ℚ)/x) + (1/(v i:ℚ)+1/(i:ℚ)) = 1 := by
    have rep := (h.rep i hi).2
    rw [sum_union (h.disj hi)] at rep
    simpa [tails,(h.order i hi).ne] using rep
  intro i hi j hj hv
  have si := sum i hi
  have sj := sum j hj
  rw [hv] at si
  have eq : 1/(i:ℚ)=1/(j:ℚ) := by linarith
  simpa only [one_div, inv_inj, Nat.cast_inj] using eq

private theorem Family.tail_inj {P Y : Finset ℕ} {v : ℕ → ℕ} (h : Family P Y v) :
    Set.InjOn (tails v) Y := by
  intro i hi j hj he
  have ma (x : ℕ) (hx : x ∈ Y) : (tails v x).sup id = x := by
    simp [tails,max_eq_right (h.order x hx).le]
  simpa only [ma _ hi, ma _ hj] using congrArg (fun s : Finset ℕ => s.sup id) he

private theorem Family.fibers {P Y L : Finset ℕ} {v : ℕ → ℕ} (h : Family P Y v) (hL : L ⊆ Y)
    (x : ℕ) : (L.filter fun i => x ∈ tails v i).card ≤ 2 := by
  let A := L.filter fun i => x=v i
  let B := L.filter fun i => x=i
  have hA : A.card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    obtain ⟨hi,he⟩ := mem_filter.mp hi
    obtain ⟨hj,he'⟩ := mem_filter.mp hj
    exact h.left_inj (hL hi) (hL hj) (he.symm.trans he')
  have hB : B.card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    exact (mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2
  have sub : (L.filter fun i => x ∈ tails v i) ⊆ A ∪ B := by
    intro i hi
    obtain ⟨hi,hs⟩ := mem_filter.mp hi
    rcases mem_insert.mp hs with hs | hs
    · exact mem_union_left _ (mem_filter.mpr ⟨hi,hs⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hi,mem_singleton.mp hs⟩)
  exact (card_le_card sub).trans ((card_union_le ..).trans (by omega))

private def scaled (u : ℕ) (s : Finset ℕ) := s.image (u * ·)

private theorem scaled_card {u : ℕ} (hu : 0 < u) (s : Finset ℕ) : (scaled u s).card = s.card :=
  card_image_of_injective _ (fun _ _ eq => Nat.eq_of_mul_eq_mul_left hu eq)

private theorem scaled_rep {u : ℕ} (hu : 1 < u) (ho : Odd u) {s : Finset ℕ}
    (hs : Represents 1 s) : Represents (1/(u:ℚ)) (scaled u s) := by
  constructor
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
    obtain ⟨ha1,hoa⟩ := hs.1 a ha
    have hle : a ≤ u*a := by simpa using Nat.mul_le_mul_right a hu.le
    exact ⟨ha1.trans_le hle,ho.mul hoa⟩
  · rw [scaled,sum_image (fun _ _ _ _ eq => Nat.eq_of_mul_eq_mul_left (by omega : 0<u) eq)]
    simp only [Nat.cast_mul,one_div,mul_inv_rev,←sum_mul]
    simpa only [one_div,one_mul] using congrArg (fun t : ℚ => t * (u:ℚ)⁻¹) hs.2

private theorem Family.original_le {P Y : Finset ℕ} {v : ℕ → ℕ} (h : Family P Y v)
    {i : ℕ} (hi : i ∈ Y) {x : ℕ} (hx : x ∈ P ∪ tails v i) : x ≤ i := by
  rcases mem_union.mp hx with hp | hy
  · exact ((h.below i hi x hp).trans (h.order i hi)).le
  · simp only [tails,mem_insert,mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact (h.order _ hi).le
    · rfl

private theorem Family.one_fiber {P Y L : Finset ℕ} {v : ℕ → ℕ} {m j u : ℕ}
    (h : Family P Y v) (hL : L ⊆ Y) (hj : j ∈ Y) (hij : ∀ i ∈ L, i < j)
    (hcard : P.card+2=m) (hu : u ∈ P) (huMax : ∀ p ∈ P, p ≤ u) :
    ∃ S : Finset (Finset ℕ), L.card-2*m ≤ S.card ∧ ∀ s ∈ S,
      Represents 1 s ∧ s.card=2*m-1 ∧ s.sup id=u*j := by
  classical
  let W := scaled u (P ∪ tails v j)
  let B := P.erase u ∪ W
  let G := admissibleChoices L W (tails v)
  have huPair := (h.rep j hj).1 u (mem_union_left _ hu)
  have huPos : 0<u := by have := huPair.1; omega
  have hwr : Represents (1/(u:ℚ)) W := scaled_rep huPair.1 huPair.2 (h.rep j hj)
  have hwc : W.card=m := by dsimp only [W]; rw [scaled_card huPos,card_union_of_disjoint (h.disj hj),h.cardTail hj,hcard]
  have dis : Disjoint (P.erase u) W := by
    apply disjoint_left.mpr
    intro x hp hx
    obtain ⟨z,hz,he⟩ := mem_image.mp hx
    have h₁ := (h.rep j hj).1 z hz
    have h₂ := huMax x (mem_of_mem_erase hp)
    have h₃ : u<u*z := by simpa using Nat.mul_lt_mul_of_pos_left h₁.1 huPos
    omega
  have hLast : u*j ∈ W := mem_image.mpr ⟨j,mem_union_right _ (by simp [tails]),rfl⟩
  have hG : L.card-2*m ≤ G.card := by
    rw [← hwc]
    exact card_admissibleChoices L W (tails v) (fun x _ => h.fibers hL x)
  have parts (i : ℕ) (hi : i ∈ G) : i ∈ L ∧ Disjoint B (tails v i) := by
    obtain ⟨hil,hwt⟩ := mem_admissibleChoices.mp hi
    exact ⟨hil,disjoint_union_left.mpr ⟨(h.disj (hL hil)).mono_left (erase_subset _ _),hwt⟩⟩
  have inj : Set.InjOn (fun i => B ∪ tails v i) G := by
    intro i hi i' hi' he
    have h₁ := parts i hi
    have h₂ := parts i' hi'
    apply h.tail_inj (hL h₁.1) (hL h₂.1)
    exact (union_sdiff_cancel_left h₁.2).symm.trans
      ((congrArg (fun s => s \ B) he).trans (union_sdiff_cancel_left h₂.2))
  refine ⟨G.image (fun i => B ∪ tails v i), ?_, ?_⟩
  · rwa [card_image_of_injOn inj]
  intro s hs
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hs
  obtain ⟨hil,hbt⟩ := parts i hi
  have hy := hL hil
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro x hx
    rcases mem_union.mp hx with hx|hx
    · rcases mem_union.mp hx with hx|hx
      · exact (h.rep j hj).1 _ (mem_union_left _ (mem_of_mem_erase hx))
      · exact hwr.1 _ hx
    · exact (h.rep i hy).1 _ (mem_union_right _ hx)
  · rw [sum_union hbt]
    dsimp only [B]
    rw [sum_union dis, hwr.2]
    rw [sum_erase_add P (fun x : ℕ => (1:ℚ)/x) hu]
    simpa only [sum_union (h.disj hy)] using (h.rep i hy).2
  · rw [card_union_of_disjoint hbt]
    dsimp only [B]
    rw [card_union_of_disjoint dis,
      card_erase_of_mem hu, hwc, h.cardTail hy]
    have hp : 0 < P.card := card_pos.mpr ⟨u,hu⟩
    omega
  · apply le_antisymm
    · apply Finset.sup_le
      intro x hx
      have hjmul : j ≤ u*j := by simpa using Nat.mul_le_mul_right j (show 1≤u by omega)
      rcases mem_union.mp hx with hx|hx
      · rcases mem_union.mp hx with hx|hx
        · exact (h.original_le hj (mem_union_left _ (mem_of_mem_erase hx))).trans hjmul
        · obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
          exact Nat.mul_le_mul_left _ (h.original_le hj hz)
      · exact ((h.original_le hy (mem_union_right _ hx)).trans (hij _ hil).le).trans hjmul
    · exact le_sup (f:=id) (mem_union_left _ (mem_union_right _ hLast))

/-- Splicing the upper halves into the lower halves produces many distinct maxima,
each with many distinct representations of the same length. -/
theorem maximumFamilies_base {m Q : ℕ} {P Y : Finset ℕ} (h : IsPrefixFamily m Q P Y)
    (hm : 3 ≤ m) (hY : 2 ≤ Y.card) : HasMaximumFamilies (2*m-1) Q (Y.card/2-2*m) := by
  classical
  obtain ⟨cardP,hh⟩ := h
  choose! v prop using hh
  have fam : Family P Y v := by
    refine ⟨fun i hi => (prop i hi).1, fun i hi => (prop i hi).2.1, ?_⟩
    intro i hi
    have eq : P ∪ tails v i = insert i (insert (v i) P) := by
      ext x
      simp only [tails,mem_union,mem_insert,mem_singleton]
      tauto
    rw [eq]
    exact (prop i hi).2.2.1
  have pex : P.Nonempty := card_pos.mp (by omega)
  let u := P.max' pex
  have hu : u ∈ P := P.max'_mem _
  have huMax (p : ℕ) (hp : p ∈ P) : p ≤ u := P.le_max' p hp
  obtain ⟨j, hj⟩ := card_pos.mp (show 0<Y.card by omega)
  have huPos : 0<u := by have := ((fam.rep j hj).1 u (mem_union_left _ hu)).1; omega
  obtain ⟨L,H,hL,hH,cardL,cardH,sep⟩ := ordered_halves Y
  refine ⟨scaled u H, ?_, ?_⟩
  · rw [scaled_card huPos,cardH]; omega
  intro y hy
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hy
  refine ⟨dvd_mul_of_dvd_right (prop j (hH hj)).2.2.2 _, ?_⟩
  rw [← cardL]
  exact fam.one_fiber hL (hH hj) (fun i hi => sep i hi j hj) cardP hu huMax

end MaximumFiberCore
end OddEgyptian