/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Instances.ZMod
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.IsPrimePow
import FLT.Deformations.RepresentationTheory.GaloisRep

/-!

See
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/n-torsion.20or.20multiplication.20by.20n.20as.20an.20additive.20group.20hom/near/429096078

The main theorems in this file are part of the PhD thesis work of David Angdinata, one of KB's
PhD students. It would be great if anyone who is interested in working on these results
could talk to David first. Note that he has already made substantial progress.

-/

universe u

set_option maxHeartbeats 25600000

section group_theory_lemma_helpers

private lemma smul_natGcd_eq_zero' {A : Type*} [AddCommGroup A]
    (d n : ℕ) {x : A} (hd : (d : ℤ) • x = 0) (hn : (n : ℤ) • x = 0) :
    (Nat.gcd d n : ℤ) • x = 0 := by
  rw [show (Nat.gcd d n : ℤ) = ((d : ℤ).gcd (n : ℤ) : ℤ) from by simp [Int.gcd_natCast_natCast],
      Int.gcd_eq_gcd_ab (d : ℤ) (n : ℤ), add_smul, mul_comm (d : ℤ), mul_smul,
      mul_comm (n : ℤ), mul_smul, hd, hn, smul_zero, smul_zero, add_zero]

private theorem card_torsionBy_of_torsionBy' {A : Type*} [AddCommGroup A] (n d : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (Submodule.torsionBy ℤ A n) d) =
    Nat.card (Submodule.torsionBy ℤ A (Nat.gcd d n)) := by
  apply Nat.card_congr
  refine Equiv.ofBijective (fun x => ⟨x.1.1, ?_⟩) ⟨?_, ?_⟩
  · rw [Submodule.mem_torsionBy_iff]
    have hd : (d : ℤ) • (x.1 : A) = 0 := by
      have h := x.2; rw [Submodule.mem_torsionBy_iff] at h
      exact_mod_cast congr_arg Subtype.val h
    have hn : (n : ℤ) • (x.1 : A) = 0 := by
      have h := x.1.2; rw [Submodule.mem_torsionBy_iff] at h; exact h
    exact smul_natGcd_eq_zero' d n hd hn
  · intro x y heq; simp only [Subtype.mk.injEq] at heq; ext; exact heq
  · intro ⟨a, ha⟩
    rw [Submodule.mem_torsionBy_iff] at ha
    refine ⟨⟨⟨a, ?_⟩, ?_⟩, rfl⟩
    · rw [Submodule.mem_torsionBy_iff]
      have : (Nat.gcd d n : ℤ) ∣ n := by exact_mod_cast Nat.gcd_dvd_right d n
      obtain ⟨k, hk⟩ := this; rw [hk, mul_comm, mul_smul, ha, smul_zero]
    · rw [Submodule.mem_torsionBy_iff]
      change (d : ℤ) • (⟨a, _⟩ : Submodule.torsionBy ℤ A n) = 0; ext
      have : (Nat.gcd d n : ℤ) ∣ d := by exact_mod_cast Nat.gcd_dvd_left d n
      obtain ⟨k, hk⟩ := this; simp [hk, mul_comm, mul_smul, ha]

private def torsionBy_pi_equiv' {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    (R : Type*) [CommRing R] [∀ i, Module R (M i)] (a : R) :
    Submodule.torsionBy R (∀ i, M i) a ≃ ∀ i, Submodule.torsionBy R (M i) a where
  toFun x := fun i => ⟨(x.1 i), by
    rw [Submodule.mem_torsionBy_iff]
    have h := x.2; rw [Submodule.mem_torsionBy_iff] at h; exact congr_fun h i⟩
  invFun f := ⟨fun i => (f i).1, by
    rw [Submodule.mem_torsionBy_iff]; funext i
    have h := (f i).2; rw [Submodule.mem_torsionBy_iff] at h; simp [h]⟩
  left_inv x := by ext; rfl
  right_inv f := by ext; rfl

private theorem card_torsionBy_zmod_nat' (n d : ℕ) [NeZero n] :
    Nat.card (Submodule.torsionBy ℤ (ZMod n) (d : ℤ)) = Nat.gcd d n := by
  have h_eq : Nat.card (Submodule.torsionBy ℤ (ZMod n) (d : ℤ)) =
    Nat.card ((nsmulAddMonoidHom d : ZMod n →+ ZMod n).ker) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl _) (fun x => by
      simp [Submodule.mem_torsionBy_iff, AddMonoidHom.mem_ker, nsmulAddMonoidHom,
            Nat.cast_smul_eq_nsmul ℤ])
  rw [h_eq, IsAddCyclic.card_nsmulAddMonoidHom_ker, Nat.card_zmod, Nat.gcd_comm]

private lemma card_torsionBy_addEquiv' {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (d : ℕ) :
    Nat.card (Submodule.torsionBy ℤ A d) = Nat.card (Submodule.torsionBy ℤ B d) := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv e.toEquiv (fun a => ?_)
  simp only [Submodule.mem_torsionBy_iff, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv]
  constructor
  · intro ha
    rw [show (d : ℤ) • (e a) = e ((d : ℤ) • a) from (map_zsmul e (d : ℤ) a).symm, ha, map_zero]
  · intro hb
    have := congr_arg e.symm hb
    rw [show e.symm ((d : ℤ) • (e a)) = (d : ℤ) • a from by
      rw [(map_zsmul e.symm (d : ℤ) (e a)).symm.symm]; simp, map_zero] at this
    exact this

private theorem card_torsionBy_pi_zmod_general' {ι : Type*} [Fintype ι] (n : ι → ℕ)
    [∀ i, NeZero (n i)] (d : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (∀ i, ZMod (n i)) (d : ℤ)) =
      ∏ i : ι, Nat.gcd d (n i) := by
  rw [Nat.card_congr (torsionBy_pi_equiv' ℤ (d : ℤ)), Nat.card_pi]
  congr 1; ext i; exact card_torsionBy_zmod_nat' (n i) d

private theorem card_torsionBy_pi_zmod' (n r : ℕ) [NeZero n] (d : ℤ) :
    Nat.card (Submodule.torsionBy ℤ (Fin r → ZMod n) d) = (Int.gcd d n) ^ r := by
  have h_eq : Submodule.torsionBy ℤ (Fin r → ZMod n) d =
      Submodule.torsionBy ℤ (Fin r → ZMod n) (d.natAbs : ℤ) := by
    ext x; simp only [Submodule.mem_torsionBy_iff]
    rcases Int.natAbs_eq d with hd | hd <;>
    · constructor <;> intro h <;> (rw [hd] at * <;> simpa using h)
  rw [h_eq]
  have h2 : Nat.card (Submodule.torsionBy ℤ (Fin r → ZMod n) (d.natAbs : ℤ)) =
      (Nat.gcd d.natAbs n) ^ r := by
    rw [Nat.card_congr (torsionBy_pi_equiv' ℤ (d.natAbs : ℤ)), Nat.card_pi,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        card_torsionBy_zmod_nat' n d.natAbs]
  rw [h2]; simp [Int.gcd, Int.natAbs_natCast]

private lemma sum_min_succ' (u : Multiset ℕ) (k : ℕ) :
    (u.map (min (k + 1))).sum = (u.map (min k)).sum + (u.filter (k < ·)).card := by
  induction u using Multiset.induction with
  | empty => simp
  | cons a u ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.filter_cons, ih]
    by_cases ha : k < a
    · simp only [ha, ↓reduceIte, Multiset.card_add, Multiset.card_singleton,
                  show min (k + 1) a = k + 1 from by omega,
                  show min k a = k from by omega]; omega
    · simp only [ha, ↓reduceIte, zero_add,
                  show min (k + 1) a = a from by omega,
                  show min k a = a from by omega]; omega

private lemma gcd_prime_pow_eq' {p k n : ℕ} (hp : Nat.Prime p) (hn : n ≠ 0) :
    Nat.gcd (p ^ k) n = p ^ min k (n.factorization p) := by
  apply Nat.eq_of_factorization_eq (Nat.gcd_pos_of_pos_left _ (pow_pos hp.pos k)).ne'
    (pow_ne_zero _ hp.ne_zero)
  intro q
  rw [Nat.factorization_gcd (pow_ne_zero k hp.ne_zero) hn, Finsupp.inf_apply,
      hp.factorization_pow, hp.factorization_pow]
  by_cases hqp : q = p <;> simp [Finsupp.single_apply, hqp]

private lemma prod_map_gcd_prime_pow' {p k : ℕ} (hp : Nat.Prime p) {s : Multiset ℕ}
    (hs : ∀ x ∈ s, x ≠ 0) :
    (s.map (Nat.gcd (p ^ k))).prod = p ^ (s.map (fun n => min k (n.factorization p))).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    rw [ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx)), pow_add,
        gcd_prime_pow_eq' hp (hs a (Multiset.mem_cons_self a s))]

private lemma prime_pow_factorization_iff' {n p : ℕ} {e : ℕ} (hn : IsPrimePow n)
    (hp : Nat.Prime p) (he : 0 < e) :
    n.factorization p = e ↔ n = p ^ e := by
  constructor
  · intro hvp
    obtain ⟨r, k, hr, hk, rfl⟩ := hn
    have hrp : r = p := by
      by_contra h
      have : (r ^ k).factorization p = 0 := by
        rw [(Nat.prime_iff.mpr hr).factorization_pow]; simp [Finsupp.single_apply, h]
      omega
    subst hrp; congr 1
    rwa [(Nat.prime_iff.mpr hr).factorization_pow, Finsupp.single_apply, if_pos rfl] at hvp
  · intro h; subst h; simp [hp.factorization_pow, Finsupp.single_apply]

private theorem multiset_eq_of_prod_gcd_eq' {s t : Multiset ℕ}
    (hs : ∀ x ∈ s, IsPrimePow x) (ht : ∀ x ∈ t, IsPrimePow x)
    (h : ∀ d : ℕ, (s.map (Nat.gcd d)).prod = (t.map (Nat.gcd d)).prod) :
    s = t := by
  have hs0 : ∀ x ∈ s, x ≠ 0 := fun x hx => (hs x hx).ne_zero
  have ht0 : ∀ x ∈ t, x ≠ 0 := fun x hx => (ht x hx).ne_zero
  have h_sum : ∀ (p : ℕ) (_ : Nat.Prime p) (j : ℕ),
      (s.map (fun n => min j (n.factorization p))).sum =
      (t.map (fun n => min j (n.factorization p))).sum := by
    intro p hp j
    have hj := h (p ^ j)
    rw [prod_map_gcd_prime_pow' hp hs0, prod_map_gcd_prime_pow' hp ht0] at hj
    exact Nat.pow_right_injective hp.two_le hj
  have filter_vp : ∀ (p : ℕ) (_ : Nat.Prime p) (k : ℕ),
      (s.filter (fun n => k < n.factorization p)).card =
      (t.filter (fun n => k < n.factorization p)).card := by
    intro p hp k
    have hs_d := sum_min_succ' (s.map (fun n => n.factorization p)) k
    have ht_d := sum_min_succ' (t.map (fun n => n.factorization p)) k
    simp only [Multiset.map_map, Function.comp, Multiset.filter_map, Multiset.card_map] at hs_d ht_d
    have hk := h_sum p hp k
    have hk1 := h_sum p hp (k + 1)
    omega
  ext a
  by_cases ha_pp : IsPrimePow a
  · obtain ⟨p, e, hp, he, rfl⟩ := ha_pp
    have hpn : Nat.Prime p := Nat.prime_iff.mpr hp
    suffices key : ∀ (u : Multiset ℕ), (∀ x ∈ u, IsPrimePow x) →
        u.count (p ^ e) = (u.filter (fun n => e ≤ n.factorization p)).card -
        (u.filter (fun n => e < n.factorization p)).card by
      rw [key s hs, key t ht]
      rcases e with _ | e; · omega
      · have h1 := filter_vp p hpn e
        have h2 := filter_vp p hpn (e + 1)
        simp only [Nat.lt_iff_add_one_le, Nat.succ_eq_add_one] at h1 h2 ⊢
        omega
    intro u hu
    have h1 : u.count (p ^ e) = (u.filter (· = p ^ e)).card := by
      rw [Multiset.count_eq_card_filter_eq]; congr 1; ext x
      simp only [Multiset.count_filter]; congr 1; exact propext eq_comm
    have h2 : (u.filter (· = p ^ e)).card =
        (u.filter (fun n => n.factorization p = e)).card := by
      congr 1; ext x; simp only [Multiset.count_filter]
      by_cases hx : x ∈ u
      · simp only [prime_pow_factorization_iff' (hu x hx) hpn he]
      · simp [Multiset.count_eq_zero.mpr hx]
    have h3 : (u.filter (fun n => n.factorization p = e)).card =
        (u.filter (fun n => e ≤ n.factorization p)).card -
        (u.filter (fun n => e < n.factorization p)).card := by
      have split_eq : (u.filter (fun n => e ≤ n.factorization p)).card =
          (u.filter (fun n => n.factorization p = e)).card +
          (u.filter (fun n => e < n.factorization p)).card := by
        rw [← Multiset.card_add]; congr 1; ext x
        simp only [Multiset.count_filter, Multiset.count_add]
        split_ifs with h1 h2 h3 <;> omega
      omega
    omega
  · have hcs : Multiset.count a s = 0 :=
      Multiset.count_eq_zero.mpr (fun hm => ha_pp (hs a hm))
    have hct : Multiset.count a t = 0 :=
      Multiset.count_eq_zero.mpr (fun hm => ha_pp (ht a hm))
    rw [hcs, hct]

private lemma equiv_of_multiset_map_eq' {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ}
    (h : Finset.univ.val.map n₁ = Finset.univ.val.map n₂) :
    ∃ (e : ι₁ ≃ ι₂), ∀ i, n₁ i = n₂ (e i) := by
  classical
  have h_fiber : ∀ c : ℕ, Nonempty ({i : ι₁ // n₁ i = c} ≃ {j : ι₂ // n₂ j = c}) := by
    intro c; apply Fintype.card_eq.mp
    rw [Fintype.card_subtype, Fintype.card_subtype]
    have hc : Multiset.count c (Finset.univ.val.map n₁) =
        Multiset.count c (Finset.univ.val.map n₂) := congr_arg _ h
    simp only [Multiset.count_map] at hc
    have conv₁ : Multiset.card (Multiset.filter (fun a => c = n₁ a) Finset.univ.val) =
        (Finset.univ.filter (fun a => n₁ a = c)).card := by
      rw [← Finset.filter_val]; congr 1; ext x; simp [eq_comm]
    have conv₂ : Multiset.card (Multiset.filter (fun a => c = n₂ a) Finset.univ.val) =
        (Finset.univ.filter (fun a => n₂ a = c)).card := by
      rw [← Finset.filter_val]; congr 1; ext x; simp [eq_comm]
    rw [conv₁, conv₂] at hc; exact hc
  exact ⟨Equiv.ofFiberEquiv (fun c => (h_fiber c).some),
    fun i => (Equiv.ofFiberEquiv_map _ i).symm⟩

private noncomputable def piFilterAddEquiv'
    {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → ℕ) (e : ι → ℕ) :
    (∀ i, ZMod (p i ^ e i)) ≃+ (∀ j : {i // e i ≠ 0}, ZMod (p j ^ e j)) := by
  have hK : ∀ k : {i // ¬(e i ≠ 0)}, Subsingleton (ZMod (p ↑k ^ e ↑k)) := by
    intro ⟨k, hk⟩; simp only [not_not] at hk; rw [hk, pow_zero]; infer_instance
  haveI : Unique (∀ k : {i // ¬(e i ≠ 0)}, ZMod (p ↑k ^ e ↑k)) :=
    ⟨⟨fun _ => 0⟩, fun f => funext fun k => (hK k).elim (f k) 0⟩
  exact {
    toFun := fun f j => f j
    invFun := fun g i => if h : e i ≠ 0 then g ⟨i, h⟩
      else by rw [show e i = 0 from not_not.mp h, pow_zero]; exact 0
    left_inv := fun f => funext fun i => by
      by_cases he : e i ≠ 0 <;> simp [he]
      exact ((hK ⟨i, he⟩).elim _ _)
    right_inv := fun g => funext fun ⟨j, hj⟩ => by simp [hj]
    map_add' := fun _ _ => funext fun _ => rfl
  }

private theorem addEquiv_of_torsionBy_card_eq' {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Finite G] [Finite H]
    (h : ∀ d : ℕ, Nat.card (Submodule.torsionBy ℤ G d) =
      Nat.card (Submodule.torsionBy ℤ H d)) :
    Nonempty (G ≃+ H) := by
  classical
  obtain ⟨ι₁, hι₁, p₁, hp₁, e₁, ⟨φ₁⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite G
  obtain ⟨ι₂, hι₂, p₂, hp₂, e₂, ⟨φ₂⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite H
  let ψ₁ := φ₁.trans (DirectSum.addEquivProd (fun i => ZMod (p₁ i ^ e₁ i)))
  let ψ₂ := φ₂.trans (DirectSum.addEquivProd (fun i => ZMod (p₂ i ^ e₂ i)))
  set J₁ := {i : ι₁ // e₁ i ≠ 0}
  set J₂ := {i : ι₂ // e₂ i ≠ 0}
  let n₁ : J₁ → ℕ := fun j => p₁ j ^ e₁ j
  let n₂ : J₂ → ℕ := fun j => p₂ j ^ e₂ j
  haveI : ∀ j : J₁, NeZero (n₁ j) := fun ⟨j, _⟩ => ⟨pow_ne_zero _ (hp₁ j).ne_zero⟩
  haveI : ∀ j : J₂, NeZero (n₂ j) := fun ⟨j, _⟩ => ⟨pow_ne_zero _ (hp₂ j).ne_zero⟩
  have hn₁_pp : ∀ j : J₁, IsPrimePow (n₁ j) := fun ⟨j, hj⟩ =>
    ⟨p₁ j, e₁ j, (hp₁ j).prime, Nat.pos_of_ne_zero hj, rfl⟩
  have hn₂_pp : ∀ j : J₂, IsPrimePow (n₂ j) := fun ⟨j, hj⟩ =>
    ⟨p₂ j, e₂ j, (hp₂ j).prime, Nat.pos_of_ne_zero hj, rfl⟩
  let χ₁ := ψ₁.trans (piFilterAddEquiv' p₁ e₁)
  let χ₂ := ψ₂.trans (piFilterAddEquiv' p₂ e₂)
  have h_prod : ∀ d : ℕ, ∏ j : J₁, Nat.gcd d (n₁ j) = ∏ j : J₂, Nat.gcd d (n₂ j) := by
    intro d
    rw [← card_torsionBy_pi_zmod_general' n₁ d,
        ← card_torsionBy_addEquiv' χ₁ d,
        h d,
        card_torsionBy_addEquiv' χ₂ d,
        card_torsionBy_pi_zmod_general' n₂ d]
  have h_multi : Finset.univ.val.map n₁ = Finset.univ.val.map n₂ := by
    apply multiset_eq_of_prod_gcd_eq'
    · intro x hx; obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx; exact hn₁_pp i
    · intro x hx; obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx; exact hn₂_pp i
    · intro d; simp only [Multiset.map_map, Function.comp]
      rw [← Finset.prod_eq_multiset_prod, ← Finset.prod_eq_multiset_prod]; exact h_prod d
  obtain ⟨σ, hσ⟩ := equiv_of_multiset_map_eq' h_multi
  let π : (∀ j : J₁, ZMod (n₁ j)) ≃+ (∀ j : J₂, ZMod (n₂ j)) :=
    (AddEquiv.piCongrRight fun j => (ZMod.ringEquivCongr (hσ j)).toAddEquiv).trans
      (RingEquiv.piCongrLeft (fun j => ZMod (n₂ j)) σ).toAddEquiv
  exact ⟨χ₁.trans (π.trans χ₂.symm)⟩

end group_theory_lemma_helpers

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]

open WeierstrassCurve WeierstrassCurve.Affine

abbrev WeierstrassCurve.n_torsion (n : ℕ) : Type u := Submodule.torsionBy ℤ (E ⟮k⟯) n

--variable (n : ℕ) in
--#synth AddCommGroup (E.n_torsion n)

-- not sure if this instance will cause more trouble than it's worth
noncomputable instance (n : ℕ) : Module (ZMod n) (E.n_torsion n) :=
  AddCommGroup.zmodModule <| by
  intro ⟨P, hP⟩
  simpa using hP

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
theorem WeierstrassCurve.n_torsion_finite {n : ℕ} (hn : 0 < n) : Finite (E.n_torsion n) := sorry

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.n_torsion n) = n^2 := sorry

theorem group_theory_lemma {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n) (r : ℕ)
    (h : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → (ZMod n))) := by
  have hfin : Finite (Submodule.torsionBy ℤ A n) :=
    Nat.finite_of_card_ne_zero (by rw [h n dvd_rfl]; exact pow_ne_zero _ hn.ne')
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : Finite (Fin r → ZMod n) := Pi.finite
  apply addEquiv_of_torsionBy_card_eq'
  intro d
  rw [card_torsionBy_of_torsionBy', card_torsionBy_pi_zmod', Int.gcd_natCast_natCast]
  exact h _ (Nat.gcd_dvd_right d n)

-- I only need this if n is prime but there's no harm thinking about it in general I guess.
-- It follows from the previous theorem using pure group theory (possibly including the
-- structure theorem for finite abelian groups)
theorem WeierstrassCurve.n_torsion_dimension [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (E.n_torsion n ≃+ (ZMod n) × (ZMod n)) := by
  obtain ⟨φ⟩ : Nonempty (E.n_torsion n ≃+ (Fin 2 → (ZMod n))) := by
    apply group_theory_lemma (Nat.pos_of_ne_zero fun h ↦ by simp [h] at hn)
    intro d hd
    apply E.n_torsion_card
    contrapose! hn
    rcases hd with ⟨c, rfl⟩
    simp [hn]
  exact ⟨φ.trans (RingEquiv.piFinTwo _).toAddEquiv⟩

-- follows easily from the above
noncomputable instance (n : ℕ) : Module.Finite (ZMod n) (E.n_torsion n) := sorry

-- This should be a straightforward but perhaps long unravelling of the definition
/-- The map on points for an elliptic curve over `k` induced by a morphism of `k`-algebras
is a group homomorphism. -/
noncomputable def WeierstrassCurve.Points.map {K L : Type u} [Field K] [Field L] [Algebra k K]
    [Algebra k L] [DecidableEq K] [DecidableEq L]
    (f : K →ₐ[k] L) : E ⟮K⟯ →+ E ⟮L⟯ := WeierstrassCurve.Affine.Point.map f

omit [E.IsElliptic] [DecidableEq k] in
lemma WeierstrassCurve.Points.map_id (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    WeierstrassCurve.Points.map E (AlgHom.id k K) = AddMonoidHom.id _ := by
      ext
      exact WeierstrassCurve.Affine.Point.map_id _

omit [E.IsElliptic] [DecidableEq k] in
lemma WeierstrassCurve.Points.map_comp (K L M : Type u) [Field K] [Field L] [Field M]
    [DecidableEq K] [DecidableEq L] [DecidableEq M] [Algebra k K] [Algebra k L] [Algebra k M]
    (f : K →ₐ[k] L) (g : L →ₐ[k] M) :
    (WeierstrassCurve.Affine.Point.map g).comp (WeierstrassCurve.Affine.Point.map f) =
    WeierstrassCurve.Affine.Point.map (W' := E) (g.comp f) := by
  ext P
  exact WeierstrassCurve.Affine.Point.map_map _ _ _

/-- The Galois action on the points of an elliptic curve. -/
noncomputable instance WeierstrassCurve.galoisRepresentation_smul
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    SMul (K ≃ₐ[k] K) (E ⟮K⟯) := ⟨
  fun g P ↦ WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K) P⟩

/-- The Galois action on the points of an elliptic curve. -/
noncomputable def WeierstrassCurve.galoisRepresentation
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    DistribMulAction (K ≃ₐ[k] K) (E ⟮K⟯) where
      one_smul P := by cases P <;> rfl
      mul_smul g h P := by cases P <;> rfl
      smul_zero g := map_zero _
      smul_add g P Q := map_add _ P Q

-- the next `sorry` is data but the only thing which should be missing is
-- the continuity argument, which follows from the finiteness asserted above.

/-- The continuous Galois representation associated to an elliptic curve over a field. -/
def WeierstrassCurve.galoisRep {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    [DecidableEq K] [DecidableEq (AlgebraicClosure K)] (n : ℕ) (hn : 0 < n) :
  GaloisRep K (ZMod n) ((E.map (algebraMap K (AlgebraicClosure K))).n_torsion n) := sorry
