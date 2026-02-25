(* ================================================================== *)
(* Leonardo's Prime Factors — Rocq Formalization                       *)
(* ================================================================== *)
(*                                                                      *)
(* Problem: given n, find the maximum number of distinct prime factors  *)
(* any integer in [1..n] can have.                                      *)
(*                                                                      *)
(* This file provides a complete formal proof that `max_distinct_prime_ *)
(* factors n` computes the correct answer. The proof has two parts:     *)
(*                                                                      *)
(*   Soundness  (max_distinct_sound):                                   *)
(*     There exists an m <= n whose distinct prime factor count equals  *)
(*     the returned value.  Witness: the k-th primorial accumulated     *)
(*     inside max_distinct_aux.                                         *)
(*                                                                      *)
(*   Maximality (max_distinct_maximal):                                 *)
(*     No m <= n can have more distinct prime factors than the answer.  *)
(*     Key lemma: the product of any k distinct primes divides m, so   *)
(*     the *smallest* such product (the primorial of the first k        *)
(*     primes) must also be <= n.  If max_distinct_aux stopped before   *)
(*     counting k, that primorial exceeded n — contradiction.           *)
(*                                                                      *)
(* High-level proof structure                                           *)
(* ─────────────────────────────────────────────────────────────────── *)
(*  1. Define `prime`, `divides`, `product`, `all_primes`.              *)
(*  2. Axiomatise the Fundamental Theorem of Arithmetic (existence and  *)
(*     uniqueness up to permutation).  Proving FTA in Rocq is          *)
(*     substantial; axiomatising it keeps the file focused.            *)
(*  3. Build `largest_divisor` (trial division, downward search) and    *)
(*     prove it is maximal among proper divisors.                       *)
(*  4. Define `primefactors` via Program Fixpoint (measure = n), prove  *)
(*     correctness (product = n, all elements prime) and that the list  *)
(*     is sorted in ascending order.                                    *)
(*  5. Define `dedup` on sorted lists; prove it yields NoDup + sorted.  *)
(*  6. Define `distinct_primefactors = dedup ∘ primefactors`.           *)
(*  7. Define `max_distinct_aux` with a fuel argument for termination.  *)
(*  8. Prove soundness via an explicit invariant on the accumulator.    *)
(*  9. Prove maximality via the coprimality + divisibility argument     *)
(*     (`nodup_primes_product_divides`).                                *)
(*                                                                      *)
(* Correspondence with the C++ solution                                 *)
(* ─────────────────────────────────────────────────────────────────── *)
(*  C++ TrialDivision::primeCount   ↔  max_distinct_aux / max_distinct_ *)
(*                                      prime_factors                   *)
(*  C++ TrialDivision::nextPrime    ↔  is_prime / has_divisor (the     *)
(*                                      primality test used inside      *)
(*                                      max_distinct_aux)               *)
(*  C++ `product > n / p`           ↔  `product * candidate <=? n`     *)
(*                                      (same overflow-safe comparison) *)
(*  C++ greedy primorial loop       ↔  max_distinct_aux_counts_ge       *)
(*                                      (the maximality direction)      *)
(* ================================================================== *)

Require Import Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import List.
Require Import Coq.Sorting.Permutation.

Require Import Classical.

Require Import Coq.Program.Wf.
Require Import Coq.Program.Equality.

Require Import Coq.Init.Wf.
Require Import Coq.Arith.Wf_nat.

Require Import Coq.Sorting.Sorted.

Import ListNotations.

(* ================================================================== *)
(* Basic Definitions                                                    *)
(* ================================================================== *)

Definition divides (a b : nat) : Prop :=
  exists k : nat, a * k = b.
Infix "|'" := divides (at level 70).

Definition prime (n : nat) : Prop :=
  n > 1 /\ forall k : nat, k |' n -> k = 1 \/ k = n.

Definition all_primes (elements : list nat) : Prop :=
  Forall prime elements.

Fixpoint product (elements : list nat) : nat :=
  match elements with
  | [] => 1
  | x :: xs => x * (product xs)
  end.

(* ================================================================== *)
(* Basic Lemmas                                                         *)
(* ================================================================== *)

Lemma product_nil : product [] = 1.
Proof.
  reflexivity.
Qed.

Lemma product_of_singleton :
  forall l x, l = [x] ->
         product l = x.
Proof.
  intros l n Hsingleton.
  rewrite Hsingleton.
  unfold product.
  ring.
Qed.

Lemma in_list_divides_product :
  forall l x, In x l -> x |' product l.
Proof.
  induction l as [| h t IH]; intros x Hin; [inversion Hin |].
  destruct Hin as [-> | Hin].
  - exists (product t). reflexivity.
  - destruct (IH x Hin) as [k Hk].
    exists (h * k). simpl. lia.
Qed.

Lemma product_app :
  forall a l,
    product ([a] ++ l) = a * product l.
Proof.
  intros a l.
  induction l; reflexivity.
Qed.

Lemma product_app_reverse :
  forall a l,
    product (l ++ [a]) = (product l) * a.
Proof.
  intros a l.
  induction l; simpl; [lia | rewrite IHl; lia].
Qed.

Lemma product_ge_1 : 
  forall l, all_primes l -> (product l) >= 1.
Proof.
  intros l.
  induction l; simpl; [lia|].
  intros Hallprimes.
  
  inversion Hallprimes.
  inversion H1.
  assert (product l >= 1).
  {
    apply IHl.
    assumption.
  }
  lia.
Qed.

Lemma product_gt_1 :
  forall l,
    all_primes l -> l <> [] -> (product l) > 1.
Proof.
  intros l Hallprimes Hnonempty.
  induction l as [| x xs].
  - contradiction.
  - simpl.
    inversion Hallprimes as [|? ? Hprime Hforall]; subst.
    destruct Hprime as [Hgt1 _].
    
    assert (product xs >= 1).
    {
      apply product_ge_1.
      inversion Hallprimes.
      assumption.
    }
    lia.
Qed.      

(* ================================================================== *)
(* Basic Examples                                                       *)
(* ================================================================== *)

Example prime_2 : prime 2.
Proof.
  unfold prime. split; [lia |].
  intros k [m Hm].
  destruct k as [| k']; [discriminate |].
  destruct m as [| m']; lia.
Qed.

Example not_prime_4 : ~(prime 4).
Proof.
  unfold prime.
  intros [_ Hcontradiction].
  specialize (Hcontradiction 2).
  destruct Hcontradiction; try discriminate.
  exists 2. reflexivity.
Qed.

(* ================================================================== *)
(* Fundamental Theorem of Arithmetic (Assumed)                         *)
(* ================================================================== *)

(* Existence: every n > 1 factors into primes.                        *)
Axiom FTA_existence :
  forall n, 1 < n ->
    exists l, all_primes l /\ product l = n.

(* Uniqueness: the factorisation is unique up to permutation.         *)
(* Only used in primefactors_product_id to identify two sorted factor  *)
(* lists that share the same product.                                  *)
Axiom FTA_uniqueness :
  forall n l1 l2,
    1 < n ->
    all_primes l1 -> all_primes l2 ->
    product l1 = n -> product l2 = n ->
    Permutation l1 l2.

(* ================================================================== *)
(* Largest Divisor                                                      *)
(* ================================================================== *)

(* ld_aux n i: searches downward from i for the largest proper         *)
(* divisor of n, i.e. the largest d with d | n and d < n.             *)
(* Returns 1 if n is prime (no proper divisor > 1 exists).            *)
Fixpoint ld_aux (n i : nat) : nat :=
  match i with
  | 0 => 1
  | S i' =>
      if (n mod (S i') =? 0) then S i' else ld_aux n i'
  end.

Definition largest_divisor (n : nat) : nat :=
  match n with
  | 0 | 1 => 1
  | S n'  => ld_aux (S n') n'
  end.

(* ================================================================== *)
(* Largest Divisor Lemmas                                               *)
(* ================================================================== *)

Lemma ld_aux_le :
  forall n i, ld_aux n i <= S i.
Proof.
  intros n i.
  induction i as [| i' IH]; [simpl; lia |].
  unfold ld_aux at 1.
  destruct (n mod (S i') =? 0); [lia |].
  transitivity (S i'); [apply IH | lia].
Qed.

Lemma ld_aux_le_i :
  forall n i, ld_aux n i <= i \/ ld_aux n i = 1.
Proof.
  intros n i.
  induction i as [| i IH]; [simpl; right; reflexivity |].
  unfold ld_aux at 1.
  destruct (n mod (S i) =? 0).
  - left; lia.
  - left; apply ld_aux_le.
Qed.

Lemma largest_divisor_lt :
  forall n, 2 <= n -> largest_divisor n <= n - 1.
Proof.
  intros n H.
  unfold largest_divisor.
  destruct n as [| [| n'']]; [lia | lia |].
  destruct (ld_aux_le_i (S (S n'')) (S n'')); [assumption | lia].
Qed.

Lemma largest_divisor_strict :
  forall n,
    2 <= n ->
    largest_divisor n < n.
Proof.
  intros n H.
  pose proof (largest_divisor_lt n H) as Hle.
  lia.
Qed.

Lemma ld_aux_gt1 : forall n i, ld_aux n i >= 1.
Proof.
  intros n i.
  induction i.
  - simpl. lia.
  - unfold ld_aux.
    destruct (n mod S i =? 0) eqn:EQ; [lia|].
    fold ld_aux.
    assumption.
Qed.

Lemma largest_divisor_ge1 :
  forall n, 2 <= n -> largest_divisor n >= 1.
Proof.
  intros n H.
  unfold largest_divisor.
  destruct n as [| [| n']]; [lia | lia |].
  apply ld_aux_gt1.
Qed.

Lemma ld_aux_of_prime_is_1 :
  forall n i,
    prime n ->
    i < n ->
    ld_aux n i = 1.
Proof.
  intros n i Hprime.
  induction i as [| i' IHi']; intro Hi_lt.
  - simpl. reflexivity.
  - unfold ld_aux at 1.
    destruct (n mod (S i') =? 0) eqn:Hmod.
    + apply Nat.eqb_eq in Hmod.
      (* If n mod (S i') = 0 then (S i') divides n. For prime n, that
         forces S i' = 1 or S i' = n; but S i' < n, so S i' = 1. *)
      assert (Hdiv : (S i') |' n).
      {
        apply Nat.mod_divides in Hmod; [| lia].
        destruct Hmod as [k Hk].
        exists k. exact (eq_sym Hk).
      }
      destruct Hprime as [_ Hprime_div].
      specialize (Hprime_div (S i') Hdiv) as [Hd1 | HdN].
      * rewrite Hd1. reflexivity.
      * exfalso. lia.
    + apply IHi'. lia.
Qed.

Lemma largest_divisor_of_prime_is_1 :
  forall n, 2 <= n -> (prime n) -> largest_divisor n = 1.
Proof.
  intros n Hgt2 Hprime.
  destruct n as [| [| n']]; [lia | lia |].
  cbn [largest_divisor].
  apply ld_aux_of_prime_is_1; [exact Hprime | lia].
Qed.

(* Key property: largest_divisor actually divides n *)
Lemma ld_aux_divides :
  forall n i, ld_aux n i <> 0 /\ ld_aux n i |' n.
Proof.
  intros n i.
  induction i as [|i' IH].
  - cbn. 
    split; [discriminate | exists n; ring].
  - destruct (n mod S i' =? 0) eqn:H.
    + split.
      * cbn in *. rewrite H.
        discriminate.
      * unfold ld_aux.
        rewrite H.
        apply Nat.eqb_eq in H.
        exists (n / (S i')).
        apply Nat.div_exact in H; [lia | auto].
    + split.
      all: cbn in *; rewrite H; apply IH.
Qed.

Lemma largest_divisor_divides :
  forall n, 2 <= n ->
    let d := largest_divisor n in
    d <> 0 /\ d |' n.
Proof.
  intros n H d.
  unfold d, largest_divisor.
  destruct n as [| [| n'']]; [lia | lia |].
  apply ld_aux_divides.
Qed.

Lemma ld_aux_max_gen :
  forall n i k,
    1 <= k ->
    k <= i ->
    k |' n ->
    k <= ld_aux n i.
Proof.
  intros n i.
  induction i as [| i' IH]; intros k HkGt1 HkleSi Hdivides.
  - lia.
  - destruct (n mod S i' =? 0) eqn:Hmod.
    + cbn in *. rewrite Hmod.
      exact HkleSi.
    + cbn in *. rewrite Hmod.
      apply Nat.eqb_neq in Hmod.
      (* k cannot equal S i', since k |' n but S i' ∤ n *)
      assert (Hk_ne : k <> S i').
      { 
        intro Heq. subst.
        destruct Hdivides as [m Hm].
        apply Hmod.
        apply (Nat.mod_divides n (S i')); [lia |].
        exists m. lia. 
      }
      
      (* So k <= i', apply IH *)
      apply IH; [lia | lia | exact Hdivides].
Qed.

Lemma ld_aux_max :
  forall i k,
    let n := S (S i) in
      k <= n ->
      k |' n ->
      k <> n ->
      k <= ld_aux n i.
Proof.
  intros i k n Hle Hdivides Hneq.
  (* k >= 1: a divisor of n >= 2 must be positive *)
  assert (Hk1 : 1 <= k).
  { 
    destruct Hdivides as [m Hm].
    destruct k; simpl in Hm; [unfold n in Hm; lia | lia]. 
  }
  (* k < n = S (S i), so k <= S i *)
  assert (HkSi : k <= S i) by (unfold n in *; lia).
  destruct i as [| i'].
  - (* i = 0: n = 2, so k <= 1 and k >= 1, meaning k = 1 *)
    simpl. exact HkSi.
  - (* i = S i': k <= S(S i') and k <> S(S i'), so k <= S i' *)
    assert (HneqSSi : k <> S (S i')).
    {
      intro Heq.
      subst.
      destruct Hdivides as [m Hm].
      (*
        m = 0: gives 0 = n, contradicting n >= 2
        m = 1: gives S(S i') = n = S(S i'), fine — but then k = n, contradicted
        m >= 2: product would exceed n
      *)
      destruct m as [| [| m'']]; lia.
    }
    
    assert (Hki : k <= S i') by (unfold n in *; lia).
    apply ld_aux_max_gen; assumption.
Qed.

Remark factor_le :
  forall k t n : nat,
    k * t = S n ->
    k <= S n.
Proof.
  intros k t n H.
  destruct t.
  - lia.                            
  - apply Nat.le_trans with (m := k + k * t).
    + apply Nat.le_add_r.
    + lia.
Qed.


Lemma largest_divisor_maximal :
  forall n k,
    2 <= n ->
    k |' n ->
    k <> n ->
    k <= largest_divisor n.
Proof.
  intros n k H_le2 Hdivides Hneq.
  unfold largest_divisor.
  destruct n as [| [| n']]; try lia.
  apply ld_aux_max_gen.
  - destruct Hdivides as [t Ht].
    destruct k; lia.
  - destruct Hdivides as [m Hm].
    apply factor_le in Hm.
    lia.
  - exact Hdivides.
Qed.

Lemma largest_divisor_of_composite_ge_2 :
  forall n, 2 <= n -> ~(prime n) -> largest_divisor n >= 2.
Proof.
  intros n Hgt2 Hcomposite.
  assert (Hgt1: 1 < n) by lia.

  destruct (FTA_existence n Hgt1) as [factors [Hallprimes Heq]].
  destruct factors as [| p [|q l]].
  - simpl in Heq. lia.
  - simpl in Heq. subst n.
    exfalso. apply Hcomposite.
    replace (p * 1) with (p) by lia.
    exact (Forall_inv Hallprimes).
  - inversion Hallprimes as [| ? ? Hp_prime Hrest_primes].
    assert (Hp_ge2: 2 <= p) by (destruct Hp_prime; lia).

    assert (Hp_div_n: p |' n).
    {
      exists (product (q :: l)).
      simpl in *. assumption. 
    }

    assert (Hrest_nonempty: (q :: l) <> []) by (discriminate).
    assert (Hrest_gt1: product (q :: l) > 1) by (apply product_gt_1; assumption).
    
    assert (Hp_ne_n: p <> n).
    {
      intros HPeqN.
      assert (p <> 0) by lia.

      assert (Hrest_eq1: product (q :: l) = 1).
      {
        replace (product (p :: q :: l)) with (p * product (q :: l)) in Heq.
        - rewrite HPeqN in Heq.
          apply Nat.mul_id_r in Heq.
          + assumption.
          + rewrite HPeqN in H1; assumption.
        - reflexivity. 
      }
      lia.
    }
    
    destruct n as [| [| n]]; try lia.
    unfold largest_divisor.
    assert (Hld_ge2 : 2 <= ld_aux (S (S n)) (S n)).
    {
      eapply Nat.le_trans; [exact Hp_ge2|].
      apply ld_aux_max_gen; [lia| |].
      - assert (Hmul_lt: p * 1 < p * product (q :: l)) by (apply Nat.mul_lt_mono_pos_l; lia).
        replace (product (p :: q :: l)) with (p * product (q :: l)) in Heq.
        + rewrite Heq in Hmul_lt.
          lia.
        + reflexivity.
      - assumption.  
    }
    lia.
Qed.

(* ================================================================== *)
(* Prime Factorisation                                                  *)
(* ================================================================== *)

(* If d = largest_divisor N, then p = N/d is prime.                   *)
(* Argument: d is the largest proper divisor of N, so p = N/d has no  *)
(* proper divisor except 1 (any proper divisor of p would combine with *)
(* d to give a larger proper divisor of N, contradicting maximality).  *)
Theorem quotient_prime :
  forall N,
    2 <= N ->
    let d := largest_divisor N in
    let p := N / d in
    prime p.
Proof.
  intros N HN d p.
  
  assert (D := largest_divisor_divides N HN).
  destruct D as [Hd_ne0 [k Hdk]].
  assert (Hd_lt : d < N) by (apply largest_divisor_strict; assumption).
  assert (Hd_pos : 0 < d) by lia.
  assert (Hk_pos : 0 < k) by (destruct k; lia).
  assert (Hk_ge2 : 2 <= k) by (destruct k as [|[|]]; lia).
  
  assert (Hpk : p = k).
  {
    unfold p.
    rewrite <- Hdk, Nat.mul_comm.
    apply Nat.div_mul.
    apply Hd_ne0.
  }
  
  unfold prime. split; [lia|].
  intros q [m Hqm].
  rewrite Hpk in Hqm.
  
  assert (Hq_pos : 0 < q) by (destruct q; lia).
  assert (Hqd_div : (q * d) |' N) by (exists m; nia).
  
  assert (Hqd_le_N : q * d <= N).
  {
    destruct Hqd_div as [m' Hm'].
    destruct m'; nia.
  }
  
  destruct (Nat.eq_dec (q * d) N) as [Heq | Hne].
  - right. nia.
  - left.
    assert (Hqd_le_d : q * d <= d).
    { 
      apply largest_divisor_maximal; [assumption | exact Hqd_div | lia]. 
    }
    nia.
Qed.

(* Returns prime factors of n in ascending order, with repetition.    *)
(* e.g. primefactors 12 = [2; 2; 3]                                   *)
(* Note: does NOT deduplicate — see distinct_primefactors below.       *)
(* Termination: each recursive call is on largest_divisor n < n.      *)
Program Fixpoint primefactors (n : nat) {measure n} : list nat :=
  match n with
  | 0 | 1 => []
  | _     =>
      let d := largest_divisor n in
      let p := n / d in
      p :: primefactors d
  end.
Next Obligation.
  pose proof (largest_divisor_lt n) as Hlt.
  lia.
Qed.

Lemma primefactors_unfold :
  forall n,
    n > 1 ->
    primefactors n =
      let d := largest_divisor n in
      let p := n / d in
      p :: primefactors d.
Proof.
  intros n Hn.
  unfold primefactors at 1.
  rewrite fix_sub_eq.
  - simpl.
    destruct n as [| [| n']].
    + inversion Hn.
    + lia.
    + reflexivity.
  - intros x f g Hext.
    destruct x as [| [| x']]; try reflexivity.
    simpl.
    f_equal.
    apply Hext.
Qed.

Lemma primefactors_of_prime :
  forall n, prime n -> primefactors n = [n].
Proof.
  intros n Hprime.
  assert (Hgt1: n > 1) by (destruct Hprime; lia).
  rewrite primefactors_unfold.
  - pose proof (largest_divisor_of_prime_is_1 n ltac:(lia) Hprime) as Hd1.
    rewrite Hd1.
    cbn [largest_divisor].
    rewrite Nat.div_1_r.
    compute. reflexivity.
  - inversion Hprime. assumption.
Qed.

(* Any prime divisor of n is >= p = n / largest_divisor n.            *)
(* Follows from: the co-divisor m = n/q is a proper divisor of n,     *)
(* so m <= d = largest_divisor n, hence n/d <= n/m = q.               *)
Lemma prime_divisor_ge_quotient :
  forall n q,
    2 <= n ->
    prime q ->
    q |' n ->
    n / largest_divisor n <= q.
Proof.
  intros n q Hn Hq [m Hm].
  assert (Hq_pos : 0 < q) by (destruct Hq; lia).
  assert (Hm_pos : 0 < m) by (destruct m; lia).
  set (d := largest_divisor n).
  (* n/q = m is a proper divisor of n *)
  assert (Hm_div : m |' n) by (exists q; lia).
  assert (Hm_ne_n : m <> n) by (destruct Hq as [Hq2 _]; nia).
  assert (Hm_le_d : m <= d).
  { 
    apply largest_divisor_maximal. 
    - exact Hn.
    - exact Hm_div.
    - exact Hm_ne_n.
  }
  (* n/d <= n/m = q *)
  assert (Hd_facts := largest_divisor_divides n Hn).
  destruct Hd_facts as [Hd_ne0 [k Hdk]].
  assert (Hn_div_m : n / m = q).
  {
    rewrite <- Hm.
    apply Nat.div_mul.
    lia.
  }
  rewrite <- Hn_div_m.
  apply Nat.div_le_compat_l; lia.
Qed.

(* Every element of primefactors n is prime, and their product is n.  *)
(* Proof sketch:                                                       *)
(*   - product: n / d * product (primefactors d) = n                  *)
(*     follows from d |' n and the IH on d.                           *)
(*   - all_primes: p = n/d is prime because d is the *largest*        *)
(*     proper divisor, so p has no proper divisors itself.            *)
Theorem primefactors_correct :
  forall n, n > 1 ->
    product (primefactors n) = n /\ all_primes (primefactors n).
Proof.
  intros n.
  induction n using lt_wf_ind.
  intro Hgt1.
  destruct n as [| [| n'']]; try lia.
  set (N := S (S n'')).
  set (d := largest_divisor N).
  set (p := N / d).
  assert (Hn_gte2 : 2 <= N) by lia.
  assert (Hd_lt : d < N) by (unfold d; apply largest_divisor_strict; lia).

  destruct (Nat.eq_dec d 1) as [Hd1 | Hd1neq].
  - assert (Hunfold : primefactors N = p :: primefactors d) by (apply primefactors_unfold; lia).
    rewrite Hunfold.
    rewrite Hd1.
    split; simpl.
    + unfold p.
      rewrite Hd1.
      rewrite Nat.div_1_r.
      rewrite Nat.mul_1_r.
      reflexivity.
    + unfold all_primes.
      apply Forall_cons.
      * apply quotient_prime. assumption.
      * simpl. constructor.
  - assert (Hd_gt1 : d > 1).
    {
        unfold d.
        apply largest_divisor_of_composite_ge_2; [assumption|].
        intros Hprime.
        inversion Hprime.
        assert (largest_divisor N >= 1).
        {
          apply largest_divisor_ge1.
          assumption.
        }
        assert (largest_divisor N |' N).
        {
          apply largest_divisor_divides.
          assumption.
        }
        
        pose proof (H1 d H3) as [->|Hd_eq]; lia.
    }
  assert (Hunfold : primefactors N = p :: primefactors d) by
    (apply primefactors_unfold; lia).
  specialize (H d Hd_lt Hd_gt1) as [IHprod IHprimes].
  rewrite Hunfold.
  split.
  + (* product *)
    destruct (largest_divisor_divides N Hn_gte2) as [Hd_ne0 [k Hk]].
    simpl. rewrite IHprod.
    assert (N mod d = 0) by
      (apply Nat.mod_divides; [exact Hd_ne0 | exists k; lia]).
    pose proof (Nat.div_mod N d Hd_ne0) as Hdiv.
    subst p. rewrite H in Hdiv. lia.
  + (* all_primes *)
    apply Forall_cons.
    * apply quotient_prime; exact Hn_gte2.
    * exact IHprimes.
Qed.

Lemma head_primefactors_divides :
  forall n, n > 1 ->
    forall q rest, primefactors n = q :: rest -> q |' n.
Proof.
  intros n Hn q rest Hpf.
  destruct (primefactors_correct n Hn) as [Hprod _].
  rewrite <- Hprod.
  apply in_list_divides_product.
  rewrite Hpf. left. reflexivity.
Qed.

(* primefactors produces factors in ascending (le) order.             *)
(* The head p = n/d is the *smallest* prime factor of n; every prime  *)
(* q dividing d satisfies q >= p by prime_divisor_ge_quotient.        *)
Lemma primefactors_sorted :
  forall n, n > 1 -> Sorted le (primefactors n).
Proof.
  intros n.
  induction n using lt_wf_ind. intro Hn.
  destruct n as [|[|n'']]; try lia.
  set (N := S (S n'')).
  set (d := largest_divisor N).
  set (p := N / d).
  assert (Hn_gte2 : 2 <= N) by lia.
  assert (Hd_lt  : d < N) by (apply largest_divisor_strict; lia).
  assert (Hunfold : primefactors N = p :: primefactors d) by (apply primefactors_unfold; lia).
  rewrite Hunfold.
  destruct (classic (prime N)) as [HprimeN | HcompositeN].
  - (* N is prime: d = 1, primefactors d = [], result is [N], trivially sorted *)
    assert (Hd1 : d = 1) by (apply largest_divisor_of_prime_is_1; [lia | exact HprimeN]).
    assert (Hpf_d : primefactors d = []).
    {
      rewrite Hd1. compute.
      reflexivity.
    }
    rewrite Hpf_d.
    repeat constructor.
  - assert (Hd_gt1 : d > 1) by (apply largest_divisor_of_composite_ge_2; [lia | exact HcompositeN]).
    apply Sorted_cons.
    + exact (H d Hd_lt Hd_gt1).
    + destruct (primefactors d) as [| q rest] eqn:Hpf.
      * constructor.
      * constructor.
        apply prime_divisor_ge_quotient; [lia | | ].
        -- destruct (primefactors_correct d Hd_gt1) as [_ Hprimes].
           rewrite Hpf in Hprimes.
           apply Forall_inv in Hprimes. exact Hprimes.
        -- assert (Hqd : q |' d).
           {
             apply head_primefactors_divides with (rest := rest); assumption. 
           }
           destruct Hqd as [a Ha].
           destruct (largest_divisor_divides N Hn_gte2) as [_ [b Hb]].
           exists (a * b). unfold d in *. nia.
Qed.

(* ================================================================== *)
(* Deduplication and Distinct Prime Factors                            *)
(* ================================================================== *)

(* Deduplicate a sorted list, keeping one copy of each element.       *)
(* Precondition: input must be sorted (guaranteed by primefactors).   *)
Fixpoint dedup (l : list nat) : list nat :=
  match l with
  | []  => []
  | [x] => [x]
  | x :: ((y :: _) as rest) =>
      if x =? y then dedup rest else x :: dedup rest
  end.

(* dedup preserves all_primes since it only removes elements *)
Lemma dedup_all_primes :
  forall l, all_primes l -> all_primes (dedup l).
Proof.
  intros l Hl.
  induction l.
  - simpl. exact Hl.
  - destruct l.
    + simpl. exact Hl.
    + destruct (a =? n) eqn:EQ.
      * simpl. rewrite EQ.
        apply IHl.
        apply Forall_cons_iff in Hl.
        destruct Hl.
        apply H0.
      * simpl. rewrite EQ.
        apply Forall_cons_iff.
        apply Forall_cons_iff in Hl.
        destruct Hl as [HA HRest].
        split.
        -- apply HA.
        -- apply IHl.
           apply HRest.
Qed.

Lemma dedup_is_subset :
  forall l x, In x (dedup l) -> In x l.
Proof.
  intro l.
  induction l as [| a [| b rest] IH].
  - simpl. tauto.
  - simpl. auto.
  - simpl.
    destruct (a =? b).
    + intros x Hin.
      right.
      apply IH.
      destruct rest; assumption.
    + intros x Hin.
      destruct Hin as [-> | Hin].
      * left; reflexivity.
      * destruct rest.
        -- right.
           destruct Hin.
           ** left. assumption.
           ** right. assumption.
        -- right.
           apply IH.
           destruct (b =? n) eqn:EQ.
           ** simpl. rewrite EQ.
              assumption.
           ** simpl. rewrite EQ.
              assumption.
Qed.

Lemma sorted_implies_ge_head :
  forall l x y, Sorted le (x :: l) -> In y (x :: l) -> x <= y.
Proof.
  intros l x y Hsorted Hin.
  apply Sorted_StronglySorted in Hsorted; [| exact Nat.le_trans].
  inversion Hsorted as [| ? ? Hforall ?].
  destruct Hin as [-> | Hin]; [lia |].
  eapply Forall_forall in H; eassumption.
Qed.

Lemma sorted_tail :
  forall x l, Sorted le (x :: l) -> Sorted le l.
Proof.
  intros x l H.
  inversion H; subst; auto.
Qed.

(* dedup of a sorted list produces no duplicates *)
Lemma dedup_NoDup :
  forall l, Sorted le l -> NoDup (dedup l).
Proof.
  induction l as [| x [| y rest] IH]; intros Hsorted.
  - constructor.
  - repeat constructor; auto.
  - simpl. destruct (x =? y) eqn:EQ.
    + apply Nat.eqb_eq in EQ. subst.
      apply IH. eapply sorted_tail; eassumption.
    + constructor.
      * intro Hin.
        pose proof (dedup_is_subset (y :: rest) x) as dedup_is_subset.
        apply dedup_is_subset in Hin.
        apply Nat.eqb_neq in EQ.
        inversion Hsorted as [| ? ? Hhd Htail].
        inversion Hhd as [| ? ? Hle].
        assert (Hlt : x < y).
        {
          inversion Htail; subst.
          lia.
        }
        destruct Hin as [-> | Hin']; [lia |].
        assert (Hfall : Forall (le y) rest).
        { 
          apply Sorted_StronglySorted in Hhd; [| exact Nat.le_trans].
          inversion Hhd; assumption. 
        }
        eapply Forall_forall in Hfall; [| exact Hin']. lia.
      * apply IH. eapply sorted_tail; eassumption.
Qed.

Lemma dedup_NoDup_id :
  forall l, Sorted le l -> NoDup l -> dedup l = l.
Proof.
  intros l Hsorted HNoDup.
  induction l as [| x [| y rest] IH]; auto.
  simpl. destruct (x =? y) eqn:EQ.
  - apply Nat.eqb_eq in EQ. subst.
    inversion HNoDup; subst.
    simpl in H1.
    exfalso; apply H1; left; reflexivity.
  - f_equal.
    apply IH.
    + eapply sorted_tail. eassumption.
    + inversion HNoDup; assumption.
Qed.

Lemma primefactors_NoDup_of_sorted_perm :
  forall (l l' : list nat),
    Permutation l l' ->
    NoDup l ->
    NoDup l'.
Proof.
  intros l l' Hperm HNoDup.
  exact (Permutation_NoDup (A := nat) Hperm HNoDup).
Qed.

(* Distinct prime factors of n: deduplicated, sorted factor list.     *)
Definition distinct_primefactors (n : nat) : list nat :=
  dedup (primefactors n).

(* Correctness of distinct_primefactors: the result is a list of      *)
(* distinct primes. Note we don't claim product = n here since dedup  *)
(* removes repeated factors — the product may be smaller than n.      *)
Theorem distinct_primefactors_correct :
  forall n, n > 1 ->
    Sorted le (primefactors n) ->
    all_primes (distinct_primefactors n) /\
    NoDup (distinct_primefactors n).
Proof.
  intros n H Hsorted.
  unfold distinct_primefactors.
  split.
  - apply dedup_all_primes.
    exact (proj2 (primefactors_correct n H)).
  - apply dedup_NoDup.
    exact Hsorted.
Qed.

Lemma sorted_perm_eq :
  forall l1 l2 : list nat,
    Sorted le l1 -> Sorted le l2 ->
    Permutation l1 l2 ->
    l1 = l2.
Proof.
  intro l1.
  induction l1 as [| x l1' IH]; intros l2 Hs1 Hs2 Hperm.
  - symmetry. apply Permutation_nil. exact Hperm.
  - destruct l2 as [| y l2'].
    + symmetry in Hperm.
      apply Permutation_nil in Hperm. discriminate.
    + assert (x = y).
      { 
        assert (Hxiny : In x (y :: l2')) by (apply (Permutation_in _ Hperm); left; reflexivity).
        assert (Hyinx : In y (x :: l1')) by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
        pose proof (sorted_implies_ge_head l1' x y Hs1 Hyinx).
        pose proof (sorted_implies_ge_head l2' y x Hs2 Hxiny).
        lia. 
      }
      subst. f_equal.
      apply IH.
      * exact (sorted_tail _ _ Hs1).
      * exact (sorted_tail _ _ Hs2).
      * exact (Permutation_cons_inv Hperm).
Qed.

Lemma primefactors_product_id :
  forall l,
    all_primes l -> Sorted le l -> NoDup l ->
    primefactors (product l) = l.
Proof.
  intros l Hallprimes Hsorted HNoDup.
  destruct l as [| x l'].
  - compute. reflexivity.
  - assert (Hgt1 : product (x :: l') > 1) by (apply product_gt_1; [exact Hallprimes | discriminate]).
    apply sorted_perm_eq.
    + apply primefactors_sorted; lia.
    + exact Hsorted.
    + apply FTA_uniqueness with (n := product (x :: l')).
      * lia.
      * exact (proj2 (primefactors_correct _ Hgt1)).
      * exact Hallprimes.
      * exact (proj1 (primefactors_correct _ Hgt1)).
      * reflexivity.
Qed.

Lemma primefactors_of_prime_list_product :
  forall l,
    all_primes l ->
    NoDup l ->
    Sorted le l ->
    primefactors (product l) = l.
Proof.
  intros l Hprimes HNoDup Hsorted.
  destruct (product l) eqn:Hprod.
  - (* product l = 0 is impossible since all primes > 1 *)
    destruct (product_ge_1 l Hprimes); lia.
  - destruct n.
    + inversion Hprod.
      apply primefactors_product_id; assumption.
    + rewrite <- Hprod.
      apply primefactors_product_id; assumption.
Qed.

Theorem distinct_primefactors_product :
  forall l,
    all_primes l ->
    NoDup l ->
    Sorted le l ->
    length (distinct_primefactors (product l)) = length l.
Proof.
  intros l Hallprimes HNoDup HSorted.
  unfold distinct_primefactors.
  rewrite primefactors_of_prime_list_product; try assumption.
  rewrite dedup_NoDup_id; try assumption.
  reflexivity.
Qed.

(* A number has distinct prime factors if it can be written as a      *)
(* product of distinct primes.                                        *)
Definition has_distinct_prime_factors (n : nat) : Prop :=
  exists l, product l = n /\ all_primes l /\ NoDup l.

(* ================================================================== *)
(* Primality Test                                                       *)
(* ================================================================== *)

(* Check if n has any divisor in [2..k] *)
Fixpoint has_divisor (n k : nat) : bool :=
  match k with
  | 0 | 1 => false
  | S k'  =>
      if (n mod k =? 0) then true else has_divisor n k'
  end.

Definition is_prime (n : nat) : bool :=
  match n with
  | 0 | 1 => false
  | _     => negb (has_divisor n (n - 1))
  end.

Lemma has_divisor_false_iff :
  forall n k, has_divisor n k = false <-> forall m, 2 <= m <= k -> ~(m |' n).
Proof.
  intros n k.
  induction k as [| [| k'] IH].
  - simpl. split; [intros _ m Hm; lia | auto].
  - simpl. split; [intros _ m Hm; lia | auto].
  - destruct (n mod S (S k') =? 0) eqn:Hmod.
    + split.
      * cbn in *. rewrite Hmod. 
        discriminate.
      * intros Hall.
        exfalso. apply (Hall (S (S k'))); [lia |].
        apply Nat.eqb_eq in Hmod.
        exists (n / S (S k')).
        apply Nat.div_exact in Hmod; [lia | lia].
    + replace (has_divisor n (S (S k'))) with (has_divisor n (S k')).
      * rewrite IH. split.
        -- intros Hall m Hm.
           apply Nat.eqb_neq in Hmod.
           destruct (Nat.eq_dec m (S (S k'))) as [-> | Hne].
           ** intros [t Ht]. apply Hmod.
              apply Nat.mod_divides; [lia | exists t; lia].
           ** apply Hall; lia.
        -- intros Hall m Hm. apply Hall; lia.
      * unfold has_divisor.
        rewrite Hmod.
        reflexivity.
Qed.

(* is_prime correctly reflects the prime Prop *)
Lemma is_prime_correct :
  forall n, is_prime n = true <-> prime n.
Proof.
  intros n.
  split; intro H.
  - unfold is_prime in H.
    destruct n as [|[| n']]; try discriminate.
    apply Bool.negb_true_iff in H.
    rewrite has_divisor_false_iff in H.
    split; [lia|].
    intros k [m Hm].
    destruct (Nat.eq_dec k 1) as [| Hk1]; [left; assumption |].
    destruct (Nat.eq_dec k (S (S n'))) as [| HkN]; [right; assumption |].
    exfalso. apply (H k).
    + split.
      * destruct k; [lia|].
        destruct m; lia.
      * apply factor_le in Hm. lia.
    + exists m. exact Hm.
  - destruct H as [Hgt1 Hdivides].
    unfold is_prime.
    destruct n as [| [| n']]; try lia.
    apply Bool.negb_true_iff.
    apply has_divisor_false_iff.
    intros m [Hlo Hhi] [t Ht].
    destruct (Hdivides m) as [-> | ->].
    + exists t. assumption.
    + lia.
    + lia. 
Qed.

(* ================================================================== *)
(* Max Distinct Prime Factors                                           *)
(* ================================================================== *)

(* Iterate candidates from `candidate` upward, accumulating the       *)
(* product of primes found so far. Stop when the next prime would      *)
(* push the product over n. `fuel` is decremented each step to        *)
(* satisfy Coq's termination checker.                                  *)
(*                                                                      *)
(* This mirrors C++ TrialDivision::primeCount exactly:                 *)
(*   candidate  ↔  the loop variable (incremented each step)           *)
(*   prod       ↔  C++ `product`                                        *)
(*   count      ↔  C++ `count`                                         *)
(*   `prod * candidate <=? n`  ↔  C++ `product > n / next` (negated)  *)
Fixpoint max_distinct_aux
    (candidate : nat)  (* next number to test for primality *)
    (product   : nat)  (* product of primes included so far *)
    (count     : nat)  (* number of primes included so far  *)
    (n         : nat)  (* the upper bound                   *)
    (fuel      : nat)  (* decreases each step               *)
    : nat :=
  match fuel with
  | 0 => count
  | S fuel' =>
      if is_prime candidate then
        if product * candidate <=? n then
          max_distinct_aux (candidate + 1) (product * candidate) (count + 1) n fuel'
        else
          count   (* adding this prime would exceed n, so we're done *)
      else
        max_distinct_aux (candidate + 1) product count n fuel'
  end.

Definition max_distinct_prime_factors (n : nat) : nat :=
  max_distinct_aux 2 1 0 n n.

(* ================================================================== *)
(* Correctness                                                          *)
(* ================================================================== *)

(* Soundness: the answer is achieved by some number <= n.             *)
(* Proof sketch: the witness is the primorial of the first k primes   *)
(* (the product accumulated inside max_distinct_aux). Its distinct    *)
(* prime factors are exactly those k primes, justified by             *)
(* distinct_primefactors_correct.                                     *)
Definition aux_invariant
    (candidate prod count : nat) : Prop :=
  exists l,
    all_primes l /\
    NoDup l /\
    Sorted le l /\
    Forall (fun p => p < candidate) l /\
    length l = count /\
    product l = prod.

Lemma sorted_app_reverse :
  forall l c,
    Sorted le l ->
    Forall (fun p => p < c) l ->
    Sorted le (l ++ [c]).
Proof.
  intros l c Hsorted Hlt.
  induction l as [| x xs IH]; simpl.
  - repeat constructor.
  - apply Sorted_cons.
    + apply IH.
      * eapply sorted_tail. exact Hsorted.
      * inversion Hlt; assumption.
    + destruct xs; simpl.
      * constructor. inversion Hlt; lia.
      * constructor.
        inversion Hsorted as [| ? ? ? Htrans].
        inversion Htrans; assumption. 
Qed.

Lemma max_distinct_aux_sound :
  forall fuel candidate prod count n,
    prod <= n ->
    aux_invariant candidate prod count ->
    exists m, m <= n /\
      length (distinct_primefactors m) =
        max_distinct_aux candidate prod count n fuel.
Proof.
  induction fuel as [| fuel' IH]; intros candidate prod count n HProdleN Hinvariant.
  - exists prod. split; [exact HProdleN|].
    simpl.
    destruct Hinvariant as [l [Hprimes [HNoDup [Hsorted [Hlt [Hlen Hprod]]]]]].
    rewrite <- Hprod.
    rewrite distinct_primefactors_product; assumption.
  - simpl. destruct (is_prime candidate) eqn:Hprime.
    + destruct (prod * candidate <=? n) eqn:Hbound.
      * apply IH; [apply Nat.leb_le; exact Hbound|].
        destruct Hinvariant as [l [Hprimes [HNoDup [Hsorted [Hlt [Hlen Hprod]]]]]].
        exists (l ++ [candidate]). repeat split.
        -- apply Forall_app; split; [exact Hprimes|].
           apply Forall_cons; [apply is_prime_correct; exact Hprime | auto].
        -- clear - HNoDup Hlt.
           induction l as [| h t IHt]; simpl.
           ** apply NoDup_cons; [intros H; inversion H | assumption].
           ** apply NoDup_cons.
              --- intro Hin.
                  apply in_app_iff in Hin.
                  inversion HNoDup; subst.
                  destruct Hin as [Hin | Heq].
                  *** auto.
                  *** inversion Hlt; subst.
                      inversion Heq; [lia|inversion H].
              --- apply IHt.
                  *** inversion HNoDup; assumption.
                  *** inversion Hlt; assumption.
        -- apply sorted_app_reverse; assumption. 
        -- apply Forall_app. split; [| apply Forall_cons; [lia | auto]].
           eapply Forall_impl; [| exact Hlt].
           intros. inversion H; lia.
        -- rewrite app_length.
           f_equal. exact Hlen.
        -- rewrite product_app_reverse.
           rewrite Hprod.
           reflexivity.
      * exists prod. split; [exact HProdleN|].
        destruct Hinvariant as [l [Hprimes [HNoDup [Hsorted [Hlt [Hlen Hprod]]]]]].
        rewrite <- Hprod.
        rewrite distinct_primefactors_product; assumption.
    + apply IH; [exact HProdleN|].
      destruct Hinvariant as [l [Hprimes [HNoDup [Hsorted [Hlt [Hlen Hprod]]]]]].
      exists l; repeat split; try assumption.
      eapply Forall_impl; [| exact Hlt].
      intros. inversion H; lia.  
Qed.

Theorem max_distinct_sound :
  forall n,
    1 <= n ->
    exists m, m <= n /\
      length (distinct_primefactors m) = max_distinct_prime_factors n.
Proof.
  intros n Hgte1.
  unfold max_distinct_prime_factors.
  apply max_distinct_aux_sound; [assumption|].
  exists []. repeat split; constructor.
Qed.

(* Maximality: no number <= n has more distinct prime factors.        *)
(* Proof sketch: any number with k distinct prime factors has a       *)
(* product of k distinct primes as a divisor. The smallest such       *)
(* product is the primorial of the first k primes (exchange argument).*)
(* If that primorial exceeds n then no such number can exist in [1..n]*)
(* and max_distinct_aux would have stopped before counting k.         *)

Lemma divides_is_divide :
  forall n m,
    n |' m <-> Nat.divide n m.
Proof.
  intros n m.
  split; intro H. 
  all: inversion H; exists x; lia.
Qed.

Lemma prime_coprime :
  forall p q, prime p -> prime q -> p <> q -> Nat.gcd p q = 1.
Proof.
  intros p q HpPrime HqPrime Hneq.
  destruct HpPrime as [Hp_gt1 Hp_div].
  destruct HqPrime as [Hq_gt1 Hq_div].

  destruct (Hp_div (Nat.gcd p q)) as [|Hgp].
  - destruct (Nat.gcd_divide_l p q) as [k Hk].
    exists k. lia.
  - assumption.
  - destruct (Hq_div (Nat.gcd p q)) as [|Hgq].
    + destruct (Nat.gcd_divide_r p q) as [k Hk].
      exists k. lia.
    + assumption.
    + exfalso.
      apply Hneq.
      rewrite <- Hgp.
      rewrite <- Hgq at 2.
      reflexivity.
Qed.


Lemma distinct_primefactors_all_divide :
  forall m, m > 1 ->
    Forall (fun p => p |' m) (distinct_primefactors m).
Proof.
  intros n H.
  apply Forall_forall.
  intros x Hin.
  unfold distinct_primefactors in Hin.
  apply dedup_is_subset in Hin.
  apply in_list_divides_product in Hin.
  destruct (primefactors_correct n H) as [Hid _].
  rewrite <- Hid.
  assumption. 
Qed.

Lemma coprime_to_product :
  forall p l,
    prime p ->
    all_primes l ->
    ~In p l ->
    Nat.gcd p (product l) = 1.
Proof.
  intros p l Hprime Hallprimes Hnotin.
  induction l; simpl.
  - apply Nat.gcd_1_lcm_mul; [|lia|].
    + inversion Hprime; lia.
    + rewrite Nat.lcm_1_r.
      lia.
  - inversion Hallprimes as [| ? ? Hh_primes Htail_prime]; subst.
    assert (Hpa_neq: p <> a).
    {
      intro Heq.
      apply Hnotin.
      left. symmetry.
      exact Heq.
    }

    assert (Hnotin_l: ~ In p l).
    {
      intro Hin.
      apply Hnotin.
      right; assumption.
    }

    assert (Hgcd_pa: Nat.gcd p a = 1) by (apply prime_coprime; assumption).
    assert (Hgcd_pl: Nat.gcd p (product l) = 1).
    {
      apply IHl; [assumption|].
      exact Hnotin_l.
    }

    set (d := Nat.gcd p (a * product l)).
    assert (Hd_div_p: d |' p).
    {
      subst d.
      destruct (Nat.gcd_divide_l p (a * product l)) as [k Hk].
      exists k. lia.
    }

    destruct Hprime as [Hp_gt1 Hp_div].
    specialize (Hp_div d Hd_div_p) as [Hd1 | Hdp].
    + subst d. exact Hd1.
    + exfalso. subst d.
      assert (Hp_div_aprod: p |' (a * product l)).
      {
        destruct (Nat.gcd_divide_r p (a * product l)) as [k Hk].
        rewrite Hdp in Hk at 1.
        exists k. lia.
      }
      
      assert (Hp_div_approd_nat: Nat.divide p (a * product l)).
      {
        apply divides_is_divide.
        exact Hp_div_aprod.
      }

      assert (Hp_div_prod_nat: Nat.divide p (product l)) by (eapply Nat.gauss; eauto).
      assert (Hp_div_gcd_nat: Nat.divide p (Nat.gcd p (product l))).
      {
        apply Nat.gcd_greatest.
        - exists 1. lia.
        - exact Hp_div_prod_nat.
      }

      rewrite Hgcd_pl in Hp_div_gcd_nat.
      destruct Hp_div_gcd_nat as [k Hk].
      destruct k; simpl in Hk; lia.
Qed.

Lemma divisor_le :
  forall k m, k |' m -> 0 < m -> k <= m.
Proof.
  intros k m [t Ht] Hpos.
  destruct m.
  - lia.
  - eapply factor_le.
    exact Ht.
Qed.

Lemma mul_dvd_of_coprime :
  forall a b m,
    Nat.gcd a b = 1 ->
    a |' m ->
    b |' m ->
    (a * b) |' m.
Proof.
  intros a b m Hcop [ka Hka] Hb_div.
  (* m = a * ka, and b | a * ka *)
  (* Since gcd(a,b) = 1, by Gauss: b | ka *)
  rewrite divides_is_divide in Hb_div.
  rewrite <- Hka in Hb_div.
  rewrite Nat.gcd_comm in Hcop.

  pose proof (Nat.gauss b a ka Hb_div Hcop) as Hb_ka.
  destruct Hb_ka as [j Hj].
  exists j.
  lia.
Qed.

(* Core lemma for maximality: if every prime in l divides m,          *)
(* and the primes in l are distinct, then their product divides m.    *)
(* Proof: by induction on l, using pairwise coprimality of distinct   *)
(* primes and Gauss's lemma.                                          *)
Lemma nodup_primes_product_divides :
  forall l m,
    all_primes l -> NoDup l ->
    Forall (fun p => p |' m) l ->
    product l |' m.
Proof.
  intros l.
  induction l as [|h rest IH]; intros m Hallprimes HNoDup Hforall; simpl.
  - exists m. lia.
  - inversion Hallprimes as [| ? ? Hh_primes Hrest_primes]; subst.
    inversion HNoDup   as [| ? ? Hh_notin Hrest_nodup]; subst.
    inversion Hforall  as [| ? ? Hh_div Hrest_div]; subst.

    assert (Hprod_rest : product rest |' m) by (apply IH; assumption).
    apply mul_dvd_of_coprime; try assumption.
    apply coprime_to_product; assumption.
Qed.

Lemma forall_neq_of_notin :
  forall (a : nat) l,
    ~ In a l ->
    Forall (fun x => x <> a) l.
Proof.
  intros a l Hnotin.
  induction l as [|x xs IH]; constructor.
  - intro Heq. apply Hnotin. left. exact Heq.
  - apply IH. intro Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma forall_succ_from_ge_and_neq :
  forall c l,
    Forall (fun x => c <= x) l ->
    Forall (fun x => x <> c) l ->
    Forall (fun x => c + 1 <= x) l.
Proof.
  intros c l Hge Hneq.
  induction Hge.
  - constructor.
  - inversion Hneq; subst.
    constructor; [lia | auto].
Qed.

Lemma sorted_head_le_tail :
  forall h t,
    Sorted le (h :: t) ->
    Forall (fun x => h <= x) t.
Proof.
  intros h t Hs.
  induction t as [|x xs IH].
  - apply Forall_nil.
  - inversion Hs as [| ? ? Hsorted_xt' HhdRel]; subst.
    inversion HhdRel; subst.  (* gives h <= x *)
    constructor; [assumption |].
    apply IH.
    inversion Hsorted_xt' as [| ? ? Hsorted_t' HhdRel']; subst.
    constructor.
      * assumption.
      * inversion HhdRel'; subst; repeat constructor. lia.
Qed.

(* Main inductive step for maximality.                                *)
(* Invariant: l is a list of primes (distinct, sorted, all >= cand)  *)
(* whose product times prod_acc fits in n.  Then the algorithm's     *)
(* final count is at least count + length l.                         *)
Lemma max_distinct_aux_counts_ge :
  forall fuel candidate prod_acc count n l,
    all_primes l ->
    NoDup l ->
    Sorted le l ->
    Forall (fun p => candidate <= p) l ->
    prod_acc * product l <= n ->
    prod_acc >= 1 ->
    n < candidate + fuel ->
    count + length l <= max_distinct_aux candidate prod_acc count n fuel.
Proof.
  induction fuel; intros candidate prod_acc count n l 
    Hallprimes HNoDup Hsorted Hforall Hbound Hprod_pos Hfuel.
  - simpl.
    destruct l as [| h t].
    + simpl. lia.
    + exfalso.
      inversion Hforall as [| ? ? Hh_ge ht]; subst.
      assert (Hh_prime : prime h) by (inversion Hallprimes; assumption).
      assert (Hh_ge2 : h >= 2) by (destruct Hh_prime; lia).
      assert (Hprod_ge : product (h :: t) >= h).
      {
        simpl.
        assert (product t >= 1).
        { 
          apply product_ge_1. inversion Hallprimes; assumption. 
        }
        nia.
      }
      assert (candidate > n) by lia.
      nia.
  - simpl.
    destruct (is_prime candidate) eqn:Hcp.
    + destruct (prod_acc * candidate <=? n) eqn:Hfit.
      * apply Nat.leb_le in Hfit.
        destruct l as [| h t].
        -- simpl.
           assert (Hstep: (count + 1) + (length ([] : list nat)) <= (max_distinct_aux (candidate + 1) (prod_acc * candidate) (count + 1) n fuel)).
           {
             apply IHfuel.
             + constructor.
             + constructor.
             + constructor.
             + constructor.
             + simpl. lia.
             + apply is_prime_correct in Hcp.
               destruct Hcp as [Hcand_ge2 _].
               nia.
             + lia.
           }
           simpl in Hstep.
           lia.
        -- inversion Hallprimes  as [| ? ? Hh_prime  Ht_primes]; subst.
           inversion HNoDup   as [| ? ? Hh_notin  Ht_nodup];  subst.
           inversion Hforall  as [| ? ? Hh_ge     Ht_ge];     subst.
           destruct (Nat.eq_dec h candidate) as [Heq | Hne].
           ++ subst.
              apply Nat.le_trans with
                (m := (count + 1) + length t).
              ** simpl. lia.
              ** apply IHfuel; try assumption.
                 --- eapply sorted_tail; eassumption.
                 --- eapply forall_succ_from_ge_and_neq.
                     +++ exact Ht_ge.
                     +++ apply forall_neq_of_notin.
                         exact Hh_notin.
                 --- simpl in Hbound. nia.
                 --- inversion Hh_prime. lia.
                 --- lia.
           ++ assert (Hh_gt : h > candidate) by lia.
              apply Nat.le_trans with (m := (count + 1) + length t).
              ** simpl. lia.
              ** apply IHfuel.
                 --- exact Ht_primes.
                 --- exact Ht_nodup.
                 --- eapply sorted_tail; eassumption.
                 --- pose proof (sorted_head_le_tail h t Hsorted) as Htail_ge_h.
                     apply Forall_forall.
                     intros x Hinx.
                     apply Forall_forall with (x := x) in Htail_ge_h; [| exact Hinx].
                     lia.
                 --- simpl in Hbound.
                     assert (Hpt_ge1 : 1 <= product t).
                     { apply product_ge_1. exact Ht_primes. }
                     nia.
                 --- apply is_prime_correct in Hcp.
                     destruct Hcp as [Hcand_ge2 _].
                     nia.
                 --- lia.
      * apply Nat.leb_nle in Hfit.
        destruct l as [| h t].
        -- simpl. lia.
        -- exfalso.
           inversion Hallprimes  as [| ? ? Hh_prime  ?]; subst.
           inversion Hforall  as [| ? ? Hh_ge     ?]; subst.
           assert (Hprod_ge : product (h :: t) >= h).
           {
             simpl.
             assert (product t >= 1).
             { 
              apply product_ge_1. inversion Hallprimes; assumption. 
             }
             nia.
           }
           nia.
    + apply IHfuel; try assumption.
      * assert (Hcand_not_prime : ~ prime candidate).
        {
          intro Hpc.
          apply is_prime_correct in Hpc.
          rewrite Hpc in Hcp.
          discriminate.
        }
        apply Forall_forall.
        intros x Hinx.
        assert (Hx_ge : candidate <= x).
        { eapply Forall_forall; [exact Hforall | exact Hinx]. }
        assert (Hx_prime : prime x).
        { eapply Forall_forall; [exact Hallprimes | exact Hinx]. }
        assert (x <> candidate).
        { intro Heq; subst; contradiction. }
        lia.
      * lia.
Qed.

Lemma Forall_dedup :
  forall (P : nat -> Prop) l,
    Forall P l ->
    Forall P (dedup l).
Proof.
  intros P l HFor.
  apply Forall_forall.
  intros x Hinx.
  apply dedup_is_subset in Hinx.
  eapply Forall_forall; eauto.
Qed.

Lemma dedup_strongly_sorted :
  forall l, StronglySorted le l -> StronglySorted le (dedup l).
Proof.
  intros l Hss.
  induction l as [| x l IH].
  - simpl. constructor.
  - destruct l as [| y rest].
    + simpl. constructor; constructor.
    + simpl.
      inversion Hss as [| ? ? Hss_tail Hforall_tail]; subst.
      destruct (x =? y) eqn:Heq.
      * apply IH. exact Hss_tail.
      * constructor.
        -- apply IH. exact Hss_tail.
        -- change (Forall (le x) (dedup (y :: rest))).
           apply Forall_dedup. exact Hforall_tail.
Qed.

Lemma dedup_sorted :
  forall n,
    Sorted le (primefactors n) ->
    Sorted le (distinct_primefactors n).
Proof.
  intros n Hsorted.
  unfold distinct_primefactors.
  apply StronglySorted_Sorted.
  apply dedup_strongly_sorted.
  apply Sorted_StronglySorted; [exact Nat.le_trans | exact Hsorted].
Qed.

Theorem max_distinct_maximal :
  forall n m,
    m <= n ->
    length (distinct_primefactors m) <= max_distinct_prime_factors n.
Proof.
  intros n m Hle.
  destruct (le_lt_dec m 1) as [Hle1 | Hgt1].
  - destruct m as [|[|m']].
    all: unfold distinct_primefactors, primefactors; simpl; lia.
  - unfold max_distinct_prime_factors.
    apply Nat.le_trans with
      (m := 0 + length (distinct_primefactors m)).
    + lia.
    + apply max_distinct_aux_counts_ge with
        (l := distinct_primefactors m).
      * exact (proj1 (distinct_primefactors_correct m Hgt1
                        (primefactors_sorted m Hgt1))).
      * exact (proj2 (distinct_primefactors_correct m Hgt1
                        (primefactors_sorted m Hgt1))).
      * apply dedup_sorted. apply primefactors_sorted. lia.
      * apply Forall_forall. intros x Hx.
        assert (Hprimes := proj1 (distinct_primefactors_correct m Hgt1
                                    (primefactors_sorted m Hgt1))).
        eapply Forall_forall in Hprimes; [| exact Hx].
        destruct Hprimes as [Hgt1' _].
        lia.
      * apply Nat.le_trans with (m := m); [| exact Hle].
        apply divisor_le; [| lia].
        rewrite Nat.mul_1_l.
        apply nodup_primes_product_divides.
        -- exact (proj1 (distinct_primefactors_correct m Hgt1
                          (primefactors_sorted m Hgt1))).
        -- exact (proj2 (distinct_primefactors_correct m Hgt1
                          (primefactors_sorted m Hgt1))).
        -- exact (distinct_primefactors_all_divide m Hgt1).
      * lia.
      * lia.
Qed.