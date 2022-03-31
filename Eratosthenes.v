Require Import ZArith_base.
Require Import Zdiv.
Require Import NPeano.
Require Import Psatz.
Require Import Coq.Init.Nat.
Require Import Omega.
Require Import PeanoNat.
Require Import List Relations Relations_1.
Local Open Scope nat_scope.
Require Import List.
Require Import Sorting.Sorted.
Open Scope list_scope.
Require Import Coq.Structures.Orders.
Require Import NAxioms NProperties OrdersFacts.
Include Coq.Init.Nat.
Require Import Classical_Prop.
Require Import Bertrand.Bertrand.
Require Import Bertrand.Prime.
Require Import Coq.Logic.Classical.
Import List.ListNotations.

Definition getListOfN (n : nat) : list nat :=
  List.seq 2 (n-1).

Definition divides (n m : nat) : bool :=
 match n with
 | 0 => m =? 0
 | _ => m mod n =? 0
 end.

Definition sieveHelper (p : nat) (l : list nat) : list nat :=
filter (fun a => negb (divides p a)) l.


Fixpoint siever (len : nat) (l : list nat) : list nat :=
match len with
  | O => l
  | S len' => match l with
              | nil => nil
              | p :: z => p :: (siever len' ((sieveHelper p) z))
              end
end.

Definition primesUpToN (n : nat) : list nat :=
  siever n (getListOfN n).


Theorem filterPreservesSortedness 
  (P : nat -> nat -> Prop) (l : list nat) (f : nat -> bool) :
  StronglySorted P l -> StronglySorted P (filter f l).
Proof.
induction 1.
- simpl. constructor.
- simpl. destruct (f a).
  + apply SSorted_cons. apply IHStronglySorted.
    assert (incl (filter f l) l) by apply incl_filter. apply incl_Forall with l.
    { exact H1. }
    { exact H0. }
  + apply IHStronglySorted.
Qed.

Theorem filterPreservesSortednessCons 
  (P : nat -> nat -> Prop) (f : nat -> bool) (n : nat) (l : list nat):
  StronglySorted P (n :: l) -> StronglySorted P (n :: (filter f l)).
Proof.
intros. apply SSorted_cons.
- apply StronglySorted_inv in H. destruct H.
  apply filterPreservesSortedness. exact H.
- apply StronglySorted_inv in H. destruct H.
  assert (incl (filter f l) l) by apply incl_filter.
  apply incl_Forall with l; auto.
Qed.

Lemma divideSame:
  forall n m, (n | m) <-> (divides n m = true).
Proof.
split. 
  - intros. destruct n.
    + apply NPeano.Nat.divide_0_l in H. subst. reflexivity.
    + apply NPeano.Nat.mod_divide in H. 
      * unfold divides. apply NPeano.Nat.eqb_eq. apply H.
      * lia.
  - intros. destruct n.
    + simpl in H. apply beq_nat_true in H. subst. intuition.
    + unfold divides in H. apply NPeano.Nat.mod_divide.
      * lia.
      * apply NPeano.Nat.eqb_eq. apply H.
Qed.

Lemma dividesSame2:
  forall n m, (divides n m = true) <-> Divides.divides n m.
Proof.
split.
- intros. destruct n.
  + simpl in H. apply beq_nat_true in H. subst. intuition.
  + unfold divides in H. apply NPeano.Nat.mod_divide.
      * lia.
      * apply NPeano.Nat.eqb_eq. apply H.
- intros. destruct n.
    + apply NPeano.Nat.divide_0_l in H. subst. reflexivity.
    + apply NPeano.Nat.mod_divide in H. 
      * unfold divides. apply NPeano.Nat.eqb_eq. apply H.
      * lia.
Qed.


Definition I (m n : nat) (l : list nat) : Prop :=
match l with
  | [] => forall x, m <= x <= n -> ~(prime x)
  | x :: l' => (
    prime x /\
    (forall x' y, x' < x /\ x' > 1 -> (In y l') -> ~(x' | y)) /\
    (forall x', x < x' <= n -> prime x' -> (In x' l')) /\
    (StronglySorted lt l) /\
    (forall y, In y l -> y <= n) /\ 
    m = x
  ) 
  end.

Theorem soundSortedPrime (l : list nat) (x : nat) :
  x > 1 -> StronglySorted lt (x :: l) /\
  (forall x' y, 1 < x' < x -> (In y (x :: l)) -> ~(x' | y)) ->
    prime x.
Proof.
intros. destruct H0.
assert (forall x', 1 < x' < x -> ~(x' | x)).
{ intros. apply H1.
  { exact H2. }
  { intuition. }
}
unfold prime.
split. { lia. }
intros.
assert (x = b \/ ~(x = b))by apply classic.
destruct H5. { exact H5. }
assert (b < x \/ b > x) by lia.
destruct H6.
- unfold Divides.divides in H3.
  assert (x = 0 \/ ~(x = 0)) by apply classic.
  destruct H7.
    { subst. inversion H6. }
  assert (b = 0 \/ ~(b = 0)) by apply classic.
  destruct H8.
    { subst. destruct H3. lia. }
  assert (1 < b < x) by lia.
  apply H2 in H9. unfold not in H9. unfold Nat.divide in H9.
  apply H9 in H3. intuition.
- assert (b = 0 \/ ~(b = 0)) by apply classic.
  destruct H7.
  + unfold Divides.divides in H3. subst. lia.
  + assert (~Divides.divides b x).
    { apply not_lt_div. lia. lia. } contradiction.
Qed.

Theorem noDupStronglySortedlt l :
  StronglySorted lt l -> NoDup l.
Proof.
induction l.
- intros. apply NoDup_nil.
- intros. apply StronglySorted_inv in H.
  destruct H. apply IHl in H.
  apply NoDup_cons.
  { rewrite Forall_forall in H0.
    unfold not. intros.
    apply H0 in H1. lia. }
  { exact H. }
Qed.

Lemma seqSorted n m:
  StronglySorted lt (seq n m).
Proof.
revert n.
induction m.
- intros. simpl. apply SSorted_nil.
- intros. rewrite <- cons_seq. 
  specialize (IHm (S n)). constructor.
  + apply IHm.
  + assert (forall (x : nat), In x (seq (S n) m) -> n < x).
    { intros. apply in_seq in H. lia. }
    rewrite Forall_forall. exact H.
Qed.

Lemma seqHead len x l:
  len > 0 -> (seq 2 len) = (x :: l) ->
    2 = x.
Proof. 
intros. simpl in *. destruct len.
- discriminate.
- simpl in *. inversion H0. reflexivity.
Qed.

Lemma IgetListOfN (m n : nat) :
  I 2 n (getListOfN n).
Proof.
unfold I. unfold getListOfN. remember (seq 2 (n - 1)) as a.
assert (n = 0 \/ n = 1 \/ n > 1) by lia. destruct H.
- destruct a.
  { intuition. }
  { subst. inversion Heqa. }
- destruct H.
  + destruct a.
    { intuition. }
    { subst. inversion Heqa. }
  + destruct a. 
    * intuition. assert (n-1 >= 1) by lia.
      assert (length (seq 2 (n-1)) = n-1) by apply seq_length.
      assert ((length (seq 2 (n-1))) >= 1 ) by lia. 
      rewrite <- Heqa in H5. inversion H5.
    * split.
      -- assert (2 = n0). 
         { apply seqHead with (n - 1) a. { lia. } { symmetry. exact Heqa. } }
         subst. unfold prime. split.
         { lia. } 
         { intros.
           assert (b = 0 \/ b = 1 \/ b = 2 \/ b > 2) by lia. 
           destruct H2.
           { subst. inversion H0. lia. }
            destruct H2.
            { subst. contradiction. }
            destruct H2.
            { subst. reflexivity. }
            { assert (b <> 0) by lia. 
              assert (2 < b) by lia.
              apply not_lt_div in H4.
              { contradiction. }
              { lia. }
         } }
      -- split.
          ** unfold not. intros. assert (1 < x' < n0) by lia. clear H0.
            assert (2 = n0). 
            { apply seqHead with (n - 1) a. 
              { lia. } 
              { symmetry. exact Heqa. } }
            subst. inversion H3. lia.
          ** split.
            --- intros.
                assert (2 = n0).
                  { apply seqHead with (n - 1) a. 
                    { lia. }
                    { symmetry. exact Heqa. } }
                assert (n0 <= x' < (n0 + (n-1))) by lia. 
                subst. rewrite <- in_seq in H3.
                rewrite <- Heqa in H3. apply in_inv in H3. destruct H3.
                { subst. lia. }
                { exact H2. }
            --- split.
                ++ rewrite Heqa. apply seqSorted.
                ++ split.
                  +++ intros. rewrite Heqa in H0. 
                      rewrite in_seq in H0. lia.
                  +++ assert (2 = n0). 
                      { apply seqHead with (n - 1) a. 
                        { lia. }
                        { symmetry. exact Heqa. } }
                      exact H0.
Qed.

Lemma primeNotDivisible :
  forall m p, prime p -> 1 < m < p -> ~(m | p).
Proof.
intros. unfold not. unfold prime in H. 
intros. destruct H. intuition. destruct H2 with m. 
  - apply H1.
  - lia.
  - lia.
Qed.

Lemma divideSameOther:
  forall n m, ((n | m) <-> (divides n m = true)) -> 
    (~(n | m) <-> (divides n m = false)).
Proof.
intros. apply not_iff_compat in H. destruct H. split.
  - intros. rewrite <- Bool.not_true_iff_false. apply H. apply H1.
  - intros. apply H0. rewrite Bool.not_true_iff_false. apply H1.
Qed.


Lemma sortedHelperNoDup2 (p a : nat) (l : list nat):
  StronglySorted lt (p :: l) -> In a l -> p < a.
Proof.
intros. assert (StronglySorted lt l /\ Forall (lt p) l).
{  apply StronglySorted_inv. exact H. }
assert (NoDup (p :: l)). { apply noDupStronglySortedlt; auto. }
destruct H1.
assert (H5: Forall (lt p) l). { intuition. }
rewrite Forall_forall in H5. apply H5. apply H0.
Qed.

Lemma notIn (p x' : nat) (l : list nat) :
  NoDup (l) -> StronglySorted lt (p :: l) -> 
   ~In p l -> In x' l -> p < x'.
  intros. assert (NoDup (p :: l)). 
    { apply NoDup_cons.
      { apply H1. }
      { apply H. } }
      apply sortedHelperNoDup2 with l.
  - apply H0.
  - apply H2.
Qed.

Lemma NoPrimeDeleted (l l0 : list nat) (p n0 x' n : nat):
  StronglySorted lt (p :: l) -> 
  filter (fun a : nat => negb (divides p a)) l = (n0 :: l0) -> 
  prime p -> In x' l -> prime x' -> n0 < x' <= n -> In x' l0.
Proof.
intros.
assert (NoDup (p :: l)). 
{ apply noDupStronglySortedlt; auto. }
assert (prime x' -> negb (divides p x') = true).
{ intros. apply Bool.negb_true_iff. apply divideSameOther.  
    - apply divideSame.
    - apply primeNotDivisible.
      ** auto.
      ** intuition. 
        ++ assert (~(prime 0)) by apply not_prime_O. 
           assert (p > 0). 
            { apply prime_2_or_more in H1. lia. } 
            unfold prime in H5. unfold prime in H1. lia. 
        ++ apply NoDup_cons_iff in H5. destruct H5. 
           apply notIn with l; auto.
  }
assert (In x' l /\ ((fun a : nat => negb (divides p a)) x' = true)). 
{ intuition. }
rewrite <- filter_In in H7.
assert (NoDup (filter (fun a : nat => negb (divides p a)) l)). 
{ apply NoDup_filter. apply NoDup_cons_iff in H5.
  destruct H5. apply H8. }
intuition. 
apply Nat.lt_neq in H9. 
assert (In x' (n0 :: l0)). 
{ rewrite <- H0. exact H7. } 
unfold not in H9. unfold In in H6.
intuition.
Qed.

Lemma pSmaller (p x' z n0: nat) (l l0 : list nat) :
  StronglySorted lt (p :: l) -> 
  filter (fun a : nat => negb (divides p a)) l = n0 :: l0 -> 
  n0 < x'-> 
    p < x'.
Proof.
intros. 
assert (NoDup (p :: l)). { apply noDupStronglySortedlt; auto. }
apply StronglySorted_inv in H. 
assert (incl (filter (fun a : nat => negb (divides p a)) l)  l). 
{ subst. apply incl_filter. } 
rewrite H0 in H3. 
apply incl_Forall with (P := (lt p)) in H3. 
- apply Forall_inv in H3. lia.
- intuition.
Qed.

Lemma noDivisorBetweenPand2P (p n m : nat) :
  p > 2 /\ n > 0 /\ m > 0 ->
    p < (p + n) /\ (p + n) < (p + m) /\ (p + m) < (2 * p) ->
      ~((p + n) | (p + m)).
Proof.
unfold not. intros.
unfold Nat.divide in H1. destruct H1.
assert (x = 0 \/ x = 1 \/ x > 1) by lia.
destruct H2. { subst. lia. }
destruct H2. { subst. lia. }
nia.
Qed.

Lemma Bertrand (p : nat) :
  forall n : nat, 2 <= n -> exists p : nat, prime p /\ n < p /\ p < 2 * n.
Proof.
apply Bertrand.
Qed.

Lemma existsA (p m : nat) :
  p < m -> exists a, m = p + a.
Proof.
intros. econstructor. intuition.
Qed.

Section Generic.
Variable U : Type.

Lemma not_ex_all_not :
 forall P:U -> Prop, ~ (exists n : U, P n) -> forall n:U, ~ P n.
Proof.
unfold not; intros P notex n abs.
apply notex.
exists n; trivial.
Qed.
End Generic.

Lemma SortedNotInHelper (l : list nat) (q p : nat) :
  StronglySorted lt (p :: l) /\ ~(q = p) /\ In q (p :: l) -> In q l.
Proof. 
intros. destruct H. destruct H0. intuition. 
assert (q = p \/ ~(q = p)) by intuition.
destruct H2.
- intuition.
- apply in_inv in H1. destruct H1.
  + symmetry in H1. apply H0 in H1. intuition.
  + exact H1.
Qed.

Lemma SortedNotIn (l : list nat) (q p' : nat) : 
  q < p' /\ StronglySorted lt (p' :: l) -> ~(In q (p' :: l)).
Proof.
unfold not. intros.
assert (StronglySorted lt (p' :: l) /\ ~(q = p') 
          /\ In q (p' :: l)) by intuition.
apply SortedNotInHelper in H1.
destruct H.
apply StronglySorted_inv in H2. destruct H2.
rewrite Forall_forall in H3.
assert (lt p' q).
{ apply H3. exact H1. }
intuition.
Qed.

Lemma p'Prime p p':
  ((prime p) /\ 
  ~(p | p') /\ 
  (p < p') /\
  (forall q, p < q < p' -> ~ (prime q)) /\
  (forall q, 1 < q < p -> ~(q | p)) /\
  (forall q : nat, 1 < q < p -> ~ (q | p'))) -> 
    prime p'.
Proof.
intros. 
destruct H as [Hprime [Hnodiv [Hsmaller [Hnotprime [HnodivQ nodivHelper]]]]].
unfold prime. split.
  - assert (p >= 2). { apply prime_2_or_more in Hprime. lia. } lia.
  - intros m Hmdivp'.
    assert (m <> p).
      { unfold not. intros. subst. contradiction. }
    assert (m > p' \/ m = p' \/ m < p') by lia.
    destruct H0. 
      { apply Nat.divide_pos_le in Hmdivp'; intuition. }
    destruct H0.
      { intros. lia. }
    assert (m = 0 \/ (1 < m < p) \/ m = 1 \/ (p < m < p')) by lia.
    destruct H1.
      { subst. inversion Hmdivp'. intuition. }
    destruct H1.
      { exfalso. unfold not in HnodivQ. apply HnodivQ with m.
        { apply H1. } 
        { exfalso. unfold not in Hnotprime. apply HnodivQ with m.
          { apply H1. } 
          { exfalso. unfold not in nodivHelper. apply nodivHelper with m.
            { apply H1. }
            { apply Hmdivp'. } }
        }
       }
    destruct H1.
      { intros. subst. contradiction. }
    + assert (p' > 2 /\ p >= 2).
      { assert (p >= 2).
        { apply prime_2_or_more in Hprime. lia. } 
        unfold prime in Hprime. lia. }
      assert (p' = 2 \/ p' = 3 \/ p' > 3) by lia.
      destruct H3.
      { destruct H2. intuition. }
      destruct H3.
      { intuition. }
      assert ((p' >= 2*p) \/ (p' < 2*p)) by lia.
      destruct H4.
      ++ assert (forall q, p < q < (2*p) -> ~(prime q)).
         { unfold not. intros. unfold not in Hnotprime. 
           apply Hnotprime with q. lia. exact H6.
         }
         assert ((~(exists q, p < q < (2 * p) /\ prime q))).
         { unfold not. intros. destruct H6.
           destruct H6. unfold not in H5. 
           apply H5 with x. exact H6. exact H7. }
         apply not_ex_all_not with (n := p') in H6.
         assert (exists p', prime p' /\ p < p' < 2 * p).
         { apply Bertrand. apply p'. lia. }
         destruct H7.
         destruct H7.
         apply H5 in H8.
         contradiction.
      ++ assert (exists a, m = p + a).
         { apply existsA. lia. }
        destruct H5. subst.
        assert (p < p + x /\ p + x < p' /\ p' < 2 * p) by lia.
        assert (exists b, p' = p + b).
        { apply existsA. lia. }
        destruct H6. subst.
        assert (~((p + x) | (p + x0))).
        { apply noDivisorBetweenPand2P.
          { lia. }
          { lia. }
        }
        contradiction.
Qed.



Lemma filterNotIn (l l' : list nat) (x p : nat) :
  ~(In x (filter (fun a : nat => negb (divides p a)) l)) ->
    ~(In x l /\ (negb (divides p x)) = true).
Proof.
intros. unfold not. intros. rewrite filter_In in H. contradiction.
Qed.


Theorem newSieveHelperCorrect m n p l :
  I m n (p :: l) -> I (hd (S m) (sieveHelper p l)) n (sieveHelper p l).
Proof.
intros.
unfold I in *.
destruct H as [Hprime [Hsound [Hcomplete [Hsorted [Hbound Hmeqp]]]]].
case_eq (sieveHelper p l). 
{ intros. unfold hd in H0. rewrite <- Hmeqp in *.
  assert (m < x <= n) by lia.
  assert (prime x \/ ~ prime x) by apply classic.
  destruct H2.
  { apply Hcomplete in H1.
    assert (~(In x (sieveHelper m l))). 
    { rewrite H. intuition. }
    unfold sieveHelper in H3. rewrite filter_In in H3. 
    apply not_and_or in H3.
    destruct H3.
    { contradiction. }
    { apply eq_true_negb_classical in H3. assert (m <> x) by lia. 
      unfold prime in H2. destruct H2. apply dividesSame2 in H3. 
      apply H5 in H3.
      { intuition. }
      { apply prime_2_or_more in Hprime. lia. } }
      { exact H2. } } exact H2. }
 intros p' l' Hsieve. split.
* assert (In p' (p' :: l')). 
  { intuition. } 
  rewrite <- Hsieve in H. apply filter_In in H. 
  destruct H. apply negb_true_iff in H0.
  rewrite <- not_true_iff_false in H0. 
  rewrite <- divideSame in H0.
  apply p'Prime with (p := p).
  split. { exact Hprime. }
  split. { apply H0. }
  split. { apply sortedHelperNoDup2 with l. 
           { exact Hsorted. } 
            { exact H. } }
  split. 
  { unfold not in *. intros. 
    assert (p < q < p' -> (prime q) -> In q l).
        { intros. apply Hcomplete. 
          { unfold prime in H2. destruct H2.
            assert (p' <= n). 
            { apply Hbound. intuition. } 
            lia. }
          { apply H2. } }
    assert (In q l) by intuition.
    assert (StronglySorted lt (p' :: l')).
    { rewrite <- Hsieve. unfold sieveHelper. 
      apply filterPreservesSortedness with 
      (P := lt) (f := (fun a : nat => negb (divides p a))).
      apply StronglySorted_inv in Hsorted. intuition. }
    assert (~(In q (p' :: l'))).
    { apply SortedNotIn. split.
      { lia. }
      { exact H5. } }
    assert (p | q).
    { unfold sieveHelper in Hsieve. rewrite divideSame. 
      exfalso. unfold not in H6. apply H6. rewrite <- Hsieve. 
      rewrite filter_In. split. 
      { exact H4. }
      { assert (p >=2). { apply prime_2_or_more in Hprime. lia. } 
        unfold prime in H2. destruct H2. rewrite negb_true_iff.
        rewrite <- divideSameOther.
        { unfold not. intros. apply H8 in H9. 
          unfold prime in Hprime. 
          { lia. } 
          { lia. } }
        { apply divideSame. } } }
    assert (p >= 2).
    { apply prime_2_or_more in Hprime. lia. }
    unfold prime in H2. destruct H2.
    apply H9 in H7. unfold prime in Hprime. lia. lia. } 
  split. { unfold not. intros. unfold prime in Hprime. 
           destruct Hprime. apply H4 in H2. lia. lia. }
  intros. apply Hsound.
  { lia. }
  { exact H. }
* split.
  -- unfold not. intros.
     destruct H.
     assert (In y (p' :: l')).
     { intuition. }
     rewrite <- Hsieve in H3. unfold sieveHelper in H3.
     rewrite filter_In in H3. 
     destruct H3. apply negb_true_iff in H4. 
     rewrite <- divideSameOther in H4.
     assert (1 < x' < p \/ x' = p \/ p < x' < p') by lia.
     destruct H5.
     { unfold not in Hsound. apply Hsound with x' y.
       { lia. }
       { exact H3. }
       { exact H1. } }
     destruct H5.
     { subst. contradiction. }
      assert (StronglySorted lt (p':: l')). {
        rewrite <- Hsieve. unfold sieveHelper. 
        apply filterPreservesSortedness with 
          (P := lt) (f := (fun a : nat => negb (divides p a))).
        apply StronglySorted_inv in Hsorted. intuition.
       }
      assert (~(In x' (p' :: l'))). { 
        assert (StronglySorted lt (p' :: l')). { 
        rewrite <- Hsieve. unfold sieveHelper. 
        apply filterPreservesSortedness with 
          (P := lt) (f := (fun a : nat => negb (divides p a))).
        apply StronglySorted_inv in Hsorted. intuition.
        }
        apply SortedNotIn. intuition. 
      }
      rewrite <- Hsieve in H7.
      pose proof filter_In as filterhelp. 
      apply not_iff_compat with 
        (A := In x' (filter (fun a : nat => negb (divides p a)) l)) 
          in filterhelp.
      apply filterhelp in H7.
      apply not_and_or in H7. destruct H7.
      { assert (p' <= n).
      { apply Hbound. 
        assert (incl (filter (fun a : nat => negb (divides p a)) l) l)
          by apply incl_filter. 
        unfold sieveHelper in Hsieve. 
        rewrite Hsieve in H8. intuition. }
      assert (~(prime x')).
      { unfold not. intros. assert (p < x' <= n) by lia. 
        apply Hcomplete in H10. contradiction. exact H9. }
      assert (~(prime y)).
      { unfold not. intros. unfold prime in H10.
        destruct H10. apply H11 in H1. subst. contradiction. lia. }
      assert (y <= n).
      { apply Hbound. 
        assert (incl (filter (fun a : nat => negb (divides p a)) l) l) 
          by apply incl_filter. 
        unfold sieveHelper in Hsieve. 
        rewrite Hsieve in H11. intuition. }
      clear filterhelp.
      assert ((p' >= 2*p) \/ (p' < 2*p)) by lia.
      destruct H12.
      ++ assert (forall q, p < q < (2*p) -> ~(prime q)).
         { unfold not. intros.
            assert (forall q : nat, p < q < p' -> ~ prime q).
            { unfold not in *. intros. 
              assert (p < q < p' -> (prime q) -> In q l).
              { intros. apply Hcomplete. 
                { unfold prime in H18. destruct H18.
                  assert (p' <= n). { 
                  apply Hbound. 
                  assert (In p' (p' :: l')). 
                  { intuition. } 
                  rewrite <- Hsieve in H20.
                  unfold sieveHelper in H20. 
                  rewrite filter_In in H20. intuition. }
                  lia.
                }
                exact H18.
              }
            assert (In q l) by intuition.
            assert (StronglySorted lt (p' :: l')).
            { rewrite <- Hsieve. unfold sieveHelper. 
              apply filterPreservesSortedness 
                with (P := lt) (f := (fun a : nat => negb (divides p a))).
              apply StronglySorted_inv in Hsorted. intuition. }
            assert (~(In q (p' :: l'))).
            { apply SortedNotIn. split.
              { lia. }
              { exact H19. } }
            assert (p | q).
            { unfold sieveHelper in Hsieve. rewrite divideSame. 
              exfalso. unfold not in H20. apply H20. rewrite <- Hsieve. 
              rewrite filter_In. split. 
              { exact H18. }
              { assert (p >=2). { apply prime_2_or_more in Hprime. lia. } 
                unfold prime in H14. destruct H16. rewrite negb_true_iff.
                rewrite <- divideSameOther.
                { unfold not. intros. apply H14 in H23. 
                  unfold prime in Hprime. lia. lia. }
                { apply divideSame. } } }
            assert (p >= 2). 
            { apply prime_2_or_more in Hprime. lia. } 
            unfold prime in H14. destruct H14.
            apply H23 in H21. unfold prime in Hprime. lia. lia. }
            unfold not in H15. 
            apply H15 with q. lia. exact H14.
         }
         assert ((~(exists q, p < q < (2 * p) /\ prime q))).
         { unfold not. intros. destruct H14.
           destruct H14. unfold not in H13. 
           apply H13 with x. exact H14. exact H15. }
         apply not_ex_all_not with (n := p') in H14.
         assert (exists p', prime p' /\ p < p' < 2 * p).
         { apply Bertrand. apply p'. apply prime_2_or_more in Hprime. lia. }
         destruct H15.
         destruct H15.
         apply H13 in H16.
         contradiction.
      ++ unfold prime in H9.
      assert (forall z, (z | x') /\ z < x' -> 1 <= z < p).
      { intros. assert (x' <> z) by lia. 
        assert (z = 0 \/ z = 1 \/ 1 < z < p \/ z >= p) by lia.
        destruct H15.
        { subst. destruct H13. unfold divide in H13. inversion H13. lia. }
        destruct H15.
        { lia. }
        destruct H15.
        { lia. }
        { apply prime_2_or_more in Hprime.
          destruct H13.
          assert (z = p \/ z > p) by lia.
          destruct H17.
          { subst. apply Nat.divide_trans with p x' y in H13. 
            { contradiction. }
            { exact H1. } }
          assert (z <> p) by lia.
          assert (exists t, z = p + t).
          { apply existsA. lia. }
          assert (exists r, x' = p + r).
          { apply existsA. lia. }
          destruct H19. destruct H20.
          subst.
          assert (~((p + x) | (p + x0))).
          { apply noDivisorBetweenPand2P.
            { lia. }
            { lia. } }
          contradiction.
          } } 
          assert (~(prime x')).
          unfold not. intros.
          { assert (p < x' <= n) by lia.
            apply Hcomplete in H15. contradiction. exact H14. }
          unfold prime in H14. apply not_and_or in H14.
          destruct H14. 
          { assert (x' = 1) by lia. subst. lia. }
          assert (1 < x') by lia.
          apply divides_prime_divides in H15.
          destruct H15. destruct H15.
          assert (x < x' \/ x = x' \/ x > x') by lia.
          destruct H17.
          { assert ((x | x') /\ (x < x')) by intuition. apply H13 in H18.
            apply divides_trans with x x' y in H16.
            assert (x > 1). 
            { apply prime_2_or_more in H15. lia. }
          assert (x < p /\ x > 1) by lia. apply Hsound with x y in H20.
          contradiction. intuition. exact H1. }
          destruct H17.
          { assert (~(prime x')).
            unfold not. intros.
            { assert (p < x' <= n) by lia.
              apply Hcomplete in H19. contradiction. exact H18. } 
            subst. contradiction. }
          assert (0  < x') by lia.
          apply NPeano.Nat.divide_pos_le with x x' in H18.
          { lia. }
          { exact H16. } }
          { apply eq_true_negb_classical in H7. 
            apply divideSame in H7.
            apply Nat.divide_trans with p x' y in H7.
            2: { intuition. }
            contradiction. }
          apply divideSame.
  -- split. 
    ** intros. unfold sieveHelper in H. 
       apply NoPrimeDeleted with l p p' n; auto. 
        { apply Hcomplete. 
          { intuition. apply pSmaller with p' l l'; intuition. 
          } intuition. }
    ** split. 
      ++ unfold sieveHelper in Hsieve. rewrite <- Hsieve. 
         apply filterPreservesSortedness.
         apply StronglySorted_inv in Hsorted. intuition.
      ++ split. 
          +++ intros. apply Hbound.
            unfold sieveHelper in Hsieve.
            rewrite <- Hsieve in H. rewrite filter_In in H. 
            destruct H. 
            intuition.
          +++ intuition.
Qed.


Definition P (m n : nat) (l : list nat) : Prop := 
  (forall x, In x l <-> prime x /\ m <= x <= n) /\
  StronglySorted lt l.

Lemma filter_length {A} (f : A -> bool) l :
  length (filter f l) <= length l.
Proof.
  induction l; simpl; [reflexivity|].
  destruct (f a); simpl; lia.
Qed.

Lemma sieve_helper_length n l :
  length (sieveHelper n l) <= length l.
Proof. apply filter_length. Qed.

Lemma P_cons m' n p l :
  p < m' -> p <= n ->
  prime p ->
  (forall m, p < m < m' -> ~prime m) ->
  P m' n l ->
  P p n (p :: l).
Proof.
  intros ?? Pprime Hnotprime (Hin_prime&?). split.
  { intros x. simpl. split.
    - intros [->|Hin].
      + split; [assumption|]. lia.
      + apply Hin_prime in Hin as [??]. split; [assumption|]. lia.
    - intros [Hx ?]. assert (p = x \/ p <> x) as [?|?] by lia.
      + left. assumption.
      + right. apply Hin_prime. split. assumption.
        split; [|lia].
        assert (m' <= x \/ x < m') as [?|?] by lia; [assumption|].
        destruct (Hnotprime x). lia. assumption. }
   { constructor; [assumption|]. apply Forall_forall. intros x Hx.
     apply Hin_prime in Hx. lia. }
Qed.


Theorem siever_correct m n s2 l: 
  n >= 2 -> I m n l -> length l <= s2 -> P m n (siever s2 l).
Proof.
revert l m.
induction s2.
- intros. simpl. inversion H1.
  rewrite length_zero_iff_nil in H3.
  subst. simpl in H0.
  unfold P.
  split.
  + split. 
    { intros. inversion H2. }
    { intros. destruct H2. apply H0 in H3. contradiction. }
  + constructor.
- intros. destruct l.
  + unfold P. split.
    * split.
      { unfold In. apply except. }
      { intros. unfold I in H0. destruct H2.
        apply H0 in H3. contradiction. }
    * constructor.
  + assert (H0' := H0). 
    simpl in *. 
    assert (I (hd (S m) (sieveHelper n0 l) ) n (sieveHelper n0 l)).
    { apply newSieveHelperCorrect. exact H0. }
    assert (H2':=H2).
    apply IHs2 in H2.
    3:{ etransitivity. apply sieve_helper_length. lia. }
    2:{ lia. }
    destruct H0 as (?&?&?&?&?&->).
    apply (P_cons (hd (S n0) (sieveHelper n0 l))); [..|assumption| |assumption].
    assert (StronglySorted lt (n0 :: (sieveHelper n0 l))).
    { unfold sieveHelper. apply filterPreservesSortednessCons. auto. }
    { destruct (sieveHelper n0 l). { simpl. lia. }
      simpl. apply StronglySorted_inv in H7. 
      destruct H7. apply Forall_inv in H8. auto. }
    auto.
    unfold not. intros.
    assert (StronglySorted lt (n0 :: (sieveHelper n0 l))).
    { unfold sieveHelper. apply filterPreservesSortednessCons. auto. }
    destruct (sieveHelper n0 l) as [|n1 l0] eqn:?. 
    ++ simpl in *. assert (n0 = m \/ S n0 = m) by lia.
      destruct H10.
      { subst. inversion H8. lia. }
      { subst. lia. }

    ++ simpl in H8. unfold I in H2'.
       assert (forall y : nat, In y (n1 :: l0) -> y <= n) by intuition.
       assert (n1 <= n). { apply H10. intuition. }
       assert (n0 < m <= n) by lia.
       apply H4 in H12.
       2: { auto. }
       destruct H0'. destruct H14. destruct H15.
       unfold P in H2. destruct H2.
       unfold sieveHelper in Heql0.
       destruct H2'. destruct H19. destruct H20. destruct H21.
       assert (~(In m (n1 :: l0))).
       { apply SortedNotIn. split.
         { lia. }
         { auto. } }
       rewrite <- Heql0 in H23.
       pose proof filter_In.
       eapply not_iff_compat in H24.
       apply H24 in H23. unfold not in H23. apply H23. intros.
       split. { auto. } assert (n0 <> m) by lia.
       unfold prime in H8. apply negb_true_iff.
       destruct H8. assert (n0 <> 1).
       { unfold prime in H0. lia. }
       assert (Divides.divides n0 m \/ ~(Divides.divides n0 m)) 
         by apply classic.
       destruct H28.
       apply H26 in H28. lia. lia.
       apply divideSameOther in H28. auto.
       apply divideSame.
Qed.

Theorem primesUpToNCorrect n :
  n >= 2-> P 2 n (primesUpToN n).
Proof.
intros.
unfold primesUpToN.
apply siever_correct; auto.
  + apply IgetListOfN. intuition.
  + unfold getListOfN. rewrite seq_length. lia.
Qed.
