Require Import List.
Require Import Omega.

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  induction l; intros.
  - inversion H.
  - inversion H.
    + subst x. exists nil, l. reflexivity.
    + specialize (IHl H0). destruct IHl as [l1 [l2 A]].
      exists (a::l1), l2. subst l. reflexivity.
Qed.
  
Inductive repeats {X:Type} : list X -> Prop :=
| repeats_this:
    forall x l, In x l -> repeats (x :: l)
| repeats_other:
    forall x l, repeats l -> repeats (x :: l).

Lemma nth_error_hd:
  forall (X: Type) (l l': list X) (x: X),
    nth_error (l ++ x :: l') (length l) = Some x.
Proof.
  induction l; intros.
  - simpl. reflexivity.
  - simpl. eapply IHl; auto.
Qed.

Lemma to_list_nat:
  forall (X: Type) (l1 l2: list X),
    (forall x, In x l1 -> In x l2) ->
    exists l, map (nth_error l2) l = map (fun x => Some x) l1.
Proof.
  induction l1; intros.
  - exists nil; reflexivity.
  - generalize (IHl1 l2 (fun x Hin => H x (in_cons _ _ _ Hin))). intros [l A].
    generalize (H a (in_eq _ _)). intros B. generalize (in_split _ _ _ B). intros [hd [tl Heq]].
    exists (length hd :: l). simpl. rewrite A. f_equal.
    rewrite Heq. eapply nth_error_hd.
Qed.

Lemma repeats_in_nat_implies_repeats:
  forall (X: Type) (l: list nat),
    repeats l ->
    forall (l1 l2: list X), map (nth_error l2) l = map (fun x => Some x) l1 ->
                       repeats l1.
Proof.
  induction 1; intros.
  - simpl in H0. destruct l1; inversion H0. clear H0.
    constructor 1. generalize (in_map (nth_error l2) _ _ H). intros Hin.
    rewrite H3 in Hin. rewrite H2 in Hin. eapply in_map_iff in Hin.
    destruct Hin as [x1 [A N]]. inversion A; subst; auto.
  - simpl in H0. destruct l1; inversion H0. clear H0.
    constructor 2. eapply IHrepeats; eauto.
Qed.

Lemma not_in_app:
  forall (X: Type) (l1 l2: list X) (x: X),
    ~ In x (l1 ++ l2) ->
    ~ In x l1 /\ ~ In x l2.
Proof.
  intros; split; red; intros.
  - eapply H. eapply in_or_app. left; auto.
  - eapply H. eapply in_or_app. right; auto.
Qed.

Lemma not_in_cons:
  forall (X: Type) (l: list X) (x y: X),
    ~ In x (y::l) ->
    x <> y /\ ~ In x l.
Proof.
  unfold not; split; intros.
  - subst x; apply H; apply in_eq.
  - apply H; apply in_cons; auto.
Qed.

Lemma repeats_app:
  forall (X: Type) (l1 l2: list X) (x: X),
    In x l1 ->
    In x l2 ->
    repeats (l1 ++ l2).
Proof.
  induction l1; intros.
  - inversion H.
  - destruct H; try subst a.
    + simpl. constructor. eapply in_or_app. right; auto.
    + simpl. constructor 2. eapply IHl1; eauto.
Qed.

Lemma repeats_app_right:
  forall (X: Type) (l1 l2: list X),
    repeats l2 ->
    repeats (l1 ++ l2).
Proof.
  induction l1; intros; auto.
  simpl; constructor 2. apply IHl1; eauto.
Qed.

Lemma repeats_remove:
  forall (X: Type) (l1 l2: list X) (x: X),
    repeats (l1 ++ l2) ->
    repeats (l1 ++ x :: l2).
Proof.
  induction l1; intros.
  - simpl in H; simpl. constructor 2; auto.
  - simpl in H; inversion H; subst.
    + simpl. eapply in_app_or in H1; destruct H1.
      * constructor. eapply in_or_app. left; auto.
      * constructor. eapply in_or_app. right. right; auto.
    + eapply IHl1 in H1. simpl. constructor 2. eapply H1.
Qed.

Lemma repeats_permut_hd:
  forall (X: Type) (l: list X) (a b: X),
    repeats (a :: b :: l) ->
    repeats (b :: a :: l).
Proof.
  induction l; intros.
  - inversion H; subst.
    + destruct H1. subst.
      * constructor; eapply in_eq.
      * inversion H0.
    + inversion H1; subst.
      * inversion H2.
      * inversion H2.
  - inversion H; subst.
    + destruct H1.
      * subst. constructor; apply in_eq.
      * destruct H0.
        { subst a0. constructor 2. constructor; apply in_eq. }
        { constructor 2. constructor. right; auto. }
    + change (b :: a0 :: a :: l) with ((b :: nil) ++ a0 :: (a :: l)).
      apply repeats_remove. simpl. auto.
Qed.

Lemma repeats_permut:
  forall (X: Type) (l1 l2: list X) (a b: X),
    repeats (a :: l1 ++ b :: l2) ->
    repeats (b :: l1 ++ a :: l2).
Proof.
  induction l1; intros.
  - simpl in H. simpl.
    inversion H; subst.
    + destruct H1.
      * subst b. constructor. left; auto.
      * constructor 2. constructor; auto.
    + inversion H1; subst.
      * constructor. right; auto.
      * constructor 2. constructor 2; auto.
  - simpl in H. simpl. apply repeats_permut_hd in H. apply repeats_permut_hd.
    inversion H; subst.
    + destruct H1; subst.
      * constructor. right. apply in_or_app. right. left; auto.
      * apply in_app_or in H0. destruct H0.
        { constructor. right. apply in_or_app. left; auto. }
        { destruct H0; subst.
          - constructor; left; auto.
          - constructor. right. eapply in_or_app. right; right; auto. }
    + eapply IHl1 in H1. constructor 2. auto. 
Qed.

Lemma nth_error_Some X (l: list X) n : nth_error l n <> None <-> n < length l.
Proof.
  revert n. induction l; destruct n; simpl.
  - split; [now destruct 1 | inversion 1].
  - split; [now destruct 1 | inversion 1].
  - split; now auto with arith.
  - rewrite IHl; split; auto with arith.
Qed.

Lemma pigeonhole_nat':
  forall (m: nat) (l: list nat),
    2 <= length l < m ->
    (forall n, In n l -> n < length l - 1) ->
    repeats l.
Proof.
  induction m; intros.
  - destruct l; simpl in H; omega.
  - destruct l; simpl in H; try omega.
    destruct l; simpl in H; try omega.
    destruct l; simpl in H.
    + generalize (H0 n (in_eq _ _)). generalize (H0 n0 (in_cons _ _ _ (in_eq _ _))). simpl; intros.
      assert (n0 = 0) by omega. assert (n = 0) by omega; subst.
      constructor. eapply in_eq.
    + destruct (In_dec eq_nat_dec n (n0 :: n1 :: l)).
      * constructor; auto.
      * destruct (In_dec eq_nat_dec (S (length l)) (n0 :: n1 :: l)).
        { generalize (in_split _ _ _ i). intros [l1 [l2 A]].
          generalize (H0 n (or_introl eq_refl)). intros B.
          assert (n < S (length l)).
          - rewrite A in n2. apply not_in_app in n2. destruct n2.
            apply not_in_cons in H2. simpl in B; destruct H2; try omega.
          - destruct (In_dec eq_nat_dec (S (length l)) l1).
            + rewrite A. rewrite app_comm_cons. eapply repeats_app; auto.
              * right. apply i0.
              * apply in_eq.
            + destruct (In_dec eq_nat_dec (S (length l)) l2).
              { rewrite A. constructor 2. apply repeats_app_right; auto.
                constructor. auto. }
              { clear B. assert (HA: length (l1 ++ n :: l2) =length (l1 ++ S (length l) :: l2)).
                { rewrite ! app_length; simpl; auto. }
                assert (HB: 2 <= length (l1 ++ n :: l2) < m).
                { rewrite HA. rewrite <- A. simpl; try omega. }
                - generalize (IHm (l1 ++ n :: l2) HB). rewrite HA. rewrite ! A. intros HC.
                  assert (repeats (l1 ++ n :: l2)).
                  { apply HC. intros. eapply in_app_or in H2. destruct H2.
                    - rewrite <- A. simpl.
                      assert (n5 < S (S (length l))).
                      + apply H0. rewrite A. right. eapply in_or_app. left; auto.
                      + destruct (eq_nat_dec n5 (S (length l))); try congruence. omega.
                    - destruct H2.
                      + rewrite <- A; simpl; omega.
                      + assert (n5 < S (S (length l))).
                        * apply H0. rewrite A. right. eapply in_or_app. right. right; auto.
                        * destruct (eq_nat_dec n5 (S (length l))); try congruence. rewrite <- A; simpl. omega. }
                  eapply repeats_permut. constructor 2; auto. } }
        constructor 2. eapply IHm.
        { simpl; omega. }
        { intros. destruct H1; subst.
          - simpl. assert (n4 < S (S (length l))).
            { apply H0. right; left; auto. }
            apply not_in_cons in n3. destruct n3. omega.
          - destruct H1; subst.
            + simpl. assert (n4 < S (S (length l))).
              { apply H0. right; right; left; auto. }
              apply not_in_cons in n3. destruct n3. apply not_in_cons in H3; destruct H3. omega.
            + simpl. assert (n4 < S (S (length l))).
              { apply H0. right; right; right; auto. }
              apply not_in_cons in n3. destruct n3.
              apply not_in_cons in H4; destruct H4.
              destruct (eq_nat_dec n4 (S (length l))); try congruence; omega. }
Qed.

Lemma pigeonhole_nat:
  forall (l: list nat),
    2 <= length l ->
    (forall n, In n l -> n < length l - 1) ->
    repeats l.
Proof.
  intros; eapply pigeonhole_nat'; eauto.
Qed.

Theorem pigeonhole_principle:
  forall (X:Type) (l1 l2: list X),
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
  intros. generalize (to_list_nat _ _ _ H). intros [l A].
  eapply repeats_in_nat_implies_repeats; eauto.
  assert (length l = length l1).
  { erewrite <- (map_length (nth_error l2) l). rewrite A.
    apply map_length. }
  eapply pigeonhole_nat.
  - rewrite H1. destruct l1; simpl in H0; try omega.
    destruct l1; destruct l2; simpl in H0; try omega.
    + generalize (H x (in_eq _ _)). intro HA; inversion HA.
    + generalize (H x (in_eq _ _)). intro HA; inversion HA.
    + simpl; omega.
  - intros. rewrite H1.
    assert (n < length l2).
    { generalize (in_map (nth_error l2) _ _ H2). rewrite A. intros B.
      generalize (proj1 (in_map_iff _ _ _) B). intros [x [C D]].
      eapply nth_error_Some. rewrite <- C. congruence. }
    omega.
Qed.


