Require Import Pi.
Require Import Bool.
Require Import Nat.

Inductive action : Type :=
  | ASend (x y : name)
  | ARecv (x y : name)
  | AFresh (x z : name)
  | ATau.


Definition isFreeA (a : action) (n : name) : Prop :=
  match a with
  | ASend x y => (x = n) \/ (y = n)
  | ARecv x y => (x = n) \/ (y = n)
  | AFresh x z => (x = n) 
  | ATau => False
  end.

Definition isBindA (a : action) (n : name) : Prop :=
  match a with
  | AFresh _ z => (z = n)
  | _ => False
  end.



Notation "x ⟨ y ⟩" := (ASend x y) (at level 30). (* ⟨ ⟩ : \lAngle \rAngle *)
Notation "x [ y ]" := (ARecv x y) (at level 30). (* ⟦ ⟧ : \lBrack \rBrack *)

Inductive lts : action -> proc -> proc -> Prop :=
  | lts_out x y P : lts (x ⟨ y ⟩) (x ⟪ y ⟫ P) P
  | lts_inp x y z P : lts (x [ y ]) (x ⟦ z ⟧ P) (P.[z ⟸ y])
  | lts_tau P : lts ATau (τ P) P
  | lts_match x a P P' : lts a P P' -> lts a (IF x == x THEN P) P
  | lts_sum a P P' Q : lts a P P' -> lts a (P ⨁ Q) P'
  | lts_para a P P' Q : (~ exists n, ((isBindA a n) /\ (isFreeP Q n)) ) ->  
      lts a P P' -> lts a (P ‖ Q) (P' ‖ Q)
  | lts_comm x y P P' Q Q' : 
      lts (x ⟨ y ⟩) P P' -> lts (x [ y ]) Q Q' -> lts ATau (P ‖ Q) (P' ‖ Q')
  | lts_close x z P P' Q Q' : ~ isFreeP Q z -> 
      lts (AFresh x z) P P' -> lts (x [ z ]) Q Q' -> lts ATau (P ‖ Q) (ν z (P' ‖ Q'))
  | lts_open x z P P' : z <> x -> lts (x ⟨ z ⟩) P P' -> lts (AFresh x z) (ν z P) P'
  | lts_nu a z P P' : ~ isFreeA a z -> ~ isBindA a z -> 
      lts a P P' -> lts a (ν z P) (ν z P')  
  | lts_nu_act a P P' : lts a P P' -> lts a (! P) (P' ‖ ! P)
  | lts_nu_comm x y P P' P'' : 
      lts (x ⟨ y ⟩) P P' -> lts (x [ y ]) P P'' -> lts ATau (! P) ((P' ‖ P'') ‖ !P)
  | lts_nu_close x z P P' P'' : ~isFreeP P z ->
      lts (AFresh x z) P P' -> lts (x [ z ]) P P'' -> lts ATau (! P) ((ν z (P' ‖ P'')) ‖ !P)
  .


Module Exercise.

  Definition x := 0.
  Definition y := 1.
  Definition z := 2.
  Definition w := 3.
  Definition v := 4.

  Definition Q := x ⟪ y ⟫ (y ⟪ y ⟫ Nil) ⨁ x ⟦ z ⟧ (z ⟦ w ⟧ Nil).
  Definition P := ! (ν y Q).
  Definition P' := ν y (y ⟪ y ⟫ Nil ‖ ν v (y ⟦ w ⟧ Nil)) ‖ P.

  Goal P ⟹ P'.
  Proof.
  Abort.
End Exercise.

Lemma eq_refl (x : nat) : x =? x = true.
Proof. induction x; auto. Qed.

Lemma eqP x y : 
  ((x =? y) = true -> x = y) /\
  ((x =? y) = false -> x <> y).
Proof.
  move : y.
  induction x => y; destruct y => //=.
  move : (IHx y) => [IHT IHF].
  split => H; auto.
Qed.


Section ltsFree.

  Lemma ASend_free x y P P' : lts (x ⟨ y ⟩) P P' -> 
    isFreeP P x /\ isFreeP P y /\ (forall n,  isFreeP P' n ->  isFreeP P n).
  Proof.
    move : P'.
    induction P => P' H; inversion H; simpl; subst.
    - move : (IHP1 _ H5) => [HP1 [HP2 Hn]].
      repeat split; [left|left|]; auto.
      move => n [H0|H0]; auto.
    - move : (IHP1 _ H4) => [HP1 [HP2 Hn]].
      repeat split; [left|left|]; auto.
    - move : (IHP _ H2) => [HP1 [HP2 Hn]].
      repeat split; auto.
      move => n [H0|H0]; eauto.
    - move : (IHP _ H6) => [HP1 [HP2 Hn]].
      repeat split; auto.
    - repeat split; auto.
    - move : (IHP _ H5) => [HP1 [HP2 Hn]].
      repeat split; auto.
  Qed.

  Lemma ARecv_free x y P P' : lts (x [ y ]) P P' -> 
    (isFreeP P x ) /\ (forall n, (isFreeP P' n) -> ((isFreeP P n) \/ n = y )).
  Proof.
    move : P'.
    induction P => P' H; inversion H; simpl; subst.
    - move : (IHP1 _ H5) => [HP Hn].
      split; auto.
      move => n [H0|H0]; eauto.
      move : (Hn n H0) => [H1|H1]; eauto.
    - move : (IHP1 _ H4) => [HP Hn].
      split; auto.
      move => n H0.
      move : (Hn n H0) => [H1|H1]; eauto.
    - move : (IHP _ H2) => [HP Hn].
      split; auto.
      move => n [H0|H0]; eauto.
    - move : (IHP _ H6) => [HP Hn].
      split; auto.
    { split; auto.
      clear.
      induction P => //= n H.
      - destruct H as [H|H].
        * move : (IHP1 _ H) => [[H1 | H1] |H1]; eauto.
        * move : (IHP2 _ H) => [[H1 | H1] |H1]; eauto.
      - destruct H as [H|H].
        * move : (IHP1 _ H) => [[H1 | H1] |H1]; eauto.
        * move : (IHP2 _ H) => [[H1 | H1] |H1]; eauto.
      - destruct H as [H|[H|H]].
        * move : (IHP _ H) => [[H1 | H1] |H1]; eauto.
        * subst n.
          unfold rename; destruct (M0 =? N); eauto.
        * subst n.
          unfold rename; destruct (N0 =? N); eauto.
      - destruct H as [H|H].
        * move : (IHP _ H) => [[H1 | H1] |H1]; eauto.
        * subst n.
          unfold rename; destruct (M0 =? N); eauto.
      - destruct H as [H|[H|H]].
        * move : (IHP _ H) => [[H1 | H1] |H1]; eauto.
        * subst n.
          unfold rename; destruct (x =? N); eauto.
        * subst n.
          unfold rename; destruct (y0 =? N); eauto.
    }
    {
      move : (IHP _ H5) => [HP H0].
      split; eauto.
    }
  Qed.

  Lemma AFresh_free x y P P' : lts (AFresh x y) P P' -> 
    (isFreeP P x ) /\ (forall n, (isFreeP P' n) -> ((isFreeP P n) \/ n = y )).
  Proof.
    move : P'.
    induction P => P' H; inversion H; simpl; subst.
    - move : (IHP1 _ H5) => [HP Hn].
      split; auto.
      move => n [H0|H0]; eauto.
      move : (Hn n H0) => [H1|H1]; eauto.
    - move : (IHP1 _ H4) => [HP Hn].
      split; auto.
      move => n H0.
      move : (Hn n H0) => [H1|H1]; eauto.
    - move : (IHP _ H2) => [HP Hn].
      split; auto.
      move => n [H0|H0]; eauto.
    - move : (ASend_free _ _ _ _ H6) => [H1 [H2 H3]]; split; auto.
    - move : (IHP _ H6) => [HP Hn].
      split; auto.
    - move : (IHP _ H5) => [HP H0].
      split; eauto.
  Qed.

  Lemma ATau_free P P' : lts ATau P P' -> 
    (forall n, (isFreeP P' n) -> (isFreeP P n)).
  Proof.    
    move : P'.
    induction P => P' H; inversion H; simpl; subst; eauto.
    - move => n [H0|H0]; [left|right]; eauto.
    - move :  (ASend_free _ _ _ _ H2) => [HP1x [HP1y HP1]].
      move :  (ARecv_free _ _ _ _ H3) => [HP2x HP2].
      move => n [HP|HP]; eauto.
      move : (HP2 n HP) => [HQ|HQ]; eauto.
      subst; eauto.
    - move :  (AFresh_free _ _ _ _ H3) => [HP1x HP1].
      move :  (ARecv_free _ _ _ _ H4) => [HP2x HP2].
      rename P1 into Q.
      rename P2 into R.
      rename Q' into R'.
      rename P'0 into Q'.
      move : (valid ((ν z (Q' ‖ R'))) z ) => /= F.
      move => n [HQ|HQ]; eauto.
      * move : (HP1 n HQ) => [H0|H0]; eauto.
        subst n.        
        contradiction F; auto.
      * move : (HP2 n HQ) => [H0|H0]; eauto.
        subst n.
        contradiction F; auto.
    - move => n [H0|H0]; eauto.
    - move :  (ASend_free _ _ _ _ H1) => [HP1x [HP1y HP1]].
      move :  (ARecv_free _ _ _ _ H2) => [HP2x HP2].
      move => n [[HP|HP]|HP]; eauto.
      move : (HP2 n HP) => [H0|H0]; subst; auto.
    - move :  (AFresh_free _ _ _ _ H2) => [HP1x HP1].
      move :  (ARecv_free _ _ _ _ H3) => [HP2x HP2].
      move : (valid (ν z (P'0 ‖ P'') ‖ ! P) z) => /= F.
      move => n [[HP|HP]|HP]; eauto.
      * move : (HP1 n HP) => [H0|H0]; subst; eauto.
        contradiction F; auto.
      * move : (HP2 n HP) => [H0|H0]; subst; eauto.
        contradiction F; auto.
  Qed.
      



          

      

   
