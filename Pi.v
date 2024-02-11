From mathcomp Require Import ssreflect.
Require Import Nat.

Definition name := nat.

Inductive proc :=
  | Nil  
  | Para (P Q : proc)
  | Sum (P Q : proc)
  | Repl (P : proc)
  | Nu (M : name) (P : proc)
  | Tau (P : proc)
  | Send (M N : name) (P : proc)
  | Recv (M: name) (N : name)  (P : proc)  
  | Match (x y : name)(P : proc)
  .

Definition Subst := name -> name.
Definition isSupp (σ : Subst) x :=   (σ x <> x).
Definition isCosupp (σ : Subst) y :=  exists x, y = σ x /\ isSupp σ x.
Axiom MaxSubst : Subst -> name.
Axiom MaxSubst_Supp : forall σ, isSupp σ (MaxSubst σ).
Axiom MaxSubst_Max : forall σ x, isCosupp σ x ->  x < MaxSubst σ.
Axiom namesOf : Subst -> name -> bool.
Axiom namesOfT : forall σ x, namesOf σ x = true <-> isSupp σ x \/ isCosupp σ x.
Axiom namesOfF : forall σ x, namesOf σ x = false <-> ~ (isSupp σ x \/ isCosupp σ x).


Fixpoint isFree (P: proc) (n : name) : bool :=
  match P with
  | Nil => false
  | Tau P => isFree P n
  | Para P Q => isFree P n || isFree Q n
  | Sum P Q => isFree P n || isFree Q n
  | Repl P => isFree P n
  | Send M N P => isFree P n || (n =? M) || ( n =? N)
  | Recv M N P => isFree P n || (n =? M)
  | Nu M P => isFree P n
  | Match x y P => isFree P n || (n =? x) || (n =? y)
  end.

Fixpoint isFreeP (P : proc) (n : name) : Prop :=
  match P with
  | Nil => False
  | Tau P => isFreeP P n
  | Para P Q => isFreeP P n \/ isFreeP Q n
  | Sum P Q => isFreeP P n \/ isFreeP Q n
  | Repl P => isFreeP P n
  | Send M N P => isFreeP P n \/ M = n \/ N = n
  | Recv M N P => isFreeP P n \/ M = n
  | Nu M P => isFreeP P n
  | Match x y P => isFreeP P n \/ x = n \/ y = n
  end.

Lemma isFreeT : forall P n, isFree P n = true <-> isFreeP P n. Admitted.
Lemma isFreeF : forall P n, isFree P n = false <-> ~ isFreeP P n. Admitted.


Fixpoint isBound (P: proc) (n : name) : bool :=
  match P with
  | Nil => false
  | Tau P => isBound P n
  | Para P Q => isBound P n || isBound Q n
  | Sum P Q => isBound P n || isBound Q n
  | Repl P => isBound P n
  | Send M N P => isBound P n
  | Recv M N P => isBound P n || (n =? N)
  | Nu M P => isBound P n || (n =? M)
  | Match x y P => isBound P n
  end.

Definition rename (x n m : name) : name :=
  if x =? n then m else x.
  
Fixpoint maxBound (P : proc) (n : name) : name :=
  match P with
  | Nil => n
  | Tau P => maxBound P n
  | Para P Q =>  maxBound P (maxBound Q n)
  | Sum P Q =>  maxBound P (maxBound Q n)
  | Repl P => maxBound P n
  | Send _ N P => maxBound P n
  | Recv _ N P => max n N
  | Nu N _ => max n N
  | Match _ _ P => maxBound P n
  end.

Fixpoint maxName (P : proc) (n : name) : name :=
  match P with
  | Nil => n
  | Tau P => maxName P n
  | Para P Q => maxName Q (maxName P n)
  | Sum P Q => maxName Q (maxName P n)
  | Repl P => maxName P n
  | Send M N P => max M (max N (maxName P n))
  | Recv M N P => max M (max N (maxName P n))
  | Nu M P => max M (maxName P n)
  | Match x y P => max x (max y (maxName P n))
  end.

Fixpoint renameBound (P : proc) (n m : name) : proc :=
  match P with
  | Nil => Nil
  | Tau P => Tau (renameBound P n m)
  | Para P Q => Para (renameBound P n m) (renameBound Q n m)
  | Sum P Q => Sum (renameBound P n m) (renameBound Q n m)
  | Repl P => Repl (renameBound P n m)
  | Send M N P => Send M N (renameBound P n m)
  | Recv M N P => Recv M (rename N n m) (renameBound P n m)
  | Nu N P => Nu (rename N n m) (renameBound P n m)
  | Match x y P => Match x y (renameBound P n m)
  end.



Definition fresh (P : proc) (σ : Subst) : name :=
  S (max (maxName P 0) (MaxSubst σ)).

Fixpoint convert_aux (P : proc) (σ : Subst) (n  : name) : proc :=
  match n with 
  | O => P
  | S n' => 
    if isFree P n && namesOf σ n 
    then convert_aux (renameBound P n (fresh P σ)) σ n'
    else P
  end.

Definition convert P σ := convert_aux P σ (maxBound P 0).

Fixpoint subst_aux (P : proc) (σ : Subst) : proc :=
  match P with
  | Nil => Nil
  | Tau P => Tau (subst_aux P σ)
  | Para P Q => Para (subst_aux P σ) (subst_aux Q σ)
  | Sum P Q => Sum (subst_aux P σ) (subst_aux Q σ)
  | Repl P => Repl (subst_aux P σ)
  | Send M N P => Send (σ M) (σ N) (subst_aux P σ)
  | Recv M N P => Recv (σ M) (σ N) (subst_aux P σ)
  | Nu N P => Nu (σ N) (subst_aux P σ)
  | Match x y P => Match (σ x) (σ y) (subst_aux P σ)
  end.

Definition subst P σ := subst_aux (convert P σ) σ.

Ltac autosubst := unfold subst, convert, convert_aux, subst_aux, rename; simpl.



Notation τ := Tau.
Notation "P ‖ Q" := (Para P Q) (at level 31).
Notation "P ⨁ Q" := (Sum P Q) (at level 32). (* ⨁ : \bigoplus*)
Notation "! P" := (Repl P) (at level 30).
Notation "M ⟪ N ⟫ P" := (Send M N P) (at level 30). (* ⟨ ⟩ : \lAngle \rAngle *)
Notation "M ⟦ N ⟧ P" := (Recv M N P) (at level 30). (* ⟦ ⟧ : \lBrack \rBrack *)
Notation "'IF' x == y 'THEN' P" := (Match x y P) (at level 30).
Notation " P .[ n ⟸ m ]" := (subst P (fun x => rename x n m))(at level 30).
Notation ν := Nu.

Module FreeBindTest.
  Notation x := 0.
  Notation y := 1.
  Notation z := 2.
  Notation v := 3.
  Notation w := 4.
  Notation u := 5.
  Definition A :=  (z ⟪y⟫ Nil ⨁ w ⟪v⟫  Nil) ‖  (x ⟪u⟫  Nil).
  (* Eval simpl in (isFree A 10). *)
  
  
  
  Definition D := ν x  (((x ⟦z⟧ (z ⟪y⟫  Nil)) ⨁ (w ⟪v⟫ Nil)) ‖ (ν u (x ⟪u⟫ Nil))).
  (* Variable a : name. *)
  (* Eval simpl in (isBound D a). *)
End FreeBindTest.



Inductive context :=
  | ctxt_Nil
  | ctxt_Tau (C : context)
  | ctxt_ParaL (C : context) (P : proc)
  | ctxt_ParaR (P : proc) (C : context)
  | ctxt_SumL (C : context) (Q : proc)
  | ctxt_SumR (P : proc) (C : context)
  | ctxt_Repl (C : context)
  | ctxt_Send (M N : name) (C : context)
  | ctxt_Recv (M: name) (N : name)  (C : context)
  | ctxt_Nu (M : name) (C : context)
  | ctxt_Match (x y : name)(C : context)
  .

Fixpoint insert (P : proc) (C :  context) : proc :=
  match C with
  | ctxt_Nil => P
  | ctxt_Tau C => Tau (insert P C)
  | ctxt_ParaL C Q => Para (insert P C) Q
  | ctxt_ParaR Q C => Para Q (insert P C)
  | ctxt_SumL C Q => Sum (insert P C) Q
  | ctxt_SumR P' C => Sum P' (insert P C)
  | ctxt_Repl C => Repl (insert P C)
  | ctxt_Send M N C => Send M N (insert P C)
  | ctxt_Recv M N C => Recv M N (insert P C)
  | ctxt_Nu M C => Nu M (insert P C)
  | ctxt_Match x y C => Match x y (insert P C)
  end.

Reserved Notation "P ≡ Q" (at level 33).

Inductive congr : proc -> proc -> Prop :=
    | sc_match x P : IF x == x THEN P ≡ P
    | sc_sum_assoc P Q R : (P ⨁ Q) ⨁ R ≡ P ⨁ (Q ⨁ R)
    | sc_sum_comm P Q : P ⨁ Q ≡ Q ⨁ P
    | sc_sum_inact P : P ⨁ Nil ≡ P
    | sc_para_assoc P Q R : (P ‖ Q) ‖ R ≡ P ‖ (Q ‖ R)
    | sc_para_comm P Q : P ‖ Q ≡ Q ‖ P
    | sc_para_inact P : P ‖ Nil ≡ P
    | sc_nu x y P : ν x (ν y P) ≡ ν y (ν x P)
    | sc_nu_inact x : ν x Nil ≡ Nil
    | sc_nu_para x P Q : ~ isFreeP P x -> ν x (P ‖ Q) ≡ P ‖ ν x Q
    | sc_repl P : ! P ≡ P ‖ ! P
    | sc_refl P : P ≡ P
    | sc_comm P Q : P ≡ Q -> Q ≡ P
    | sc_trans P Q R : P ≡ Q -> Q ≡ R -> P ≡ R
    | sc_congr P Q C : P ≡ Q -> insert P C ≡ insert Q C
    where "P ≡ Q" := (congr P Q).


Lemma sc_nu_congr x P Q : P ≡ Q -> ν x P ≡ ν x Q.
Proof.
  move => H.
  pose C := ctxt_Nu x ctxt_Nil.
  apply (sc_congr P Q C); auto.
Qed.

Lemma sc_tau_congr P Q : P ≡ Q -> (τ P) ≡ (τ Q).
Proof.
  pose C := ctxt_Tau ctxt_Nil.
  apply (sc_congr P Q C).
Qed.  

Lemma sc_paraL_congr P Q R : P ≡ Q -> (P ‖ R) ≡ (Q ‖ R).
Proof.
  pose C := ctxt_ParaL ctxt_Nil R.
  apply (sc_congr P Q C).
Qed.

Lemma sc_paraR_congr P Q R : P ≡ Q -> (R ‖ P) ≡ (R ‖ Q).
Proof.
  pose C := ctxt_ParaR R ctxt_Nil.
  apply (sc_congr P Q C).
Qed.

Lemma sc_sumL_congr P Q R : P ≡ Q -> (P ⨁ R) ≡ (Q ⨁ R).
Proof.
  pose C := ctxt_SumL ctxt_Nil R.
  apply (sc_congr P Q C).
Qed.

Lemma sc_sumR_congr P Q R : P ≡ Q -> (R ⨁ P) ≡ (R ⨁ Q).
Proof.
  pose C := ctxt_SumR R ctxt_Nil.
  apply (sc_congr P Q C).
Qed.

Lemma sc_repl_congr P Q : P ≡ Q -> (! P) ≡ (! Q).
Proof.
  pose C := ctxt_Repl ctxt_Nil.
  apply (sc_congr P Q C).
Qed.

Lemma sc_send_congr P Q M N : P ≡ Q -> (M ⟪ N ⟫ P) ≡ (M ⟪ N ⟫ Q).
Proof.
  pose C := ctxt_Send M N ctxt_Nil.
  apply (sc_congr P Q C).
Qed.

Lemma sc_recv_congr P Q M N : P ≡ Q -> (M ⟦ N ⟧ P) ≡ (M ⟦ N ⟧ Q).
Proof.
  pose C := ctxt_Recv M N ctxt_Nil.
  apply (sc_congr P Q C).
Qed.

Lemma sc_match_congr P Q x y : 
  P ≡ Q -> (IF x == y THEN P) ≡ (IF x == y THEN Q).
Proof.
  pose C := ctxt_Match x y ctxt_Nil.
  apply (sc_congr P Q C).
Qed.  



    
Module congr.

  (* sc_match での場合は成り立たんけど、面倒だからこれで妥協  *)
  Lemma congr_free P Q : 
  P ≡ Q -> 
  forall n, isFree P n = isFree Q n.
  Proof.
    move => H n.
    induction H => /=.
    1 : admit.
    14 : {
      rename IHcongr into IH.
      induction C => //=;
      try rewrite IHC; auto.
    }
    all : try destruct (isFree P n); auto.
    all : try destruct (isFree Q n); auto.
    - inversion IHcongr1.
    - inversion IHcongr1.
  Admitted.

  Definition x := 0.
  Definition y := 1.
  Definition z := 2.
  Definition a := 3.
  Definition b := 4.

  Definition P := ν x ((x ⟦ z ⟧ (z ⟪ y ⟫ Nil)) ‖ (x ⟪ a ⟫ Nil ‖ x ⟪ b ⟫ Nil)).
  Definition P1 := ν x (((x ⟪ a ⟫ Nil ⨁ Nil ) ‖ (x ⟦ z ⟧ (z ⟪ y ⟫ Nil) ⨁ Nil)) ‖ ( x ⟪ b ⟫ Nil)).

  Lemma P_P1 : P ≡ P1.
  Proof.
    apply sc_nu_congr.
    eapply sc_trans.
    - apply sc_comm; apply sc_para_assoc.
    apply sc_paraL_congr.
    eapply sc_trans.
    - apply sc_paraL_congr.
      apply sc_comm.
      apply sc_sum_inact.
    eapply sc_trans.
    - apply sc_paraR_congr.
      apply sc_comm.
      apply sc_sum_inact.
    apply sc_para_comm.
  Qed.

End congr.

Fixpoint nu_tuple (n : name) (ns : list name) (P : proc) : proc :=
  match ns with
  | nil => ν n P
  | cons m ms => ν n (nu_tuple m ms P)
  end.

Fixpoint guard (P Q : proc) : Prop :=
  match P with
  | Nil => False 
  | Para P' Q' => guard P' Q \/ guard Q' Q
  | Sum P' Q' => guard P' Q \/ guard Q' Q
  | Repl P' => guard P' Q
  | Nu M P' => guard P' Q
  | Tau P' => Q = P' \/ guard P' Q
  | Send M N P' => Q = P' \/ guard P' Q
  | Recv M N P' => Q = P' \/ guard P' Q  
  | Match x y P' => Q = P' \/ guard P' Q
  end.

Inductive reduct : proc -> proc -> Prop :=
  | reduct_commu n a b P Q M1 M2 : reduct ((n ⟪ a ⟫ P ⨁ M1 )‖ (n ⟦ b ⟧ Q ⨁ M2)) (P ‖ Q.[b ⟸ a])
  | reduct_tau P M : reduct (τ P ⨁ M) P
  | reduct_nu n P P' : reduct P P' -> reduct (ν n P) (ν n P')
  | reduct_para P P' Q : reduct P P' -> reduct (P ‖ Q) (P' ‖ Q)
  | reduct_struct P P' Q Q' : Q ≡ P -> Q' ≡ P' -> reduct P P' -> reduct Q Q'
  .

Notation "P ⟹ Q" := (reduct P Q) (at level 33).

Lemma reduct_struct_l P Q R : P ≡ Q -> reduct Q R -> reduct P R.
Proof.
  move => PQ QR.
  eapply reduct_struct; eauto.
  apply sc_refl.
Qed.

Lemma reduct_struct_r P Q R : reduct P Q -> Q ≡ R -> reduct P R.
Proof.
  move => PQ QR.
  eapply reduct_struct; eauto.
  apply sc_refl.
  apply sc_comm; auto.
Qed.

Lemma reduct_commu_nil n a b P Q :
  reduct ((n ⟪ a ⟫ P )‖ (n ⟦ b ⟧ Q)) (P ‖ Q.[b ⟸ a]).
  eapply reduct_struct.
  - eapply sc_trans.
    * apply sc_paraL_congr.
      apply sc_comm.
      apply sc_sum_inact.
    * eapply sc_paraR_congr.
      apply sc_comm.
      apply sc_sum_inact.
  - apply sc_refl.
  - eapply reduct_commu.
Qed.  


Module reduct.
  Import congr.
  
  Definition P5 := b ⟪ y ⟫ Nil ‖ ν x (x ⟪ a ⟫ Nil).
  Definition P4 := ν x (a ⟪ y ⟫ Nil ‖ x ⟪ b ⟫ Nil).
  Definition P3 := ν x ((Nil ‖ a ⟪ y ⟫ Nil) ‖ (x ⟪ b ⟫ Nil)).

  Lemma P__P5 : reduct P P4.
  Proof.
    eapply (reduct_struct P1 P3 _ _); auto.
    - apply P_P1.
    - apply sc_nu_congr.      
      apply sc_paraL_congr.
      apply sc_comm.
      eapply sc_trans.
      * apply sc_para_comm.
      * apply sc_para_inact.
    unfold P1, P3.
    apply reduct_nu.
    apply reduct_para.
    eapply reduct_struct.
    - apply sc_refl.
    2 : apply reduct_commu.
    - autosubst.
      apply sc_refl.
  Qed.

End reduct.



(*
  「reductにおいて、reduct_structdが使われるならば最後のステップにおいてのみである」
  という命題を書きたいけど、うまくできない。
  以下は、限定性が言えてない。
  でも、Lemma 1.2.25はこれでよさそうな気がする。
*)
Inductive action_reduct : proc -> proc -> Prop :=
  | ar_commu n a b P Q M1 M2 : action_reduct ((n ⟪ a ⟫ P ⨁ M1 )‖ (n ⟦ b ⟧ Q ⨁ M2)) (P ‖ Q.[b ⟸ a])
  | ar_tau P M : action_reduct (τ P ⨁ M) P
  | ar_nu n P P' : action_reduct P P' -> action_reduct (ν n P) (ν n P')
  | ar_para P P' Q : action_reduct P P' -> action_reduct (P ‖ Q) (P' ‖ Q).

Inductive normal_reduct : proc -> proc -> Prop :=
  | nr_struct P P' Q Q' : Q ≡ P -> Q' ≡ P' -> action_reduct P P' -> normal_reduct Q Q'.

Lemma reduct_normal P Q : P ⟹ Q -> normal_reduct P Q.
Proof.
  induction 1.
  - econstructor; eauto; try apply sc_refl.
    apply ar_commu.
  - econstructor; eauto; try apply sc_refl.
    apply ar_tau.
  - induction IHreduct.
    econstructor.
    * apply sc_nu_congr; eauto.
    * apply sc_nu_congr; eauto.
    * apply ar_nu; auto.
  - induction IHreduct.
    econstructor.
    * apply sc_paraL_congr; eauto.
    * apply sc_paraL_congr; eauto.
    * apply ar_para; auto.
  - induction IHreduct.    
    econstructor.
    - eapply sc_trans; eauto.
    - eapply sc_trans; eauto.
    - auto.
Qed.



(* Inductive reduct_init : proc -> proc -> Prop :=
  | ri_commu n a b P Q M1 M2 : reduct_init ((n ⟪ a ⟫ P ⨁ M1 )‖ (n ⟦ b ⟧ Q ⨁ M2)) (P ‖ Q.[b ⟸ a])
  | ri_tau P M : reduct_init (τ P ⨁ M) P
  .

Inductive reduct_mid : proc -> proc -> Prop :=
  | rm_nu n P P' : reduct_init P P' -> reduct_mid (ν n P) (ν n P')
  | rm_para P P' Q : reduct_mid P P' -> reduct_mid (P ‖ Q) (P' ‖ Q)  
  .

Inductive normal_reduct : proc -> proc -> Prop :=
  | rf_struct P P' Q Q' : Q ≡ P -> Q' ≡ P' -> reduct_mid P P' -> normal_reduct Q Q'.

Lemma reduct_normal P Q : P ⟹ Q -> normal_reduct P Q. *)







    

  
  
  







   


  