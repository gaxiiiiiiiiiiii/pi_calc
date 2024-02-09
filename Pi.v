From mathcomp Require Import ssreflect.
Require Import Nat.

Definition name := nat.

Inductive proc :=
  | Nil
  | Tau (P : proc)
  | Para (P Q : proc)
  | Sum (P Q : proc)
  | Repl (P : proc)
  | Send (M N : name) (P : proc)
  | Recv (M: name) (N : name)  (P : proc)
  | Nu (M : name) (P : proc)
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
  
Definition maxBound (P : proc) (n : name) : name :=
  match P with
  | Recv _ N P => max n N
  | Nu N _ => max n N
  | _ => n 
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





(* Notation "τ. P" := (Tau P) (at level 30). *)
Notation τ := Tau.
Notation "P ‖ Q" := (Para P Q) (at level 31).
Notation "P ⨁ Q" := (Sum P Q) (at level 32). (* ⨁ : \bigoplus*)
Notation "! P" := (Repl P) (at level 30).
Notation "M ⟪ N ⟫ P" := (Send M N P) (at level 30). (* ⟨ ⟩ : \lAngle \rAngle *)
Notation "M ⟦ N ⟧ P" := (Recv M N P) (at level 30). (* ⟦ ⟧ : \lBrack \rBrack *)
Notation "'IF' x == y 'THEN' P" := (Match x y P) (at level 30).
Notation " P .[ m <= n ]" := (subst P (fun x => rename x n m))(at level 30).
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

(* Definition congr (R : proc -> proc -> Prop) : Prop := *)
  (* forall P Q, R P Q -> forall C, R (insert P C) (insert Q C). *)


Reserved Notation "P ≡ Q" (at level 33).

Inductive congr : proc -> proc -> Prop :=
    | sc_match x P : IF x == x THEN P ≡ P
    | sc_sum_assoc P Q R : (P ⨁ Q) ⨁ R ≡ P ⨁ (Q ⨁ R)
    | sc_sum_comm P Q : P ⨁ Q ≡ Q ⨁ P
    | ac_sum_inact P : P ⨁ Nil ≡ P
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

  (* sc_match での場合は成り立たんけど、それを折り込むと面倒だからこれで妥協  *)
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

  Goal P ≡ P1.
  Proof.
    apply sc_nu_congr.
    eapply sc_trans.
    - apply sc_comm; apply sc_para_assoc.
    apply sc_paraL_congr.
    eapply sc_trans.
    - apply sc_paraL_congr.
      apply sc_comm.
      apply ac_sum_inact.
    eapply sc_trans.
    - apply sc_paraR_congr.
      apply sc_comm.
      apply ac_sum_inact.
    apply sc_para_comm.
  Qed.


End congr.









  


