From mathcomp Require Export ssreflect.
Require Export Nat.


Definition name := nat.

(* Matchは、[x = y]π.P となってるけど、actionを分けて定義してないからこうなってる *)
(* actionとprocを分けて定義もできるけど、再帰関数を定義する時に手間がかかるから、これで妥協 *)
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

Fixpoint isFree (P: proc) (n : name) : bool :=
  match P with
  | Nil => false
  | Tau P => isFree P n
  | Para P Q => isFree P n || isFree Q n
  | Sum P Q => isFree P n || isFree Q n
  | Repl P => isFree P n
  | Send M N P => isFree P n || (n =? M) || ( n =? N)
  | Recv M N P => (isFree P n || (n =? M)) && (negb (n =? N))
  | Nu M P => isFree P n && (negb (n =? M))
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
  | Recv M N P => N <> n /\ (isFreeP P n \/ M = n)
  | Nu M P => M <> n /\ isFreeP P n
  | Match x y P => isFreeP P n \/ x = n \/ y = n
  end.

Fixpoint isBind (P : proc) (n : name) : bool :=
  match P with
  | Nil => false
  | Tau P => isBind P n
  | Para P Q => isBind P n || isBind Q n
  | Sum P Q => isBind P n || isBind Q n
  | Repl P => isBind P n
  | Send M N P => isBind P n
  | Recv M N P => isBind P n || (n =? N)
  | Nu M P => (n =? M) || isBind P n
  | Match x y P => isBind P n
  end.

Fixpoint isBindP (P : proc) (n : name) : Prop :=
  match P with
  | Nil => False
  | Tau P => isBindP P n
  | Para P Q => isBindP P n \/ isBindP Q n
  | Sum P Q => isBindP P n \/ isBindP Q n
  | Repl P => isBindP P n
  | Send M N P => isBindP P n
  | Recv M N P => isBindP P n \/ N = n
  | Nu M P => M = n \/ isBindP P n
  | Match x y P => isBindP P n
  end.

Axiom valid_names : forall P n, isFreeP P n <-> ~ isBindP P n.

Definition rename (x n m : name) : name :=
  if x =? n then m else x.

(*
  変数捕捉はガン無視してる。
  代入が適用される式は、いい感じのα変換がなされているという前提でやる。
  もし今後、証明で不具合が生じたら、いい感じのα変換がなされている事を、明示的に仮定する。
*)

Fixpoint subst (P : proc) (n m : name) : proc :=
  match P with
  | Nil => Nil
  | Tau P => Tau (subst P n m)
  | Para P Q => Para (subst P n m) (subst Q n m)
  | Sum P Q => Sum (subst P n m) (subst Q n m)
  | Repl P => Repl (subst P n m)
  | Send M N P => Send (rename M n m) (rename N n m) (subst P n m)
  | Recv M N P => Recv (rename M n m) (rename N n m) (subst P n m)
  | Nu N P => Nu (rename N n m) (subst P n m)
  | Match x y P => Match (rename x n m) (rename y n m) (subst P n m)
  end.



Notation τ := Tau.
Notation "P ‖ Q" := (Para P Q) (at level 31).
Notation "P ⨁ Q" := (Sum P Q) (at level 32). (* ⨁ : \bigoplus*)
Notation "! P" := (Repl P) (at level 30).
Notation "M ⟪ N ⟫ P" := (Send M N P) (at level 30). (* ⟨ ⟩ : \lAngle \rAngle *)
Notation "M ⟦ N ⟧ P" := (Recv M N P) (at level 30). (* ⟦ ⟧ : \lBrack \rBrack *)
Notation "'IF' x == y 'THEN' P" := (Match x y P) (at level 30).
Notation " P .[ n ⟸ m ]" := (subst P n m)(at level 30).
Notation ν := Nu.



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
    | sc_nu_para x P Q : isFreeP P x -> ν x (P ‖ Q) ≡ P ‖ ν x Q
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