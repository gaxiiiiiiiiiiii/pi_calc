From mathcomp Require Import ssreflect.
Require Import Nat.


Definition name := nat.

Inductive action :=
  | Send (x y : name)
  | Recv (x y : name)
  | Tau
  | Match (x y : name) (pi : action).

Inductive proc :=
  | Sums (M : sums)
  | Para (P Q : proc)
  | Nu (z : name) (P : proc)
  | Repl (P : proc)

with sums :=
  | Nil
  | Prefix (pi : action) (P : proc)
  | Sum (M N : sums).

Scheme proc_mutual_ind := Induction for proc Sort Prop
with sums_mutual_ind := Induction for sums Sort Prop.

Notation "x <| y |>" := (Send x y) (at level 10).
Notation "x [| y |]" := (Recv x y) (at level 10).
Notation "'IF' x =?= y 'THEN' π" := (Match x y π) (at level 10).
Notation τ := Tau.
Notation "P ‖ Q" := (Para P Q) (at level 60).
(* Notation "ν. x ⇒ P" := (Nu x P) (at level 60). *)
Notation ν := Nu.
Notation "! P" := (Repl P) (at level 60).
Notation "P ⊕ Q" := ((Sum P Q)) (at level 60).
Notation "π ⋅ P" := ((Prefix π P)) (at level 50).
Notation "∅" := (Sums Nil).


Fixpoint isFreeA (pi : action) (n : name) : Prop :=
  match pi with
  | Send x y => x = n \/ y = n
  | Recv x y => x = n 
  | Tau => False
  | Match x y pi' => x = n \/ y = n \/ isFreeA pi' n
  end.

Fixpoint isFreeP (P : proc) (n : name) : Prop :=
  match P with
  | Sums M => isFreeS M n
  | Para P Q => isFreeP P n \/ isFreeP Q n
  | Nu z P => n <> z /\ isFreeP P n
  | Repl P => isFreeP P n
  end

with isFreeS (M : sums) (n : name) : Prop :=
  match M with
  | Nil => False
  | Prefix pi P => isFreeA pi n \/ isFreeP P n   
  | Sum M N => isFreeS M n \/ isFreeS N n
  end.

Fixpoint isBoundA (pi : action) (n : name) : Prop :=
  match pi with
  | Recv x y => y = n
  | Match x y pi' => isBoundA pi' n
  | _ => False
  end.

Fixpoint isBoundP (P : proc) (n : name) : Prop :=
  match P with
  | Sums M => isBoundS M n
  | Para P Q => isBoundP P n /\ isBoundP Q n
  | Nu z P => z = n \/ isBoundP P n
  | Repl P => isBoundP P n
  end

with isBoundS (M : sums) (n : name) : Prop :=
  match M with
  | Nil => False
  | Prefix pi P => isBoundA pi n \/ isBoundP P n   
  | Sum M N => isBoundS M n \/ isBoundS N n
  end.

Module FreeBindTest.
  Notation x := 0.
  Notation y := 1.
  Notation z := 2.
  Notation v := 3.
  Notation w := 4.
  Notation u := 5.

  Definition A := Sums (z <|y|> ⋅ ∅ ⊕ w <|v|> ⋅ ∅) ‖ Sums (x <|u|> ⋅ ∅).
  Eval simpl in (isFreeP A 10).
  
  Definition B := ((x [| z |] ⋅ Sums (z<|y|> ⋅ ∅)) ⊕ (w <|v|> ⋅ ∅)).
  Definition C := ν u (Sums (x <|u|> ⋅ ∅)).
  Definition D := ν x (Sums B ‖ C).
  (* Variable a : name. *)
  (* Eval simpl in (isBoundP D a). *)

End FreeBindTest.



Definition subst := name -> name.
Definition isSupp (σ : subst) (x : name) := σ x <> x.
Definition isCosupp (σ : subst) (y : name) := exists x, σ x = y /\ isSupp σ x.
Definition namesOf (σ : subst) (y : name) := isSupp σ y \/ isCosupp σ y.

Definition rename (x n m : name) : name :=
  if x =? n then m else x.

Fixpoint renameA (pi : action) (n m : name) : action :=
  match pi with
  | Send x y => Send (rename x n m) (rename y n m)
  | Recv x y => Recv (rename x n m) y
  | Tau => Tau
  | Match x y pi' => Match (rename x n m) (rename y n m) (renameA pi' n m)
  end.

Fixpoint renameP (P : proc) (n m : name) : proc :=
  match P with
  | Sums M => Sums (renameS M n m)
  | Para P Q => Para (renameP P n m) (renameP Q n m)
  | Nu z P => Nu z (renameP P n m)
  | Repl P => Repl (renameP P n m)
  end

with renameS (M : sums) (n m : name) : sums :=
  match M with
  | Nil => Nil
  | Prefix pi P => Prefix (renameA pi n m) (renameP P n m)    
  | Sum M N => Sum (renameS M n m) (renameS N n m)
  end.


Fixpoint maxA (pi : action) (n : name) : name :=
  match pi with
  | Send x y => max n (max x y)
  | Recv x y => max n (max x y)
  | Tau => n
  | Match x y pi' => max ((maxA pi' n)) ((max x y)) 
  end.

Fixpoint maxP (P : proc) (n : name) : name :=
  match P with
  | Sums M => maxS M n
  | Para P Q => max (maxP P n) (maxP Q n)
  | Nu z P => maxP P n
  | Repl P => maxP P n
  end

with maxS (M : sums) (n : name) : name :=
  match M with
  | Nil => n
  | Prefix pi P => max (maxA pi n) (maxP P n)   
  | Sum M N => max (maxS M n) (maxS N n)
  end.


Fixpoint alphaA (pi : action) (n m : name) : action :=
  match pi with
  | Send x y => pi
  | Recv x y => Recv y (rename y n m)
  | Tau => Tau
  | Match x y pi' => Match x y (alphaA pi' n m)
  end.

Fixpoint alphaP (P : proc) (n m : name) : proc :=
  match P with
  | Sums M => Sums (alphaS M n m)
  | Para P Q => Para (alphaP P n m) (alphaP Q n m)
  | Nu z P => 
    if z =? n then Nu m (renameP P n m)
    else Nu z (alphaP P n m)
    (* Nu (rename z n m) (renameP P n m) *)
  | Repl P => Repl (alphaP P n m)
  end

with alphaS (M : sums) (n m : name) : sums :=
  match M with
  | Nil => Nil
  | Prefix pi P => 
    match pi with
    | Recv _ _ => Prefix (alphaA pi n m) (renameP P n m)
    | _ => Prefix (alphaA pi n m) (alphaP P n m)
    end
  | Sum M N => Sum (alphaS M n m) (alphaS N n m)
  end.

Definition alpha_comverted (P : proc) (σ : subst) : Prop :=
  forall x, isBoundP P x -> (~ isFreeP P x) /\ (~ namesOf σ x).


Fixpoint substA (pi : action) (σ : subst) : action :=
  match pi with
  | Send x y => Send (σ x) (σ y)
  | Recv x y => Recv (σ x) (σ y)
  | Tau => Tau
  | Match x y pi' => Match (σ x) (σ y) (substA pi' σ)
  end.

Fixpoint substP (P : proc) (σ : subst) : proc :=
  match P with
  | Sums M => Sums (substS M σ)
  | Para P Q => Para (substP P σ) (substP Q σ)
  | Nu z P => Nu (σ z) (substP P σ)
  | Repl P => Repl (substP P σ)
  end

with substS (M : sums) (σ : subst) : sums :=
  match M with
  | Nil => Nil
  | Prefix pi P => Prefix (substA pi σ) (substP P σ)   
  | Sum M N => Sum (substS M σ) (substS N σ)
  end.







