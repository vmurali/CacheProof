Require Import State.

(*
Module Type DataTypes.
  Parameter classical: forall P, P \/ ~ P.

  Parameter Addr: Set.
  Inductive Desc := Ld | St.

  Definition Index := nat.

  Parameter Cache: Set.
  Parameter parent: Cache -> Cache -> Prop.
  Parameter leaf: Cache -> Prop.
  Parameter descendent: Cache -> Cache -> Prop.

  Inductive State := In | Sh | Mo.

  Definition slt x y := match x with
                          | In => match y with
                                    | In => False
                                    | Sh => True
                                    | Mo => True
                                  end
                          | Sh => match y with
                                    | In => False
                                    | Sh => False
                                    | Mo => True
                                  end
                          | Mo => False
                        end.
  Definition sgt x y := slt y x.
  Definition sle x y := match x with
                          | In => match y with
                                    | In => True
                                    | Sh => True
                                    | Mo => True
                                  end
                          | Sh => match y with
                                    | In => False
                                    | Sh => True
                                    | Mo => True
                                  end
                          | Mo => match y with
                                    | In => False
                                    | Sh => False
                                    | Mo => True
                                  end
                        end.

  Theorem sle_eq: forall {x y}, x = y -> sle x y.
  Proof.
    intros x y x_eq_y. rewrite x_eq_y.
    unfold sle.
    destruct y; auto.
  Qed.

  Theorem slt_neq: forall {x y}, x = y -> ~ slt x y.
  Proof.
    intros x y x_eq_y. rewrite x_eq_y. intros geez.
    unfold slt in geez.
    destruct y; auto.
  Qed.

  Theorem slt_neq': forall {x y}, slt x y -> x <> y.
  Proof.
    unfold slt; destruct x; destruct y; auto; discriminate.
  Qed.

  Theorem slt_slti_false: forall {x y}, slt x y -> slt y x -> False.
  Proof.
    intros x y slt1 slt2.
    unfold slt in *; destruct x in *; destruct y in *; auto.
  Qed.

  Theorem slt_slei_false: forall {x y}, slt x y -> sle y x -> False.
  Proof.
    intros x y s1 s2.
    unfold slt in *; unfold sle in *; destruct x in *; destruct y in *; auto.
  Qed.

  Theorem not_slt_sle: forall {x y}, ~ slt x y -> sle y x.
  Proof.
    intros x y noSlt.
    unfold sle; unfold slt in *;
    destruct x; destruct y; auto.
  Qed.

  Theorem slt_eq_slt_dec: forall {x y}, slt x y \/ x = y \/ slt y x.
  Proof.
    intros x y.
    destruct x; destruct y; unfold slt; auto.
  Qed.

  Theorem slt_eq_sle: forall {x y}, sle x y = slt x y \/ x = y.
  Proof.
    intros x y.
    unfold sle; unfold slt.
    destruct x; destruct y; auto.
  Qed.
    

  Definition Time := nat.
  Parameter state: Cache -> Addr -> Time -> State.
  Parameter dir: Cache -> Cache -> Addr -> Time -> State.

  Parameter Mesg: Set.
  Parameter from: Mesg -> State.
  Parameter to: Mesg -> State.
  Parameter addr: Mesg -> Addr.

  Parameter ChannelType: Set.

  Parameter mch rch: ChannelType.

  Parameter Label : Set.
  Inductive StLabel := Initial | Store : Label -> StLabel.
  Parameter data: Cache -> Addr -> Time -> StLabel.
  Parameter dataM: Mesg -> StLabel.

End DataTypes.
*)

Module Type DataTypes.
  Include MsiState.
  
  Parameter classical: forall P, P \/ ~ P.

  Parameter Addr: Set.
  Inductive Desc := Ld | St.

  Definition Index := nat.

  Inductive Cache': Set :=
    | Parent : Cache'
    | Child : nat -> Cache'.

  Definition Cache := Cache'. 

  Definition parent c p := 
    match c with
      | Parent => False
      | Child _ => 
        match p with
          | Parent => True
          | Child _ => False
        end
    end.

  Definition leaf x := match x with
                         | Parent => False
                         | Child _ => True
                       end.

  Theorem noChildIsParent: forall {c}, leaf c -> forall c', ~ parent c' c.
  Proof.
    intros c leafC.
    unfold leaf in leafC.
    destruct c.
    firstorder.
    unfold not; intros c' parentc'.
    unfold parent in parentc'.
    destruct c'; assumption.
  Qed.

  Theorem noParentHasParent: forall c, ~ parent Parent c.
  Proof.
    unfold not; intros c parentc.
    unfold parent in parentc.
    assumption.
  Qed.
    
  Theorem whoParent: forall n, parent (Child n) Parent.
  Proof.
    intros.
    unfold parent.
    auto.
  Qed.

  Theorem who'Parent: forall c, leaf c -> parent c Parent.
  Proof.
    intros c leaf_c.
    destruct c; unfold leaf; auto.
  Qed.

  Parameter descendent: Cache -> Cache -> Prop.

  Definition Time := nat.
  Parameter state: Cache -> Addr -> Time -> State.
  Parameter dir: Cache -> Cache -> Addr -> Time -> State.

  Parameter Mesg: Set.
  Parameter from: Mesg -> State.
  Parameter to: Mesg -> State.
  Parameter addr: Mesg -> Addr.

  Parameter ChannelType: Set.

  Parameter mch rch: ChannelType.

  Parameter Label : Set.
  Inductive StLabel := Initial | Store : Label -> StLabel.
  Parameter data: Cache -> Addr -> Time -> StLabel.
  Parameter dataM: Mesg -> StLabel.

End DataTypes.



