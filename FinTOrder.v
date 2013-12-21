Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersTac.

Module FinTOrder <: EqLtLe.
  Inductive FTO := In | Sh | Ow | Mo.
  Definition t := FTO.
  Definition lt x y := match x with
                         | In => match y with
                                   | In => False
                                   | Sh => True
                                   | Ow => True
                                   | Mo => True
                                 end
                         | Sh => match y with
                                   | In => False
                                   | Sh => False
                                   | Ow => True
                                   | Mo => True
                                 end
                         | Ow => match y with
                                   | In => False
                                   | Sh => False
                                   | Ow => False
                                   | Mo => True
                                 end
                         | Mo => False
                       end.
  Definition eq (x y: FTO) := x = y.
  Definition le x y := lt x y \/ eq x y.
End FinTOrder.

Module Type FTOrder := IsTotalOrder FinTOrder.
Module Type FTNot := FTOrder <+ (EqLtLeNotation FinTOrder).

Module FinTOrderIsTOrder : FTNot.
  Import FinTOrder.
  Theorem eq_ref : Reflexive eq.
  Proof.
    unfold Reflexive; unfold eq.
    auto.
  Qed.

  Theorem eq_symm: Symmetric eq.
  Proof.
    unfold Symmetric; unfold eq.
    auto.
  Qed.

  Theorem eq_trans: Transitive eq.
  Proof.
    unfold Transitive; unfold eq.
    intros.
    rewrite <- H in H0.
    assumption.
  Qed.

  Definition eq_equiv := Build_Equivalence t eq eq_ref eq_symm eq_trans.

  Theorem lt_irr: Irreflexive lt.
  Proof.
    unfold Irreflexive; unfold lt.
    unfold Reflexive; unfold complement.
    intros.
    destruct x; assumption.
  Qed.

  Theorem lt_trans: Transitive lt.
  Proof.
    unfold Transitive; unfold lt.
    intros.
    destruct x;
    destruct y; destruct z; assumption.
  Qed.

  Definition lt_strorder := Build_StrictOrder t lt lt_irr lt_trans.

  Theorem prop: Proper (eq ==> eq ==> iff) lt.
  Proof.
    unfold iff.
    unfold Proper.
    unfold respectful.
    intros.
    unfold eq in *.
    rewrite H in *.
    rewrite H0 in *.
    firstorder.
  Qed.
  Definition lt_compat := prop.

  Theorem sth1: forall x y, le x y <-> lt x y \/ eq x y.
  Proof.
    unfold le.
    intros.
    constructor; auto.
  Qed.

  Theorem sth2: forall x y, lt x y \/ eq x y \/ lt y x.
  Proof.
    intros.
    destruct x; destruct y; unfold eq; unfold lt; auto.
  Qed.
  Print IsTotalOrder.

  Definition le_lteq := sth1.
  Definition lt_total := sth2.
End FinTOrderIsTOrder.
