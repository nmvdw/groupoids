Require Import HoTT.
Require Import setoid polynomial.

Definition squot {A : Type} (R : setoid A)
  : Type
  := quotient (rel R).

Definition setoid_quotient_path
           {A : Type}
           (R : setoid A)
           `{Univalence}
  : forall {a₁ a₂ : A}, class_of (rel R) a₁ = class_of (rel R) a₂ <~> rel R a₁ a₂
  := sets_exact (rel R).

Section set_is_setoid_quotient.
  Variable (A : Type).
  Context `{IsHSet A}.

  Definition P : setoid A
    := {|rel := fun x y => BuildhProp(x = y) ;
         refl := fun _ => idpath ;
         sym := fun _ _ => inverse ;
         trans := fun _ _ _ => concat
       |}.
    
  Definition squot_to_A : squot P -> A
    := quotient_rec (rel P) idmap (fun _ _ => idmap).

  Global Instance squot_to_A_isequiv : IsEquiv squot_to_A.
  Proof.
    simple refine (isequiv_adjointify _ (class_of (rel P)) _ _).
    - intros x ; reflexivity.
    - unfold Sect.
      simple refine (quotient_ind _ _ _ _).
      + reflexivity.
      + intros.
        apply path_ishprop.
  Defined.
End set_is_setoid_quotient.

Section path_setoid_quotient.
  Variable (A : Type).
    
  Definition squot_to_TA : squot (path_setoid A) -> Trunc 0 A.
  Proof.
    simple refine (quotient_rec _ tr _).
    cbn ; intros x y H.
    simple refine (Trunc_rec _ H).
    exact (ap tr).
  Defined.

  Global Instance squot_to_TA_isequiv : IsEquiv squot_to_TA.
  Proof.
    simple refine (isequiv_adjointify _ _ _ _).
    - intros x.
      simple refine (Trunc_rec _ x).
      apply class_of.
    - unfold Sect.
      simple refine (Trunc_ind _ _) ; reflexivity.
    - unfold Sect.
      simple refine (quotient_ind _ _ _ _).
      + reflexivity.
      + intros.
        apply path_ishprop.
  Defined.
End path_setoid_quotient.

Section squot_sum.
  Variable (A B : Type)
           (R₁ : setoid A) (R₂ : setoid B).

  Definition squot_sum_in
             (z : squot R₁ + squot R₂)
    : squot (sum_setoid R₁ R₂).
  Proof.
    destruct z as [z | z].
    - simple refine (quotient_rec _ _ _ z).
      + exact (fun a => class_of _ (inl a)).
      + intros a₁ a₂ p ; cbn in *.
        apply related_classes_eq ; assumption.
    - simple refine (quotient_rec _ _ _ z).
      + exact (fun a => class_of _ (inr a)).
      + intros b₁ b₂ p ; cbn in *.
        apply related_classes_eq ; assumption.
  Defined.

  Definition squot_sum_out
    : squot (sum_setoid R₁ R₂) -> squot R₁ + squot R₂.
  Proof.
    simple refine (quotient_rec _ _ _).
    - intros [z | z].
      + exact (inl(class_of _ z)).
      + exact (inr(class_of _ z)).
    - intros [x | x] [y | y] r ; try contradiction
      ; apply ap ; apply related_classes_eq ; assumption.
  Defined.

  Lemma squot_sum_out_in_sect : Sect squot_sum_out squot_sum_in.
  Proof.
    unfold Sect.
    simple refine (quotient_ind _ _ _ _).
    - intros [z | z] ; reflexivity.
    - intros ; apply path_ishprop.
  Defined.

  Lemma squot_sum_in_out_sect : Sect squot_sum_in squot_sum_out.
  Proof.
    intros [x | x] ; revert x.
    - simple refine (quotient_ind _ _ _ _).
      + intros ; reflexivity.
      + intros ; apply path_ishprop.
    - simple refine (quotient_ind _ _ _ _).
      + intros ; reflexivity.
      + intros ; apply path_ishprop.
  Defined.

  Global Instance squot_sum_out_isequiv : IsEquiv squot_sum_out
    := isequiv_adjointify _ squot_sum_in squot_sum_in_out_sect squot_sum_out_in_sect.
End squot_sum.

Section squot_prod.
  Variable (A B : Type)
           (R₁ : setoid A) (R₂ : setoid B).
  Context `{Funext}.

  Definition squot_prod_in
             (z : squot R₁ * squot R₂)
    : squot (prod_setoid R₁ R₂).
  Proof.
    destruct z as [z₁ z₂]. revert z₁ z₂.
    simple refine (quotient_rec _ _ _).
    - intros a.
      simple refine (quotient_rec _ _ _).
      + intros b.
        exact (class_of _ (a,b)).
      + simpl ; intros b₁ b₂ p.
        apply related_classes_eq.
        exact (refl _,p).
    - simpl ; intros a₁ a₂ p₁.
      funext b. revert b.
      simple refine (quotient_ind _ _ _ _).
      + intros b ; simpl.
        apply related_classes_eq.
        exact (p₁,refl _).
      + intros ; apply path_ishprop.
  Defined.

  Definition squot_prod_out
    : squot (prod_setoid R₁ R₂) -> squot R₁ * squot R₂.
  Proof.
    simple refine (quotient_rec _ _ _).
    - exact (fun z => (class_of _ (fst z),class_of _ (snd z))).
    - simpl ; intros z₁ z₂ p.
      apply path_prod' ; apply related_classes_eq ; apply p.
  Defined.

  Lemma squot_prod_out_in_sect : Sect squot_prod_out squot_prod_in.
  Proof.
    unfold Sect.
    simple refine (quotient_ind _ _ _ _).
    - simpl ; intros [z₁ z₂] ; reflexivity.
    - intros ; apply path_ishprop.
  Defined.

  Lemma squot_prod_in_out_sect : Sect squot_prod_in squot_prod_out.
  Proof.
    intros [z₁ z₂]. revert z₁ z₂.
    simple refine (quotient_ind _ _ _ _).
    - simpl ; intros a.
      simple refine (quotient_ind _ _ _ _).
      + simpl ; intros b.
        reflexivity.
      + intros ; apply path_ishprop.
    - intros ; apply path_ishprop.
  Defined.

  Global Instance squot_prod_out_isequiv : IsEquiv squot_prod_out
    := isequiv_adjointify _ squot_prod_in squot_prod_in_out_sect squot_prod_out_in_sect.
End squot_prod.

Definition Trunc_prod
           {A B : Type}
           (n : trunc_index)
  : Trunc n A * Trunc n B -> Trunc n (A * B).
Proof.
  intros x.
  simple refine (Trunc_rec _ (fst x)) ; intros y₁.
  simple refine (Trunc_rec _ (snd x)) ; intros y₂.
  exact (tr(y₁,y₂)).
Defined.

Definition Trunc_prod_inv
           {A B : Type}
           (n : trunc_index)
  : Trunc n (A * B) -> Trunc n A * Trunc n B.
Proof.
  apply Trunc_rec.
  exact (fun x => (tr (fst x), tr (snd x))).
Defined.

Global Instance Trunc_prod_isequiv
       {A B : Type}
       (n : trunc_index)
  : IsEquiv (@Trunc_prod A B n).
Proof.
  simple refine (isequiv_adjointify _ (Trunc_prod_inv n) _ _) ; unfold Sect.
  - simple refine (Trunc_ind _ _).
    reflexivity.
  - intros [x₁ x₂]. revert x₁.
    simple refine (Trunc_ind _ _) ; intros y₁ ; simpl.
    revert x₂.
    simple refine (Trunc_ind _ _) ; intros y₂ ; simpl.
    reflexivity.
Defined.

Global Instance Truncated_sum
       {A B : Type}
       (n : trunc_index)
       (H : trunc_index_leq 0 n)
       `{IsTrunc n A} `{IsTrunc n B}
  : IsTrunc n (A + B).
Proof.
  apply trunc_sum' ; try apply _.
  exact (trunc_leq H).
Defined.

Definition Trunc_sum
           {A B : Type}
           (n : trunc_index)
  : Trunc n A + Trunc n B -> Trunc n (A + B).
Proof.
  intros [x | x].
  - simple refine (Trunc_rec _ x) ; intros y.
    exact (tr(inl y)).
  - simple refine (Trunc_rec _ x) ; intros y.
    exact (tr(inr y)).
Defined.

Definition Trunc_sum_inv
           {A B : Type}
           (n : trunc_index)
           (H : trunc_index_leq 0 n)
  : Trunc n (A + B) -> Trunc n A + Trunc n B.
Proof.
  simple refine (Trunc_rec _).
  - apply (Truncated_sum n H).
  - intros [x | x].
    + exact (inl (tr x)).
    + exact (inr (tr x)).
Defined.

Global Instance Trunc_sum_isequiv
       {A B : Type}
       (n : trunc_index)
       (H : trunc_index_leq 0 n)
  : IsEquiv (@Trunc_sum A B n).
Proof.
  simple refine (isequiv_adjointify _ (Trunc_sum_inv n H) _ _) ; unfold Sect.
  - simple refine (Trunc_ind _ _).
    intros [a | a] ; reflexivity.
  - intros [x | x] ; revert x ; simple refine (Trunc_ind _ _).
    * intros a.
      pose (@Truncated_sum (Trunc n A) (Trunc n B) n H).
      apply _.
    * reflexivity.
    * intros a.
      pose (@Truncated_sum (Trunc n A) (Trunc n B) n H).
      apply _.
    * reflexivity.
Defined.

Definition pair_maps
           {A B C D : Type}
           (f : A -> C) (g : B -> D)
  : A * B -> C * D
  := fun z => (f (fst z), g (snd z)).

Global Instance equiv_pair
       {A B C D : Type}
       (f : A -> C) (g : B -> D)
       `{IsEquiv _ _ f} `{IsEquiv _ _ g}
  : IsEquiv (pair_maps f g).
Proof.
  apply _.
Defined.

Definition sum_maps
           {A B C D : Type}
           (f : A -> C) (g : B -> D)
  : A + B -> C + D
  := fun z =>
       match z with
       | inl a => inl (f a)
       | inr b => inr (g b)
       end.

Global Instance equiv_sum
       {A B C D : Type}
       (f : A -> C) (g : B -> D)
       `{IsEquiv _ _ f} `{IsEquiv _ _ g}
  : IsEquiv (sum_maps f g).
Proof.
  apply _.
Defined.

Definition poly_squot_to_squot
           (P : polynomial)
           {A : Type}
           (R : setoid A)
  : squot (lift_groupoid R P) -> Trunc 0 (poly_act P (squot R)).
Proof.
  induction P as [ | | P IHP Q IHQ | P IHP Q IHQ] ; cbn.
  - exact tr.
  - exact (squot_to_TA T).
  - exact ((Trunc_prod 0)
             o (pair_maps IHP IHQ)
             o squot_prod_out _ _ _ _).
  - exact ((Trunc_sum 0)
              o (sum_maps IHP IHQ)
              o squot_sum_out _ _ _ _).
Defined.

Global Instance squot_polynomial
       (Q : polynomial)
       {A : Type} `{IsHSet A}
       (R : setoid A)
       `{Funext}
  : IsEquiv (poly_squot_to_squot Q R).    
Proof.
  induction Q.
  - apply _.
  - apply _.
  - apply _.
  - simpl.
    refine isequiv_compose.
    apply Trunc_sum_isequiv.
    exact tt.
Defined.