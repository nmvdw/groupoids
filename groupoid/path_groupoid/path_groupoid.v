Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation.
From GR.bicategories.bicategory Require Import
     bicategory.
From GR.bicategories.bicategory.examples Require Import
     one_types precat.
From GR.bicategories.lax_functor Require Import
     lax_functor.
From GR.groupoid.grpd_bicategory Require Import
     grpd_bicategory.

(** Now let's discuss some examples of groupoids.
    The first example is the paths on a certain type.
 *)
Definition path_groupoid (X : 1 -Type) : groupoid
  := Build_grpd X
                (fun x y => BuildhSet (x = y))
                (fun _ => idpath)
                (fun _ _ p => p^)
                (fun _ _ _ p q => p @ q)
                (fun _ _ _ _ => concat_p_pp)
                (fun _ _ => concat_1p)
                (fun _ _ => concat_p1)
                (fun _ _ => concat_Vp)
                (fun _ _ => concat_pV).

Global Instance path_groupoid_univalent (X : 1 -Type)
  : is_univalent (path_groupoid X).
Proof.
  unfold path_groupoid, is_univalent.
  apply _.
Defined.

Section PathGroupoidFunctor.
  Context `{Univalence}.

  Definition path_groupoid_map (X Y : 1 -Type)
    : Functor (Hom one_types X Y) (Hom grpd (path_groupoid X) (path_groupoid Y)).
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _).
    - intros f ; simpl in *.
      simple refine (Build_Functor _ _ _ _ _ _) ; simpl.
      + exact f.
      + exact (fun _ _ => ap f).
      + intros ; simpl.
        apply ap_pp.
      + reflexivity.
    - simpl ; intros f g p.
      simple refine (Build_NaturalTransformation _ _ _ _) ; simpl.
      + exact (ap10 p).
      + intros x y m.
        induction m, p ; simpl.
        reflexivity.
    - simpl ; intros f g h p q.
      apply path_natural_transformation ; simpl.
      intros x.
      apply ap10_pp.
    - simpl ; intros f.
      apply path_natural_transformation ; simpl.
      intros x.
      reflexivity.
  Defined.

  Definition path_groupoid_map_compose
             {X Y Z : 1 -Type}
             (g : Y -> Z)
             (f : X -> Y)
    : NaturalTransformation
        ((path_groupoid_map Y Z) g o (path_groupoid_map X Y) f)
        ((path_groupoid_map X Z) (fun x : X => g (f x))).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _) ; cbn.
    - reflexivity.
    - intros x y p ; cbn.
      refine (concat_p1 _ @ _^ @ (concat_1p _)^).
      apply ap_compose.
  Defined.

  Definition path_groupoid_map_compose_inv
             {X Y Z : 1 -Type}
             (g : Y -> Z)
             (f : X -> Y)
    : NaturalTransformation
        ((path_groupoid_map X Z) (fun x : X => g (f x)))
        ((path_groupoid_map Y Z) g o (path_groupoid_map X Y) f).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _) ; cbn.
    - reflexivity.
    - intros x y p ; cbn.
      refine (concat_p1 _ @ _ @ (concat_1p _)^).
      apply ap_compose.
  Defined.

  Definition path_groupoid_map_id (X : 1 -Type)
    : NaturalTransformation 1%functor ((path_groupoid_map X X) idmap).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _) ; cbn.
    - reflexivity.
    - intros x y p ; cbn.
      refine (concat_p1 _ @ _^ @ (concat_1p _)^).
      apply ap_idmap.
  Defined.

  Definition path_groupoid_map_id_inv (X : 1 -Type)
    : NaturalTransformation ((path_groupoid_map X X) idmap) 1%functor.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _) ; cbn.
    - reflexivity.
    - intros x y p ; cbn.
      refine (concat_p1 _ @ _ @ (concat_1p _)^).
      apply ap_idmap.
  Defined.

  Definition path_functor_rd
    : PseudoFunctor_rd one_types grpd.
  Proof.
    simple refine (Build_PseudoFunctor_rd _ _ _ _ _ _ _).
    - exact path_groupoid.
    - exact path_groupoid_map.
    - intros X Y f g p ; cbn.
      simple refine (Build_NaturalTransformation _ _ _ _) ; simpl.
      + exact (ap10 p).
      + intros x y q ; simpl.
        induction p, q.
        reflexivity.
    - intros X Y Z.
      exact path_groupoid_map_compose.
    - exact path_groupoid_map_id.
    - intros X Y Z.
      exact path_groupoid_map_compose_inv.
    - exact path_groupoid_map_id_inv.
  Defined.

  Definition path_functor_rd_is_pseudo
    : is_pseudo_functor_d path_functor_rd.
  Proof.
    repeat split.
    - intros X Y f.
      apply path_natural_transformation.
      intro ; reflexivity.
    - intros X Y f g h p q.
      induction p, q.
      apply path_natural_transformation.
      intro ; reflexivity.
    - intros X Y Z f₁ f₂ g₁ g₂ p q.
      induction p, q.
      apply path_natural_transformation.
      intro ; reflexivity.
    - intros X Y f.
      apply path_natural_transformation.
      intro ; reflexivity.
    - intros X Y f.
      apply path_natural_transformation.
      intro ; reflexivity.
    - intros W X Y Z h g f.
      apply path_natural_transformation.
      intro ; reflexivity.
    - intros X Y Z g f.
      apply path_natural_transformation.
      intro ; reflexivity.
    - intros X Y Z g f.
      apply path_natural_transformation.
      intro ; reflexivity.
    - intros X.
      apply path_natural_transformation.
      intro ; reflexivity.
    - intros X.
      apply path_natural_transformation.
      intro ; reflexivity.
    - intros X Y Z f₁ f₂ g₁ g₂ p q.
      induction p, q.
      apply path_natural_transformation.
      intro ; reflexivity.
  Defined.

  Definition path_groupoid_functor
    : LaxFunctor one_types grpd
    := Build_PseudoFunctor path_functor_rd path_functor_rd_is_pseudo.

  Global Instance path_groupoid_pseudo
    : is_pseudo_functor path_groupoid_functor.
  Proof.
    apply _.
  Defined.
End PathGroupoidFunctor.

  

 
(*
Definition path_groupoid_map_compose `{Univalence} (X Y Z : 1 -Type)
  : NaturalTransformation
      (c_m o (path_groupoid_map Y Z, path_groupoid_map X Y))
      (path_groupoid_map X Z o c_m).
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - intros [g f] ; simpl.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros x ; simpl in *.
      reflexivity.
    + intros x y p ; simpl in *.
      induction p ; simpl.
      reflexivity.
  - intros [g₁ f₁] [g₂ f₂] [p q].
    apply path_natural_transformation ; simpl in *.
    intros x.
    induction p, q ; simpl.
    reflexivity.
Defined.

Global Instance path_groupoid_map_compose_iso `{Univalence} (X Y Z : 1 -Type)
  : @IsIsomorphism (_ -> _) _ _ (path_groupoid_map_compose X Y Z).
Proof.
  simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
  - simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [g f] ; simpl in *.
      simple refine (Build_NaturalTransformation _ _ _ _).
      * simpl ; intros x.
        reflexivity.
      * simpl ; intros x y p.
        refine (concat_p1 _ @ _ @ (concat_1p _)^).
        apply ap_compose.
    + intros [g₁ f₁] [g₂ f₂] [p₁ p₂].
      apply path_natural_transformation.
      intros x ; simpl in *.
      induction p₁, p₂ ; simpl.
      reflexivity.
  - apply path_natural_transformation.
    intros [g f].
    apply path_natural_transformation.
    intros x ; simpl in *.
    reflexivity.
  - apply path_natural_transformation.
    intros [g f].
    apply path_natural_transformation.
    intros x ; simpl in *.
    reflexivity.
Defined.

Definition path_groupoid_map_id `{Univalence} (X : 1 -Type)
  : morphism
      (Hom grpd (path_groupoid X) (path_groupoid X))
      (@id_m _ grpd (path_groupoid X))
      ((path_groupoid_map X X) (@id_m _ one_types X)).
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - intros x ; simpl in *.
    reflexivity.
  - intros x y p ; simpl in *.
    induction p ; simpl.
    reflexivity.
Defined.

Global Instance path_groupoid_map_id_iso `{Univalence} (X : 1 -Type)
  : @IsIsomorphism (_ -> _) _ _ (path_groupoid_map_id X).
Proof.
  simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
  - simple refine (Build_NaturalTransformation _ _ _ _).
    + intros x ; simpl in *.
      reflexivity.
    + intros x y p ; simpl in *.
      refine (concat_p1 _ @ _ @ (concat_1p _)^).
      apply ap_idmap.
  - apply path_natural_transformation.
    intros x ; simpl.
    reflexivity.
  - apply path_natural_transformation.
    intros x ; simpl.
    reflexivity.
Defined.
    
Definition path_groupoid_functor_d `{Univalence} : LaxFunctor_d one_types grpd.
Proof.
  simple refine {| Fobj_d := _ |}.
  - exact path_groupoid.
  - exact path_groupoid_map.
  - exact path_groupoid_map_compose.
  - exact path_groupoid_map_id.
Defined.

Definition is_lax_path_groupoid `{Univalence} : is_lax path_groupoid_functor_d.
Proof.
  repeat split.
  - intros X Y f.
    apply path_natural_transformation ; simpl in *.
    intros x ; simpl.
    reflexivity.
  - intros X Y f.
    apply path_natural_transformation ; simpl in *.
    intros x ; simpl.
    reflexivity.
  - intros W X Y Z h g f.
    apply path_natural_transformation ; simpl in *.
    intros x ; simpl.
    reflexivity.
Qed.

Definition path_groupoid_functor `{Univalence} : LaxFunctor one_types grpd
  := (path_groupoid_functor_d;is_lax_path_groupoid).

Global Instance path_groupoid_pseudo `{Univalence}
  : is_pseudo_functor path_groupoid_functor.
Proof.
  simple refine {| Fcomp_iso := _ |}.
Defined.
*)