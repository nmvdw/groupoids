Require Import HoTT.
From HoTT.Categories Require Import
     Functor NaturalTransformation.
From GR.bicategories.bicategory Require Import
     examples.one_types.
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

Definition path_groupoid_functor `{Univalence} : LaxFunctor one_types grpd.
Proof.
  simple refine {| Fobj := _ |}.
  - exact path_groupoid.
  - intros X Y.
    simple refine (Build_Functor _ _ _ _ _ _).
    + intros f.
      simple refine (Build_Functor _ _ _ _ _ _).
      * exact f.
      * intros x y p ; simpl.
        exact (ap f p).
      * intros x y z p q ; simpl.
        apply ap_pp.
      * reflexivity.
    + intros f g p ; simpl in *.
      simple refine (Build_NaturalTransformation _ _ _ _).
      * intros x ; cbn in *.
        exact (ap10 p x).
      * intros x y q ; simpl in *.
        induction p, q ; cbn.
        reflexivity.
    + intros f g h p q ; simpl in *.
      apply path_natural_transformation ; simpl.
      intros x.
      induction p, q ; simpl.
      reflexivity.
    + intros f ; simpl.
      apply path_natural_transformation ; simpl.
      intros x.
      reflexivity.
  - intros X Y Z ; simpl in *.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [g f] ; simpl.
      simple refine (Build_NaturalTransformation _ _ _ _).
      * intros x ; simpl in *.
        reflexivity.
      * intros x y p ; simpl in *.
        induction p ; simpl.
        reflexivity.
    + intros [g₁ f₁] [g₂ f₂] [p q].
      apply path_natural_transformation ; simpl in *.
      intros x.
      induction p, q ; simpl.
      reflexivity.
  - intros X ; simpl.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros x ; simpl in *.
      reflexivity.
    + intros x y p ; simpl in *.
      induction p ; simpl.
      reflexivity.
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
Defined.